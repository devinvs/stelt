use std::fs::File;
use std::io::Read;

use stelt::gen_impl_map;
use stelt::Lexer;
use stelt::MIRTree;
use stelt::Module;
use stelt::Program;
use stelt::TypeChecker;

use std::collections::{HashMap, VecDeque};
use std::path::Path;

fn print_usage() {
    eprintln!("Usage: steltc [FILE]");
    eprintln!("Usage: steltc [FILE] [OUT_DIR]");
    std::process::exit(1);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        print_usage();
    }

    let path = Path::new(&args[1]);
    let outdir = Path::new(args.get(2).map(|s| s.as_str()).unwrap_or("./"));

    compile(path, outdir);
}

fn parse(path: &Path) -> Program {
    let mut file = File::open(path).unwrap();
    let mut buf = String::with_capacity(file.metadata().unwrap().len() as usize);
    file.read_to_string(&mut buf).unwrap();

    // Lex
    let mut lexer = Lexer::default();
    let mut tokens = match lexer.lex(&buf) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    };

    // Parse
    let program = match Program::parse(&mut tokens) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    };

    program
}

fn compile(path: &Path, outdir: &Path) {
    // Base directory of file path
    let parent = path.parent().unwrap();
    let mod_name = path.file_stem().unwrap().to_str().unwrap().to_string();

    // map of module names to their parse trees
    let mut trees = HashMap::new();

    // map of module name to module interface
    let mut modules = HashMap::new();

    // queue of modules to be parsed
    let mut mod_queue = VecDeque::new();
    mod_queue.push_back(mod_name.clone());

    // also build the order that we resolve, should
    // be the opposite of parsing
    let mut resolve_queue = VecDeque::new();

    // Parse each file using a breadth first search technique, using imported
    // namespace names to locate the source file corresponding to the namespace
    while !mod_queue.is_empty() {
        let name = mod_queue.pop_front().unwrap();
        resolve_queue.push_front(name.clone());

        let path = parent.join(Path::new(&format!("{}.st", name.replace(".", "/"))));
        let mut tree = parse(&path);

        // queue up other modules to be compiled
        for ns in tree.imports.iter() {
            if !trees.contains_key(ns) && !mod_queue.contains(ns) {
                mod_queue.push_back(ns.to_string());
            }
        }

        modules.insert(name.clone(), tree.canonicalize(&name));
        trees.insert(name, tree);
    }

    // Actually Handle imports
    while let Some(name) = resolve_queue.pop_front() {
        // Find the tree, resolve it, add to resolved
        let tree = trees.get_mut(&name).unwrap();
        tree.resolve(&name, &modules);
    }

    // Aggregate the impls
    let impl_map = gen_impl_map(&modules, &trees);

    // Resolve namespace references and convert to mir
    let mut modules_mir = HashMap::new();
    for (name, tree) in trees {
        let tree = MIRTree::from(tree);
        modules_mir.insert(name, tree);
    }

    // Now compile :)
    for (name, mut mir) in modules_mir.into_iter() {
        let mut checker = TypeChecker::default();
        match checker.check_program(&mut mir, &impl_map) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }

        let mir = mir.with_concrete_types(&impl_map, &modules);
        let lir = mir.lower(&impl_map);

        let out_path = outdir.join(Path::new(&format!("{}.ll", name)));

        let out = File::create(out_path).unwrap();
        let mut module = Module::new(Box::new(out));

        let main = lir
            .funcs
            .keys()
            .find(|s| s.ends_with(".main"))
            .map(|s| s.clone());

        module.compile(lir, main).unwrap();
    }
}
