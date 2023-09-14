use std::fs::File;
use std::io::Read;

use stelt::Lexer;
use stelt::MIRTree;
use stelt::Program;
use stelt::TypeChecker;

use stelt::Module;

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
    let mut modules = HashMap::new();

    // queue of modules to be parsed
    let mut mod_queue = VecDeque::new();
    mod_queue.push_back(mod_name.clone());

    // Parse each file using a breadth first search technique, using imported
    // namespace names to locate the source file corresponding to the namespace
    while !mod_queue.is_empty() {
        let name = mod_queue.pop_front().unwrap();
        let path = parent.join(Path::new(&format!("{}.st", name.replace(".", "/"))));
        let tree = parse(&path);

        // queue up other modules to be compiled
        for ns in tree.namespaces.iter() {
            if !modules.contains_key(ns) {
                mod_queue.push_back(ns.to_string());
            }
        }

        modules.insert(name, tree);
    }

    // Resolve namespace references and convert to mir
    let mut modules_mir = HashMap::new();
    for (name, tree) in modules.iter() {
        let tree = tree.clone();
        let tree = tree.resolve(&modules, if *name == mod_name { "" } else { name });

        modules_mir.insert(name, MIRTree::from(tree));
    }

    // Now compile :)
    for (name, mut mir) in modules_mir.into_iter() {
        eprintln!("{}", mir.funcs["main"].to_sexpr().to_string());
        let mut checker = TypeChecker::default();
        match checker.check_program(&mut mir) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }

        let mir = mir.with_concrete_types();
        let lir = mir.lower();

        let out_path = outdir.join(Path::new(&format!("{}.ll", name)));

        let out = File::create(out_path).unwrap();
        let mut module = Module::new(Box::new(out));

        module.compile(lir).unwrap();
    }
}
