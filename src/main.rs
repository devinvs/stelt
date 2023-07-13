use std::fs::File;
use std::io::Read;

use stelt::Lexer;
use stelt::MIRTree;
use stelt::Program;
use stelt::TypeChecker;

use stelt::Module;

use std::collections::{HashMap, VecDeque};
use std::path::Path;

fn main() {
    compile(Path::new("./main.st"));
}

fn parse(path: &Path) -> Program {
    eprintln!("parse {path:?}");
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

fn compile(path: &Path) {
    // Base directory of file path
    let parent = path.parent().unwrap();
    let mod_name = path.file_stem().unwrap().to_str().unwrap().to_string();

    // map of module names to their parse trees
    let mut modules = HashMap::new();

    // queue of modules to be parsed
    let mut mod_queue = VecDeque::new();
    mod_queue.push_back(mod_name);

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
        let tree = tree.resolve(&modules);
        modules_mir.insert(name, MIRTree::from(tree));
    }

    // Now compile :)
    for (name, mut mir) in modules_mir.into_iter() {
        let mut checker = TypeChecker::default();
        eprintln!("check {name}");
        match checker.check_program(&mut mir) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }

        eprintln!("with concrete types {name}");
        let mir = mir.with_concrete_types();

        eprintln!("lir {name}");
        let lir = mir.lower();
        //eprintln!("{:#?}", lir.funcs);

        let out_path = parent.join(Path::new(&format!("{}.ll", name)));

        let out = File::create(out_path).unwrap();
        let mut module = Module::new(Box::new(out));
        module.compile(lir).unwrap();
    }
}
