use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;

use crate::llvm::LLVMType;

use crate::mir::resolve_typefn;
use crate::mir::MIRExpression;
use crate::mir::MIRTree;
use crate::parse_tree::DataDecl;
use crate::parse_tree::Pattern;
use crate::parse_tree::Type;
use crate::parse_tree::Vis;

macro_rules! eq_type {
    ($i:expr) => {
        Type::Arrow(
            Box::new(Type::Tuple(vec![$i.clone(), $i.clone()])),
            Box::new(Type::Bool),
        )
    };
}

#[derive(Debug)]
pub struct LIRTree {
    /// Set of external function names
    pub external: HashSet<String>,

    /// Named Types
    pub enums: HashMap<String, LLVMType>,

    /// Enum Variants
    pub variants: HashMap<String, Vec<(String, LLVMType)>>,

    /// Map of function names to their llvm types
    pub func_types: HashMap<String, (Vis, LLVMType, LLVMType)>,

    pub extern_types: HashMap<String, (Vec<LLVMType>, LLVMType)>,

    /// Map of function names to their expressions
    pub funcs: HashMap<String, LIRExpression>,

    pub type_sizes: HashMap<String, usize>,
}

impl MIRTree {
    pub fn lower(self, impl_map: &HashMap<String, Vec<(String, Type)>>) -> LIRTree {
        // get list of global names
        let mut globals = HashSet::new();
        globals.insert("arg.0".to_string());

        let mut func_types = HashMap::new();
        let mut funcs = HashMap::new();

        // convert all types into their llvm forms
        let mut variants = HashMap::new();
        let mut enums = HashMap::new();

        for (name, (_, t)) in self.types {
            match t {
                DataDecl(_, _, cons) => {
                    let vars = LLVMType::from_enum(cons);
                    variants.insert(name, vars);
                }
            }
        }

        // for each type enum get the max size of its variants,
        // add padding of bytes to the base type
        // needs to be breath first cause dependencies
        let mut queue = VecDeque::new();
        queue.extend(variants.iter());

        let mut type_sizes = HashMap::new();
        'outer: while let Some((name, vars)) = queue.pop_front() {
            let mut size = 0;

            for (_, var) in vars {
                let s = var.size(1, &type_sizes);

                if s.is_none() {
                    queue.push_back((name, vars));
                    continue 'outer;
                }

                size = size.max(s.unwrap());
            }

            // align to the byte boundary
            size += size % 8;

            let enm = if size == 8 {
                LLVMType::Struct(vec![LLVMType::I8])
            } else {
                LLVMType::Struct(vec![
                    LLVMType::I8,
                    LLVMType::Array(Box::new(LLVMType::I8), (size / 8) - 1),
                ])
            };

            enums.insert(name.clone(), enm);

            type_sizes.insert(name.clone(), size);
        }

        // get list of global function and constructor names
        let mut global_funcs = HashSet::new();
        for (f, _) in self.typedecls.iter() {
            global_funcs.insert(f.clone());
        }
        for n in self.external.iter() {
            global_funcs.insert(n.clone());
        }
        for vars in variants.values() {
            for (e, _) in vars {
                global_funcs.insert(e.clone());
            }
        }

        let mut externs = HashSet::new();
        externs.extend(self.external.iter().map(|s| s.clone()));

        let eq_impls = &impl_map["prelude/eq"];
        let mut imports = vec![];

        // lower all the mir functions to lir expressions
        for (f, expr) in self.funcs {
            let e = expr.lower(&variants, &global_funcs, &externs, eq_impls, &mut imports);
            funcs.insert(f, e);
        }

        for (n, _) in self.typedecls.iter() {
            globals.insert(n.clone());
        }

        for n in self.external.iter() {
            globals.insert(n.clone());
        }

        for (def, _) in self.defs.iter() {
            globals.insert(def.clone());
        }

        for (v, _) in variants.iter() {
            globals.insert(v.clone());
        }

        // extract all the functions from the lir
        let mut extracted_funcs = HashMap::new();
        for (name, expr) in funcs {
            let (_, funcs) = expr.extract_funcs(&name, &mut func_types, &globals, &HashMap::new());
            extracted_funcs.extend(funcs)
        }

        // Insert imported eq functions into typedecls as imports
        // don't remember why this was here, but I'm going to leave it for further review
        // for import in imports {
        // find the type in the impl map
        // let t = impl_map["prelude/eq"]
        // .iter()
        // .find_map(|(n, t)| if *n == import { Some(t.clone()) } else { None })
        // .unwrap();

        // self.typedecls.insert(import, (Vis::Import, t));
        // }

        // add all types of functions that we know
        for (f, (vis, t)) in self.typedecls.iter() {
            let t = match t.clone() {
                Type::ForAll(_, _, a) => *a,
                a => a,
            };

            if let Type::Arrow(from, to) = t {
                func_types.insert(
                    f.clone(),
                    (
                        vis.clone(),
                        LLVMType::from_type(*from),
                        LLVMType::from_type(*to),
                    ),
                );
            }
        }

        let mut extern_types = HashMap::new();
        for f in self.external.iter() {
            let (_, t) = &self.typedecls[f];

            let (from, to) = match t.clone() {
                Type::Arrow(from, to) => {
                    let to = LLVMType::from_type(*to);
                    let from = match *from {
                        Type::Tuple(ts) => {
                            ts.iter().map(|t| LLVMType::from_type(t.clone())).collect()
                        }
                        Type::Unit => vec![],
                        a => vec![LLVMType::from_type(a)],
                    };

                    (from, to)
                }
                _ => panic!(),
            };

            extern_types.insert(f.clone(), (from, to));
        }

        LIRTree {
            external: self.external,
            extern_types,
            func_types,
            funcs: extracted_funcs,
            enums,
            variants,
            type_sizes,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum LIRExpression {
    Identifier(String, LLVMType),

    /// Call a closure with args. The closure is represented as
    /// (f, formals...), so this needs to be transformed into
    /// f(args..., formals...)
    Call(Box<LIRExpression>, Box<LIRExpression>, LLVMType),

    /// Call to extern function, must use c calling convention
    ExternCall(String, Vec<LIRExpression>, LLVMType),

    /// Call to global function as opposed to closure
    GlobalCall(String, Box<LIRExpression>, LLVMType),

    Lambda1(Option<String>, Box<LIRExpression>, LLVMType),

    Let1(String, Box<LIRExpression>, Box<LIRExpression>, LLVMType),

    If(
        Box<LIRExpression>,
        Box<LIRExpression>,
        Box<LIRExpression>,
        LLVMType,
    ),

    LetThunk(String, Box<LIRExpression>, Box<LIRExpression>, LLVMType),
    GotoThunk(String, LLVMType),

    // Constant Fields
    Num(i64, LLVMType), // A Number Literal
    Str(String),        // A String Literal, stores index into constant string array
    Unit,
    Tuple(Vec<LIRExpression>, LLVMType),
    List(Vec<LIRExpression>, LLVMType),
    True,
    False,

    GetTuple(Box<LIRExpression>, usize, LLVMType),
    CheckTuple(Box<LIRExpression>, usize, LLVMType),
    CastTuple(Box<LIRExpression>, String, LLVMType),

    Box(Box<LIRExpression>, LLVMType),
    Unbox(Box<LIRExpression>, LLVMType),

    NullClosure(String, LLVMType),

    LLVM(String, String, LLVMType),
}

impl LIRExpression {
    fn free_non_globals(&self, vars: &HashSet<String>) -> Vec<(String, LLVMType)> {
        match self {
            Self::True | Self::False => vec![],
            Self::Num(..) => vec![],
            Self::Str(..) => vec![],
            Self::Unit => vec![],
            Self::Identifier(a, t) => {
                if vars.contains(a) {
                    vec![]
                } else {
                    vec![(a.clone(), t.clone())]
                }
            }
            Self::Tuple(es, _) => {
                let mut free = vec![];
                for e in es {
                    free.extend(e.free_non_globals(vars))
                }

                free
            }
            Self::List(es, _) => {
                let mut free = vec![];
                for e in es {
                    free.extend(e.free_non_globals(vars))
                }

                free
            }
            Self::If(cond, yes, no, _) => {
                let mut free = vec![];
                free.extend(cond.free_non_globals(vars));
                free.extend(yes.free_non_globals(vars));
                free.extend(no.free_non_globals(vars));

                free
            }
            Self::Lambda1(x, body, _) => {
                let mut vars = vars.clone();
                if x.is_some() {
                    vars.insert(x.clone().unwrap());
                }

                body.free_non_globals(&vars)
            }
            Self::Let1(x, exp, body, _) => {
                let mut free = exp.free_non_globals(vars);

                let mut vars = vars.clone();
                vars.insert(x.clone());
                free.extend(body.free_non_globals(&vars));

                free
            }
            Self::Call(f, args, _) => {
                let mut free = vec![];
                free.extend(f.free_non_globals(vars));
                free.extend(args.free_non_globals(vars));
                free
            }
            Self::CastTuple(..) => vec![],
            Self::CheckTuple(..) => vec![],
            Self::GetTuple(..) => vec![],
            Self::GlobalCall(_, args, _) => args.free_non_globals(vars),
            Self::ExternCall(_, args, _) => {
                let mut free = vec![];
                for e in args {
                    free.extend(e.free_non_globals(vars))
                }
                free
            }
            Self::Box(e, _) => e.free_non_globals(vars),
            Self::Unbox(e, _) => e.free_non_globals(vars),
            Self::LLVM(..) => vec![],
            Self::LetThunk(_, a, b, _) => {
                let mut free = vec![];
                free.extend(a.free_non_globals(vars));
                free.extend(b.free_non_globals(vars));
                free
            }
            Self::GotoThunk(_, _) => vec![],
            Self::NullClosure(_, _) => vec![],
        }
    }

    fn extract_funcs(
        self,
        id: &String,
        types: &mut HashMap<String, (Vis, LLVMType, LLVMType)>,
        globals: &HashSet<String>,
        subs: &HashMap<String, LLVMType>,
    ) -> (LIRExpression, HashMap<String, LIRExpression>) {
        let freshen_var = |id: String, cs: &HashMap<String, LIRExpression>| {
            if cs.contains_key(&id) {
                crate::gen_var("lambda")
            } else {
                id
            }
        };

        match self {
            Self::Lambda1(_, body, t) => {
                let (from, to) = match t {
                    LLVMType::Struct(ts) => match ts[0].clone() {
                        LLVMType::Func(from, to) => (from, to),
                        _ => panic!(),
                    },
                    _ => panic!(),
                };
                let arg_t = from.clone();

                let (mut e, mut funcs) =
                    body.extract_funcs(&crate::gen_var("lambda"), types, globals, subs);

                // this is a closure, so we need to modify the function to take in
                // a boxed tuple of our formal variables
                let formals = e.free_non_globals(globals);

                // the type of our environment, a boxed tuple
                let env_tup_t = match formals.len() {
                    0 => LLVMType::Void,
                    _ => LLVMType::Struct(formals.clone().into_iter().map(|(_, a)| a).collect()),
                };
                let env_t = LLVMType::Ptr(Box::new(env_tup_t.clone()));

                let env_tup = match formals.len() {
                    0 => Self::Box(
                        Box::new(Self::Unit),
                        LLVMType::Ptr(Box::new(LLVMType::Void)),
                    ),
                    _ => LIRExpression::Box(
                        Box::new(LIRExpression::Tuple(
                            formals
                                .clone()
                                .into_iter()
                                .map(|(name, t)| LIRExpression::Identifier(name, t))
                                .collect(),
                            env_tup_t.clone(),
                        )),
                        env_t.clone(),
                    ),
                };

                // modify the from type of our lambda to take a tuple of (arg.0, env)
                let (from, n) = match *from {
                    LLVMType::Void => (env_t.clone(), 0),
                    a => (LLVMType::Struct(vec![a, env_t.clone()]), 1),
                };

                if id.starts_with("lambda.") {
                    let env_name = if formals.len() > 0 {
                        // now modify the body of the lambda expression to extract
                        // the formals from the env which is passed in
                        let env_name = crate::gen_var("env");
                        let env_var =
                            LIRExpression::Identifier(env_name.clone(), env_tup_t.clone());
                        for (i, (name, t)) in formals.clone().into_iter().enumerate() {
                            let e_ty = e.ty();
                            e = LIRExpression::Let1(
                                name,
                                Box::new(LIRExpression::GetTuple(Box::new(env_var.clone()), i, t)),
                                Box::new(e),
                                e_ty,
                            )
                        }
                        env_name
                    } else {
                        "".to_string()
                    };
                    // now we need to make arg.0 point to the actual arg...
                    // this means extracting the first arg from the tuple,
                    // but only if the arg isn't type void
                    // since n is the index in the tupel of the env,
                    // as long as n isn't zero we have args to extract
                    if n != 0 {
                        let args = LIRExpression::GetTuple(
                            Box::new(LIRExpression::Identifier("arg.0".to_string(), from.clone())),
                            0,
                            *arg_t.clone(),
                        );

                        // now go through the lambda body, replacing every instance of arg.0 with
                        // our new args
                        let arg_name = crate::gen_var("args");
                        let e_ty = e.ty();
                        e = LIRExpression::Let1(
                            arg_name.clone(),
                            Box::new(args),
                            Box::new(
                                e.replace("arg.0", LIRExpression::Identifier(arg_name, *arg_t)),
                            ),
                            e_ty,
                        );
                    }

                    if formals.len() > 0 {
                        // and now a let statement for the env
                        let e_ty = e.ty();
                        e = LIRExpression::Let1(
                            env_name,
                            Box::new(LIRExpression::Unbox(
                                Box::new(LIRExpression::GetTuple(
                                    Box::new(LIRExpression::Identifier(
                                        "arg.0".to_string(),
                                        from.clone(),
                                    )),
                                    n,
                                    env_t.clone(),
                                )),
                                env_tup_t.clone(),
                            )),
                            Box::new(e),
                            e_ty,
                        );
                    }
                }

                // insert into our list of closures
                funcs.insert(id.clone(), e);
                // insert into list of function types
                types.insert(id.clone(), (Vis::Private, from.clone(), *to.clone()));

                // get the type of our closure
                let lambda_t = LLVMType::Func(Box::new(from.clone()), to.clone());
                let clos_t = LLVMType::Struct(vec![lambda_t, env_t.clone()]);

                // return tuple of function and environment
                (
                    LIRExpression::Tuple(
                        vec![
                            LIRExpression::Identifier(
                                id.clone(),
                                LLVMType::Func(Box::new(from), to),
                            ),
                            // build the environment
                            env_tup,
                        ],
                        clos_t,
                    ),
                    funcs,
                )
            }
            Self::GlobalCall(f, args, t) => {
                let (args, cs) = args.extract_funcs(id, types, globals, subs);
                (Self::GlobalCall(f, Box::new(args), t), cs)
            }
            Self::ExternCall(f, args, t) => {
                let mut cs = HashMap::new();
                let mut newes = vec![];

                for e in args {
                    let id = freshen_var(id.clone(), &cs);
                    let (e, newcs) = e.extract_funcs(&id, types, globals, subs);
                    newes.push(e);
                    cs.extend(newcs.into_iter());
                }

                (Self::ExternCall(f, newes, t), cs)
            }
            Self::Call(func, args, t) => {
                let (e, mut cs) = func.extract_funcs(id, types, globals, subs);

                let id = freshen_var(id.clone(), &cs);
                let (argse, argscs) = args.extract_funcs(&id, types, globals, subs);
                cs.extend(argscs.into_iter());

                (Self::Call(Box::new(e), Box::new(argse), t), cs)
            }
            Self::Let1(name, exp, body, _) => {
                let (e, mut cs) = exp.extract_funcs(id, types, globals, subs);

                let mut subs = subs.clone();
                subs.insert(name.clone(), e.ty());

                let id = freshen_var(id.clone(), &cs);
                let (bodye, bodycs) = body.extract_funcs(&id, types, globals, &subs);

                cs.extend(bodycs.into_iter());
                let t = bodye.ty();

                (Self::Let1(name, Box::new(e), Box::new(bodye), t), cs)
            }
            Self::Tuple(es, _) => {
                let mut cs = HashMap::new();
                let mut newes = vec![];

                let mut ts = vec![];

                for e in es {
                    let id = freshen_var(id.clone(), &cs);
                    let (e, newcs) = e.extract_funcs(&id, types, globals, subs);
                    ts.push(e.ty());
                    newes.push(e);
                    cs.extend(newcs.into_iter());
                }

                (Self::Tuple(newes, LLVMType::Struct(ts)), cs)
            }
            Self::If(cond, yes, no, _) => {
                let (e1, mut cs) = cond.extract_funcs(id, types, globals, subs);
                let id = freshen_var(id.clone(), &cs);
                let (e2, yescs) = yes.extract_funcs(&id, types, globals, subs);

                let id = freshen_var(id, &yescs);
                let (e3, nocs) = no.extract_funcs(&id, types, globals, subs);

                let t = e2.ty();

                cs.extend(yescs.into_iter());
                cs.extend(nocs.into_iter());

                (Self::If(Box::new(e1), Box::new(e2), Box::new(e3), t), cs)
            }
            Self::Identifier(s, t) => {
                let t = subs.get(&s).unwrap_or(&t).clone();
                (Self::Identifier(s, t), HashMap::new())
            }
            Self::GetTuple(tup, i, t) => {
                let (tup, cs) = tup.extract_funcs(id, types, globals, subs);
                (Self::GetTuple(Box::new(tup), i, t), cs)
            }
            Self::CheckTuple(tup, i, t) => {
                let (tup, cs) = tup.extract_funcs(id, types, globals, subs);
                (Self::CheckTuple(Box::new(tup), i, t), cs)
            }
            Self::CastTuple(tup, name, _) => {
                let (tup, cs) = tup.extract_funcs(id, types, globals, subs);
                let t = LLVMType::Named(name.clone());
                (Self::CastTuple(Box::new(tup), name, t), cs)
            }
            Self::Box(e, t) => {
                let (e, cs) = e.extract_funcs(id, types, globals, subs);
                (Self::Box(Box::new(e), t), cs)
            }
            Self::Unbox(e, t) => {
                let (e, cs) = e.extract_funcs(id, types, globals, subs);
                (Self::Unbox(Box::new(e), t), cs)
            }
            Self::LetThunk(name, thunk, first, _) => {
                let (thunk, mut cs) = thunk.extract_funcs(id, types, globals, subs);
                let id = freshen_var(id.clone(), &cs);
                let (first, firstcs) = first.extract_funcs(&id, types, globals, subs);

                cs.extend(firstcs.into_iter());

                let t = first.ty();

                (
                    Self::LetThunk(name, Box::new(thunk), Box::new(first), t),
                    cs,
                )
            }
            _ => (self, HashMap::new()),
        }
    }

    pub fn ty(&self) -> LLVMType {
        match self {
            Self::True | Self::False => LLVMType::I1,
            Self::LetThunk(_, _, _, t) => t.clone(),
            Self::GotoThunk(_, t) => t.clone(),
            Self::GetTuple(_, _, t) => t.clone(),
            Self::Unit => LLVMType::Void,
            Self::Call(_, _, t) => t.clone(),
            Self::GlobalCall(_, _, t) => t.clone(),
            Self::Identifier(_, t) => t.clone(),
            Self::Lambda1(_, _, t) => t.clone(),
            Self::Str(..) => LLVMType::Str,
            Self::Let1(_, _, _, t) => t.clone(),
            Self::If(_, _, _, t) => t.clone(),
            Self::Num(_, t) => t.clone(),
            Self::Tuple(_, t) => t.clone(),
            Self::CheckTuple(_, _, t) => t.clone(),
            Self::CastTuple(_, _, t) => t.clone(),
            Self::ExternCall(_, _, t) => t.clone(),
            Self::Box(_, t) => t.clone(),
            Self::Unbox(_, t) => t.clone(),
            Self::LLVM(_, _, t) => t.clone(),
            Self::NullClosure(_, t) => t.clone(),
            Self::List(_, t) => t.clone(),
        }
    }

    fn replace(self, id: &str, e: LIRExpression) -> Self {
        match self {
            Self::Identifier(n, t) => {
                if n == id {
                    e
                } else {
                    Self::Identifier(n, t)
                }
            }
            Self::Call(f, args, t) => {
                let f = f.replace(id, e.clone());
                let args = args.replace(id, e);
                Self::Call(Box::new(f), Box::new(args), t)
            }
            Self::CastTuple(tup, n, t) => Self::CastTuple(Box::new(tup.replace(id, e)), n, t),
            Self::CheckTuple(tup, i, t) => Self::CheckTuple(Box::new(tup.replace(id, e)), i, t),
            Self::GetTuple(tup, i, t) => Self::GetTuple(Box::new(tup.replace(id, e)), i, t),
            Self::GlobalCall(n, args, t) => Self::GlobalCall(n, Box::new(args.replace(id, e)), t),
            Self::If(cond, yes, no, t) => {
                let cond = Box::new(cond.replace(id, e.clone()));
                let yes = Box::new(yes.replace(id, e.clone()));
                let no = Box::new(no.replace(id, e));

                Self::If(cond, yes, no, t)
            }
            Self::Lambda1(arg, body, t) => Self::Lambda1(arg, Box::new(body.replace(id, e)), t),
            Self::Let1(n, x, body, t) => {
                let x = Box::new(x.replace(id, e.clone()));
                let body = Box::new(body.replace(id, e));
                Self::Let1(n, x, body, t)
            }
            Self::Box(exp, t) => Self::Box(Box::new(exp.replace(id, e)), t),
            Self::Unbox(exp, t) => Self::Unbox(Box::new(exp.replace(id, e)), t),
            a => a,
        }
    }
}

impl MIRExpression {
    pub fn lower(
        self,
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        global: &HashSet<String>,
        externs: &HashSet<String>,
        eq_impls: &Vec<(String, Type)>,
        imports: &mut Vec<String>,
    ) -> LIRExpression {
        match self {
            Self::True => LIRExpression::True,
            Self::False => LIRExpression::False,
            Self::Call(f, args, t) => {
                let args = args.lower(vars, global, externs, eq_impls, imports);

                // auto box args if necessary
                if let MIRExpression::Identifier(n, _) = &*f.clone() {
                    // the llvm macro directly injects llvm code
                    // for the expression
                    if n.starts_with("llvm!") {
                        match args {
                            LIRExpression::Tuple(es, _) => match (es[0].clone(), es[1].clone()) {
                                (LIRExpression::Str(out), LIRExpression::Str(body)) => {
                                    return LIRExpression::LLVM(
                                        out,
                                        body,
                                        LLVMType::from_type(t.unwrap()),
                                    );
                                }
                                _ => panic!(),
                            },
                            _ => panic!(),
                        }
                    }

                    if externs.contains(n) {
                        let args = match args {
                            LIRExpression::Unit => vec![],
                            LIRExpression::Tuple(es, _) => es,
                            a => vec![a],
                        };

                        return LIRExpression::ExternCall(
                            n.clone(),
                            args,
                            LLVMType::from_type(t.unwrap()),
                        );
                    }

                    if global.contains(n) {
                        return LIRExpression::GlobalCall(
                            n.clone(),
                            Box::new(args),
                            LLVMType::from_type(t.unwrap()),
                        );
                    }
                }

                let f = f.lower(vars, global, externs, eq_impls, imports);
                LIRExpression::Call(Box::new(f), Box::new(args), LLVMType::from_type(t.unwrap()))
            }
            Self::Lambda1(arg, body, t) => {
                let (in_t, out_t) = match t.clone().unwrap() {
                    Type::Arrow(in_t, out_t) => {
                        (LLVMType::from_type(*in_t), LLVMType::from_type(*out_t))
                    }
                    _ => panic!(),
                };

                if let Some(arg) = arg {
                    LIRExpression::Lambda1(
                        Some(arg.clone()),
                        Box::new(LIRExpression::Let1(
                            arg,
                            Box::new(LIRExpression::Identifier("arg.0".to_string(), in_t)),
                            Box::new(body.lower(vars, global, externs, eq_impls, imports)),
                            out_t,
                        )),
                        LLVMType::from_type(t.unwrap()),
                    )
                } else {
                    LIRExpression::Lambda1(
                        None,
                        Box::new(body.lower(vars, global, externs, eq_impls, imports)),
                        LLVMType::from_type(t.unwrap()),
                    )
                }
            }
            Self::Match(m, pats, t) => {
                if pats.len() == 1 {
                    // unit type always passes the pattern match
                    if let (Pattern::Unit(..), expr) = &pats[0] {
                        return expr.clone().lower(vars, global, externs, eq_impls, imports);
                    }

                    // Single var pattern just becomes a let expression
                    if let (Pattern::Var(s, t2), expr) = &pats[0] {
                        return LIRExpression::Let1(
                            s.clone(),
                            Box::new(m.lower(vars, global, externs, eq_impls, imports)),
                            Box::new(expr.clone().lower(vars, global, externs, eq_impls, imports)),
                            LLVMType::from_type(t2.clone().unwrap()),
                        );
                    }
                }

                // transform if statements
                // TODO

                // General case
                if let Self::Identifier(n, _) = *m {
                    Self::match_code(
                        n,
                        &pats,
                        LLVMType::from_type(t.unwrap()),
                        vars,
                        global,
                        externs,
                        eq_impls,
                        imports,
                    )
                } else {
                    let n = crate::gen_var("match");
                    LIRExpression::Let1(
                        n.clone(),
                        Box::new(m.lower(vars, global, externs, eq_impls, imports)),
                        Box::new(Self::match_code(
                            n,
                            &pats,
                            LLVMType::from_type(t.clone().unwrap()),
                            vars,
                            global,
                            externs,
                            eq_impls,
                            imports,
                        )),
                        LLVMType::from_type(t.unwrap()),
                    )
                }
            }
            Self::Identifier(s, t) => {
                // if the type of an identifier is a function and in our globals,
                // wrap it in a null closure (a closure with null env)
                let need_wrap = if let Some(Type::Arrow(_, _)) = t {
                    global.contains(&s)
                } else {
                    false
                };

                let t = LLVMType::from_type(t.unwrap());
                if need_wrap {
                    LIRExpression::NullClosure(s, t)
                } else {
                    LIRExpression::Identifier(s, t)
                }
            }
            Self::Num(n, t) => LIRExpression::Num(n as i64, LLVMType::from_type(t.unwrap())),
            Self::String(s, _) => LIRExpression::Str(s),
            Self::Tuple(es, t) => LIRExpression::Tuple(
                es.into_iter()
                    .map(|e| e.lower(vars, global, externs, eq_impls, imports))
                    .collect(),
                LLVMType::from_type(t.unwrap()),
            ),
            Self::List(es, t) => LIRExpression::List(
                es.into_iter()
                    .map(|e| e.lower(vars, global, externs, eq_impls, imports))
                    .collect(),
                LLVMType::from_type(t.unwrap()),
            ),
            Self::Unit(_) => LIRExpression::Unit,
        }
    }

    fn match_code(
        x: String,                         // name of expr matching against
        pats: &[(Pattern, MIRExpression)], // list of patterns and their expressions
        ty: LLVMType,                      // output type of the match statement
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        global: &HashSet<String>,
        externs: &HashSet<String>,
        eq_impls: &Vec<(String, Type)>,
        imports: &mut Vec<String>,
    ) -> LIRExpression {
        if pats.is_empty() {
            panic!("Ran out of patterns");
        } else if pats.len() == 1 {
            let (pat, exp) = &pats[0];
            Self::match_pattern_last(
                pat.clone(),
                LIRExpression::Identifier(x, LLVMType::from_type(pat.ty())),
                exp.clone().lower(vars, global, externs, eq_impls, imports),
                ty,
                vars,
                eq_impls,
            )
        } else {
            let thunk_name = crate::gen_var("thunk");
            let fail = Self::match_code(
                x.clone(),
                &pats[1..],
                ty.clone(),
                vars,
                global,
                externs,
                eq_impls,
                imports,
            );

            let (pat, exp) = &pats[0];
            let thunk = LIRExpression::GotoThunk(thunk_name.clone(), fail.ty());

            // ty is the output type of this match statement
            // pat.ty() is the type of the pattern
            // exp.ty() is the type of the expression and should match ty
            // assert_eq!(ty, LLVMType::from_type(exp.ty()));

            let first = Self::match_pattern(
                pat.clone(),
                // since this passed type checking the type of our match variable x
                // should be the same type as the pattern
                LIRExpression::Identifier(x, LLVMType::from_type(pat.ty())),
                exp.clone().lower(vars, global, externs, eq_impls, imports),
                thunk,
                ty.clone(),
                vars,
                eq_impls,
                imports,
            );

            LIRExpression::LetThunk(thunk_name, Box::new(fail), Box::new(first), ty)
        }
    }

    fn match_pattern_last(
        pat: Pattern,
        exp: LIRExpression,
        yes: LIRExpression,
        ty: LLVMType,
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        eq_impls: &Vec<(String, Type)>,
    ) -> LIRExpression {
        match pat {
            Pattern::Num(..)
            | Pattern::Unit(_)
            | Pattern::True
            | Pattern::False
            | Pattern::String(..) => yes,
            Pattern::Var(x, _) => {
                LIRExpression::Let1(x, Box::new(exp), Box::new(yes.clone()), yes.ty())
            }
            Pattern::Tuple(ps, _) => {
                // due to type checking this is already guaranteed to be a tuple, so instead we
                // just verify/gen ir for the components
                Self::match_components_last(&ps, 0, exp, yes, vars, eq_impls)
            }
            Pattern::Cons(n, args, t) => {
                let t = t.unwrap();
                let tname = t.to_string();

                if let Some(var) = vars.get(&tname) {
                    // number of enum to check against,
                    let (_enum_id, (_, enum_t)) =
                        var.iter().enumerate().find(|s| s.1 .0 == n).unwrap();

                    let ps = match *args {
                        Pattern::Tuple(ps, _) => ps,
                        _ => vec![*args],
                    };

                    let v = crate::gen_var("f");

                    LIRExpression::Let1(
                        v.clone(),
                        Box::new(LIRExpression::CastTuple(Box::new(exp), n, enum_t.clone())),
                        Box::new(Self::match_components_last(
                            &ps,
                            1,
                            LIRExpression::Identifier(v.clone(), enum_t.clone()),
                            yes.clone(),
                            vars,
                            eq_impls,
                        )),
                        ty.clone(),
                    )
                } else {
                    Self::match_pattern_last(*args, exp, yes, ty, vars, eq_impls)
                }
            }
            Pattern::Any(_) => yes,
        }
    }

    fn match_pattern(
        pat: Pattern,
        exp: LIRExpression,
        yes: LIRExpression,
        no: LIRExpression,
        ty: LLVMType,
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        eq_impls: &Vec<(String, Type)>,
        imports: &mut Vec<String>,
    ) -> LIRExpression {
        match pat {
            Pattern::Unit(_) => {
                // since this passed type checking this always evaluates to true
                yes
            }
            Pattern::True => LIRExpression::If(Box::new(exp), Box::new(yes), Box::new(no), ty),
            Pattern::False => LIRExpression::If(Box::new(exp), Box::new(no), Box::new(yes), ty),
            Pattern::Num(n, t) => {
                // Find the name of the function who implements eq for this num type
                let f = resolve_typefn(eq_impls, eq_type!(t.as_ref().unwrap())).unwrap();
                imports.push(f.clone());

                LIRExpression::If(
                    Box::new(LIRExpression::GlobalCall(
                        f,
                        Box::new(LIRExpression::Tuple(
                            vec![
                                exp,
                                LIRExpression::Num(n, LLVMType::from_type(t.clone().unwrap())),
                            ],
                            LLVMType::Struct(vec![
                                LLVMType::from_type(t.clone().unwrap()),
                                LLVMType::from_type(t.unwrap()),
                            ]),
                        )),
                        LLVMType::I1,
                    )),
                    Box::new(yes),
                    Box::new(no),
                    ty,
                )
            }
            Pattern::String(s, _) => {
                // Find the name of the function who implements eq for str type
                let f = resolve_typefn(eq_impls, eq_type!(Type::Str)).unwrap();
                imports.push(f.clone());

                LIRExpression::If(
                    Box::new(LIRExpression::GlobalCall(
                        f,
                        Box::new(LIRExpression::Tuple(
                            vec![exp, LIRExpression::Str(s)],
                            LLVMType::Struct(vec![
                                LLVMType::from_type(Type::Str),
                                LLVMType::from_type(Type::Str),
                            ]),
                        )),
                        LLVMType::I1,
                    )),
                    Box::new(yes),
                    Box::new(no),
                    ty,
                )
            }
            Pattern::Var(x, _) => {
                LIRExpression::Let1(x, Box::new(exp), Box::new(yes.clone()), yes.ty())
            }
            Pattern::Tuple(ps, _) => {
                // due to type checking this is already guaranteed to be a tuple, so instead we
                // just verify/gen ir for the components
                Self::match_components(&ps, 0, exp, yes, no, vars, eq_impls, imports)
            }
            Pattern::Cons(n, args, t) => {
                let t = t.unwrap();
                let tname = t.to_string();

                if let Some(var) = vars.get(&tname) {
                    // number of enum to check against,
                    let (enum_id, (_, enum_t)) =
                        var.iter().enumerate().find(|s| s.1 .0 == n).unwrap();

                    let ps = match *args {
                        Pattern::Tuple(ps, _) => ps,
                        _ => vec![*args],
                    };

                    let v = crate::gen_var("f");

                    LIRExpression::If(
                        Box::new(LIRExpression::CheckTuple(
                            Box::new(exp.clone()),
                            enum_id,
                            LLVMType::I1,
                        )),
                        Box::new(LIRExpression::Let1(
                            v.clone(),
                            Box::new(LIRExpression::CastTuple(Box::new(exp), n, enum_t.clone())),
                            Box::new(Self::match_components(
                                &ps,
                                1,
                                LIRExpression::Identifier(v.clone(), enum_t.clone()),
                                yes.clone(),
                                no.clone(),
                                vars,
                                eq_impls,
                                imports,
                            )),
                            ty.clone(),
                        )),
                        Box::new(no),
                        ty,
                    )
                } else {
                    Self::match_pattern(*args, exp, yes, no, ty, vars, eq_impls, imports)
                }
            }
            Pattern::Any(_) => yes,
        }
    }

    fn match_components(
        ps: &[Pattern],
        n: usize,
        exp: LIRExpression,
        yes: LIRExpression,
        no: LIRExpression,
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        eq_impls: &Vec<(String, Type)>,
        imports: &mut Vec<String>,
    ) -> LIRExpression {
        if ps.is_empty() {
            yes
        } else {
            let p = &ps[0];
            let rest = Self::match_components(
                &ps[1..],
                n + 1,
                exp.clone(),
                yes,
                no.clone(),
                vars,
                eq_impls,
                imports,
            );

            let pt = LLVMType::from_type(p.ty());
            let et = match exp.ty() {
                LLVMType::Struct(ts) => ts.get(n).cloned().unwrap_or(LLVMType::Void),
                a => panic!("{a:?}"),
            };

            // check for unbox
            let et_is_ptr = if let LLVMType::Ptr(_) = et {
                true
            } else {
                false
            };

            let pt_is_ptr = if let LLVMType::Ptr(_) = pt {
                true
            } else {
                false
            };

            let newe = if et_is_ptr && !pt_is_ptr {
                LIRExpression::Unbox(
                    Box::new(LIRExpression::GetTuple(
                        Box::new(exp.clone()),
                        n,
                        LLVMType::Ptr(Box::new(LLVMType::Void)), // type shouldn't matter fingers crossed
                    )),
                    pt,
                )
            } else {
                LIRExpression::GetTuple(Box::new(exp.clone()), n, pt)
            };

            Self::match_pattern(p.clone(), newe, rest, no, exp.ty(), vars, eq_impls, imports)
        }
    }

    fn match_components_last(
        ps: &[Pattern],
        n: usize,
        exp: LIRExpression,
        yes: LIRExpression,
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        eq_impls: &Vec<(String, Type)>,
    ) -> LIRExpression {
        if ps.is_empty() {
            yes
        } else {
            let p = &ps[0];
            let rest =
                Self::match_components_last(&ps[1..], n + 1, exp.clone(), yes, vars, eq_impls);

            let pt = LLVMType::from_type(p.ty());
            let et = match exp.ty() {
                LLVMType::Struct(ts) => ts.get(n).cloned().unwrap_or(LLVMType::Void),
                a => panic!("{a:?}"),
            };

            // check for unbox
            let et_is_ptr = if let LLVMType::Ptr(_) = et {
                true
            } else {
                false
            };

            let pt_is_ptr = if let LLVMType::Ptr(_) = pt {
                true
            } else {
                false
            };

            let newe = if et_is_ptr && !pt_is_ptr {
                LIRExpression::Unbox(
                    Box::new(LIRExpression::GetTuple(
                        Box::new(exp.clone()),
                        n,
                        LLVMType::Ptr(Box::new(LLVMType::Void)), // type shouldn't matter fingers crossed
                    )),
                    pt,
                )
            } else {
                LIRExpression::GetTuple(Box::new(exp.clone()), n, pt)
            };

            Self::match_pattern_last(p.clone(), newe, rest, exp.ty(), vars, eq_impls)
        }
    }
}
