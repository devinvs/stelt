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

macro_rules! eq_type {
    ($i:expr) => {
        Type::Arrow(
            Box::new(Type::Tuple(vec![$i.clone(), $i.clone()])),
            Box::new(Type::Ident("bool".to_string())),
        )
    };
}

impl LIRExpression {
    fn str_from_cons(expr: &LIRExpression) -> String {
        match expr {
            LIRExpression::GlobalCall(f, args, _) => {
                if f.starts_with("Cons") {
                    match *args.clone() {
                        LIRExpression::Tuple(es, _) => {
                            let c = match es[0].clone() {
                                LIRExpression::GlobalCall(_, arg, _) => match *arg {
                                    LIRExpression::Num(n, _) => char::from_u32(n as u32).unwrap(),
                                    _ => panic!(),
                                },
                                a => panic!("{a:?}"),
                            };
                            let mut s = String::new();
                            s.push(c);

                            s.push_str(&LIRExpression::str_from_cons(&es[1]));
                            s
                        }
                        _ => panic!(),
                    }
                } else if f.starts_with("Nil") {
                    "".to_string()
                } else {
                    panic!()
                }
            }
            a => panic!("found {a:?}"),
        }
    }
}

#[derive(Debug)]
pub struct LIRTree {
    /// Set of functions defined in other llvm modules
    pub import_funcs: HashMap<String, LLVMType>,

    /// Set of external function names
    pub external: HashSet<String>,

    /// Named Types
    pub structs: HashMap<String, LLVMType>,
    pub enums: HashMap<String, LLVMType>,

    /// Enum Variants
    pub variants: HashMap<String, Vec<(String, LLVMType)>>,

    /// Map of function names to their llvm types
    pub func_types: HashMap<String, (LLVMType, LLVMType)>,

    pub extern_types: HashMap<String, (Vec<LLVMType>, LLVMType)>,

    /// Map of function names to their expressions
    pub funcs: HashMap<String, LIRExpression>,

    pub type_sizes: HashMap<String, usize>,
}

impl MIRTree {
    pub fn lower(self) -> LIRTree {
        // get list of global names
        let mut globals = HashSet::new();
        globals.insert("arg.0".to_string());

        globals.extend(self.import_funcs.clone().into_keys());

        let mut func_types = HashMap::new();
        let mut funcs = HashMap::new();

        // convert all types into their llvm forms
        let mut structs = HashMap::new();
        let mut variants = HashMap::new();
        let mut enums = HashMap::new();

        for (name, t) in self.types {
            match t {
                DataDecl::Sum(_, _, cons) => {
                    let vars = LLVMType::from_enum(cons);
                    variants.insert(name, vars);
                }
                DataDecl::Product(_, _, mems) => {
                    structs.insert(name, LLVMType::from_struct(mems));
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
        for (f, _) in self.funcs.iter() {
            global_funcs.insert(f.clone());
        }
        for n in self.external.iter() {
            global_funcs.insert(n.clone());
        }
        for (s, _) in structs.iter() {
            global_funcs.insert(s.clone());
        }
        for vars in variants.values() {
            for (e, _) in vars {
                global_funcs.insert(e.clone());
            }
        }
        global_funcs.extend(self.import_funcs.clone().into_keys());

        let mut externs = HashSet::new();
        externs.extend(self.external.iter().map(|s| s.clone()));

        let eq_impls = &self.impl_map["eq"];

        // lower all the mir functions to lir expressions
        for (f, expr) in self.funcs {
            globals.insert(f.clone());
            let e = expr.lower(&variants, &global_funcs, &externs, eq_impls);
            funcs.insert(f, e);
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

        // add all types of functions that we know
        for (f, t) in self.typedefs.iter() {
            let t = match t.clone() {
                Type::ForAll(_, a) => *a,
                a => a,
            };

            if let Type::Arrow(from, to) = t {
                func_types.insert(
                    f.clone(),
                    (LLVMType::from_type(*from), LLVMType::from_type(*to)),
                );
            }
        }

        let mut extern_types = HashMap::new();
        for f in self.external.iter() {
            let t = &self.typedefs[f];

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

        let import_funcs = self
            .import_funcs
            .into_iter()
            .map(|(name, t)| (name, LLVMType::from_type(t)))
            .collect();

        LIRTree {
            import_funcs,
            external: self.external,
            extern_types,
            func_types,
            funcs: extracted_funcs,
            structs,
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

    List(Vec<LIRExpression>, LLVMType),

    LetThunk(String, Box<LIRExpression>, Box<LIRExpression>, LLVMType),
    GotoThunk(String, LLVMType),

    // Constant Fields
    Num(u64, LLVMType), // A Number Literal
    Str(String),        // A String Literal, stores index into constant string array
    Unit,
    Tuple(Vec<LIRExpression>, LLVMType),

    GetTuple(Box<LIRExpression>, usize, LLVMType),
    CheckTuple(Box<LIRExpression>, usize, LLVMType),
    CastTuple(Box<LIRExpression>, String, LLVMType),

    Box(Box<LIRExpression>, LLVMType),
    Unbox(Box<LIRExpression>, LLVMType),
    Error(String),

    LLVM(String, String, LLVMType),
}

impl LIRExpression {
    fn free_non_globals(&self, vars: &HashSet<String>) -> Vec<(String, LLVMType)> {
        match self {
            Self::Error(..) => vec![],
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
            Self::List(es, _) => {
                let mut free = vec![];
                for e in es {
                    free.extend(e.free_non_globals(vars))
                }
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
        }
    }

    fn extract_funcs(
        self,
        id: &String,
        types: &mut HashMap<String, (LLVMType, LLVMType)>,
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
                let mut free = HashSet::new();
                free.extend(body.free_non_globals(&globals));

                let (from, to) = match t.clone() {
                    LLVMType::Func(from, to) => (from, to),
                    _ => panic!(),
                };

                // must modify function type to include closure variables
                let mut from = match *from {
                    LLVMType::Struct(a) => a,
                    LLVMType::Void => vec![],
                    a => vec![a],
                };

                let argl = from.len();

                let mut inner = vec![t.clone()];
                let mut tup = vec![LIRExpression::Identifier(id.clone(), t)];

                for (s, t) in free.iter() {
                    tup.push(LIRExpression::Identifier(s.clone(), t.clone()));
                    inner.push(t.clone());
                    from.push(t.clone());
                }

                let t = LLVMType::Func(Box::new(LLVMType::Struct(from.clone())), to.clone());
                inner[0] = t.clone();
                // always true, just using the pattern matching
                if let LIRExpression::Identifier(_, ty) = &mut tup[0] {
                    *ty = t;
                }

                let (mut e, mut funcs) =
                    body.extract_funcs(&crate::gen_var("lambda"), types, globals, subs);
                if argl == 1 && free.len() > 0 {
                    e = e.replace(
                        "arg.0",
                        LIRExpression::GetTuple(
                            Box::new(LIRExpression::Identifier(
                                "arg.0".to_string(),
                                LLVMType::Struct(from.clone()),
                            )),
                            0,
                            from[0].clone(),
                        ),
                    );
                }

                // create let statements for formals
                for (i, (var, t)) in free.iter().enumerate() {
                    let et = e.ty();
                    let exp = LIRExpression::Let1(
                        var.clone(),
                        Box::new(LIRExpression::GetTuple(
                            Box::new(LIRExpression::Identifier(
                                "arg.0".to_string(),
                                LLVMType::Struct(from.clone()),
                            )),
                            argl + i,
                            t.clone(),
                        )),
                        Box::new(e),
                        et,
                    );
                    e = exp;
                }

                funcs.insert(id.clone(), e);

                types.insert(id.clone(), (LLVMType::Struct(from), *to));

                let clos_t = LLVMType::Struct(inner);

                (LIRExpression::Tuple(tup, clos_t), funcs)
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
            Self::Call(func, args, _) => {
                let (e, mut cs) = func.extract_funcs(id, types, globals, subs);

                let id = freshen_var(id.clone(), &cs);
                let (argse, argscs) = args.extract_funcs(&id, types, globals, subs);
                cs.extend(argscs.into_iter());

                // e is a closure, ie (f, args...)
                let out_t = match e.ty() {
                    LLVMType::Struct(ts) => match &ts[0] {
                        LLVMType::Func(_, b) => b.clone(),
                        a => panic!("wha? {a:?} {e:?}"),
                    },
                    a => panic!("expected closure, found {a:?}, {e:?}"),
                };

                (Self::Call(Box::new(e), Box::new(argse), *out_t), cs)
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

                if let LLVMType::Func(_, _) = t {
                    let tup_t = LLVMType::Struct(vec![t.clone()]);
                    (
                        Self::Tuple(vec![Self::Identifier(s, t)], tup_t),
                        HashMap::new(),
                    )
                } else {
                    (Self::Identifier(s, t), HashMap::new())
                }
            }
            Self::List(es, _) => {
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

                (Self::List(newes, ts.last().unwrap().clone()), cs)
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
            Self::LetThunk(_, _, _, t) => t.clone(),
            Self::GotoThunk(_, t) => t.clone(),
            Self::GetTuple(_, _, t) => t.clone(),
            Self::Unit => LLVMType::Void,
            Self::Call(_, _, t) => t.clone(),
            Self::GlobalCall(_, _, t) => t.clone(),
            Self::Error(_) => LLVMType::Void,
            Self::Identifier(_, t) => t.clone(),
            Self::Lambda1(_, _, t) => t.clone(),
            Self::Str(..) => LLVMType::Str,
            Self::Let1(_, _, _, t) => t.clone(),
            Self::If(_, _, _, t) => t.clone(),
            Self::Num(_, t) => t.clone(),
            Self::Tuple(_, t) => t.clone(),
            Self::List(_, t) => t.clone(),
            Self::CheckTuple(_, _, t) => t.clone(),
            Self::CastTuple(_, _, t) => t.clone(),
            Self::ExternCall(_, _, t) => t.clone(),
            Self::Box(_, t) => t.clone(),
            Self::Unbox(_, t) => t.clone(),
            Self::LLVM(_, _, t) => t.clone(),
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
            Self::List(es, t) => {
                let mut new = vec![];

                for exp in es {
                    new.push(exp.replace(id, e.clone()))
                }

                Self::List(new, t)
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
    ) -> LIRExpression {
        match self {
            Self::Call(f, args, t) => {
                let f = f.lower(vars, global, externs, eq_impls);
                let args = args.lower(vars, global, externs, eq_impls);

                // auto box args if necessary
                if let LIRExpression::Identifier(n, _) = &f {
                    // the llvm macro directly injects llvm code
                    // for the expression
                    if n.starts_with("llvm!") {
                        match args {
                            LIRExpression::Tuple(es, _) => {
                                let out = LIRExpression::str_from_cons(&es[0]);
                                let body = LIRExpression::str_from_cons(&es[1]);

                                return LIRExpression::LLVM(
                                    out.to_string(),
                                    body.to_string(),
                                    LLVMType::from_type(t.unwrap()),
                                );
                            }
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
                            Box::new(body.lower(vars, global, externs, eq_impls)),
                            out_t,
                        )),
                        LLVMType::from_type(t.unwrap()),
                    )
                } else {
                    LIRExpression::Lambda1(
                        None,
                        Box::new(body.lower(vars, global, externs, eq_impls)),
                        LLVMType::from_type(t.unwrap()),
                    )
                }
            }
            Self::Match(m, pats, t) => {
                if pats.len() == 1 {
                    // unit type always passes the pattern match
                    if let (Pattern::Unit(..), expr) = &pats[0] {
                        return expr.clone().lower(vars, global, externs, eq_impls);
                    }

                    // Single var pattern just becomes a let expression
                    if let (Pattern::Var(s, t2), expr) = &pats[0] {
                        return LIRExpression::Let1(
                            s.clone(),
                            Box::new(m.lower(vars, global, externs, eq_impls)),
                            Box::new(expr.clone().lower(vars, global, externs, eq_impls)),
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
                    )
                } else {
                    let n = crate::gen_var("match");
                    LIRExpression::Let1(
                        n.clone(),
                        Box::new(m.lower(vars, global, externs, eq_impls)),
                        Box::new(Self::match_code(
                            n,
                            &pats,
                            LLVMType::from_type(t.clone().unwrap()),
                            vars,
                            global,
                            externs,
                            eq_impls,
                        )),
                        LLVMType::from_type(t.unwrap()),
                    )
                }
            }
            Self::Identifier(s, t) => LIRExpression::Identifier(s, LLVMType::from_type(t.unwrap())),
            Self::Num(n, t) => LIRExpression::Num(n, LLVMType::from_type(t.unwrap())),
            Self::Tuple(es, t) => LIRExpression::Tuple(
                es.into_iter()
                    .map(|e| e.lower(vars, global, externs, eq_impls))
                    .collect(),
                LLVMType::from_type(t.unwrap()),
            ),
            Self::List(es, t) => LIRExpression::List(
                es.into_iter()
                    .map(|e| e.lower(vars, global, externs, eq_impls))
                    .collect(),
                LLVMType::from_type(t.unwrap()),
            ),
            Self::Unit(_) => LIRExpression::Unit,
            a => unimplemented!("{a:?}"),
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
    ) -> LIRExpression {
        if pats.is_empty() {
            LIRExpression::Error("No patterns matched".to_string())
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
                exp.clone().lower(vars, global, externs, eq_impls),
                thunk,
                ty.clone(),
                vars,
                eq_impls,
            );

            LIRExpression::LetThunk(thunk_name, Box::new(fail), Box::new(first), ty)
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
    ) -> LIRExpression {
        match pat {
            Pattern::Unit(_) => {
                // since this passed type checking this always evaluates to true
                yes
            }
            Pattern::Num(n, t) => LIRExpression::If(
                Box::new(LIRExpression::CheckTuple(
                    Box::new(LIRExpression::GlobalCall(
                        // Find the name of the function who implements eq for this num type
                        resolve_typefn(eq_impls, eq_type!(t.as_ref().unwrap())).unwrap(),
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
                        LLVMType::Named("bool".to_string()),
                    )),
                    1,
                    LLVMType::I1,
                )),
                Box::new(yes),
                Box::new(no),
                ty,
            ),
            Pattern::Var(x, _) => {
                LIRExpression::Let1(x, Box::new(exp), Box::new(yes.clone()), yes.ty())
            }
            Pattern::Tuple(ps, _) => {
                // due to type checking this is already guaranteed to be a tuple, so instead we
                // just verify/gen ir for the components
                Self::match_components(&ps, 0, exp, yes, no, vars, eq_impls)
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
                            Box::new(LIRExpression::CastTuple(
                                Box::new(exp),
                                format!("{}.{}", tname, n),
                                enum_t.clone(),
                            )),
                            Box::new(Self::match_components(
                                &ps,
                                1,
                                LIRExpression::Identifier(v.clone(), enum_t.clone()),
                                yes.clone(),
                                no.clone(),
                                vars,
                                eq_impls,
                            )),
                            ty.clone(),
                        )),
                        Box::new(no),
                        ty,
                    )
                } else {
                    Self::match_pattern(*args, exp, yes, no, ty, vars, eq_impls)
                }
            }
            Pattern::Any(_) => yes,
            a => unimplemented!("{a:?}"),
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

            Self::match_pattern(p.clone(), newe, rest, no, exp.ty(), vars, eq_impls)
        }
    }
}
