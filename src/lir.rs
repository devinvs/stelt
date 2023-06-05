use std::collections::HashMap;
use std::collections::HashSet;

use crate::llvm::LLVMType;

use crate::mir::MIRExpression;
use crate::mir::MIRTree;
use crate::parse_tree::Type;
use crate::parse_tree::Pattern;
use crate::parse_tree::DataDecl;

#[derive(Debug)]
pub struct LIRTree {
    /// Set of external function names
    pub external: HashSet<String>,

    /// Named Types
    pub structs: Vec<(String, LLVMType)>,
    pub enums: Vec<(String, LLVMType)>,

    /// Enum Variants
    pub variants: HashMap<String, Vec<(String, LLVMType)>>,

    /// Map of function names to their llvm types
    pub func_types: HashMap<String, (LLVMType, LLVMType)>,

    pub extern_types: HashMap<String, (Vec<LLVMType>, LLVMType)>,

    /// Map of function names to their expressions
    pub funcs: HashMap<String, LIRExpression>,
}

impl MIRTree {
    pub fn lower(self) -> LIRTree {
        // get list of global names
        let mut globals = HashSet::new();
        globals.insert("arg.0".to_string());

        globals.extend(crate::builtin::BUILTIN.keys().map(|s| s.clone()));

        let mut func_types = HashMap::new();
        let mut funcs = HashMap::new();

        // convert all types into their llvm forms
        let mut structs = vec![];
        let mut variants = HashMap::new();
        let mut enums = vec![];

        for (name, t) in self.types {
            match t {
                DataDecl::Sum(_, _, cons, _) => {
                    let vars = LLVMType::from_enum(&name, cons);
                    variants.insert(name, vars);
                },
                DataDecl::Product(_, _, mems, _) => {
                    structs.push((name, LLVMType::from_struct(mems)))
                }
            }
        }

        // for each type enum get the max size of its variants,
        // add paddning of bytes to the base type
        for (name, vars) in variants.iter() {
            let mut size = 8;

            for (_, var) in vars {
                size = size.max(var.size(size));
            }

            // align to the byte boundary
            size += size % 8;

            enums.push((name.clone(), LLVMType::Struct(vec![
                LLVMType::I8,
                LLVMType::Array(Box::new(LLVMType::I8), size / 8)
            ])));
        }


        // get list of global function and constructor names
        let mut global_funcs = HashSet::new();
        global_funcs.extend(crate::builtin::BUILTIN.keys().map(|s| s.clone()));
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


        let mut externs = HashSet::new();
        externs.extend(self.external.iter().map(|s| s.clone()));

        // lower all the mir functions to lir expressions
        for (f, expr) in self.funcs {
            globals.insert(f.clone());
            funcs.insert(f, expr.lower(&variants, &global_funcs, &externs));
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

        //eprintln!("{funcs:#?}");

        // extract all the functions from the lir
        let mut extracted_funcs = HashMap::new();
        for (name, expr) in funcs {
            let (_, funcs) = expr.extract_funcs(&name, &mut func_types, &globals, &HashMap::new());
            extracted_funcs.extend(funcs)
        }

        eprintln!("{extracted_funcs:#?}");


        // add all types of functions that we know
        for (f, t) in self.typedefs.iter() {
            let t = match t.clone() {
                Type::ForAll(_, a) => *a,
                a => a
            };

            if let Type::Arrow(from, to) = t {
                func_types.insert(f.clone(), (LLVMType::from_type(*from), LLVMType::from_type(*to)));
            } 
        }

        let mut extern_types = HashMap::new();
        for f in self.external.iter() {
            let t = &self.typedefs[f];

            let (from, to) = match t.clone() {
                Type::Arrow(from, to) => {
                    let to = LLVMType::from_type(*to);
                    let from = match *from {
                        Type::Tuple(ts) => ts.iter().map(|t| LLVMType::from_type(t.clone())).collect(),
                        Type::Unit => vec![],
                        a => vec![LLVMType::from_type(a)]
                    };

                    (from, to)
                }
                _ => panic!()
            };

            extern_types.insert(f.clone(), (from, to));
        }


        LIRTree {
            external: self.external,
            extern_types,
            func_types,
            funcs: extracted_funcs,
            structs,
            enums,
            variants
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

    If(Box<LIRExpression>, Box<LIRExpression>, Box<LIRExpression>, LLVMType),

    List(Vec<LIRExpression>, LLVMType),

    // Constant Fields
    Num(u64),    // A Number Literal
    Str(String), // A String Literal, stores index into constant string array
    Unit,
    Tuple(Vec<LIRExpression>, LLVMType),

    GetTuple(Box<LIRExpression>, usize, LLVMType),
    CheckTuple(Box<LIRExpression>, usize, LLVMType),
    CastTuple(Box<LIRExpression>, String, LLVMType),

    Error(String)
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
            Self::GlobalCall(_, args, _) => {
                args.free_non_globals(vars)
            }
            Self::ExternCall(_, args, _) => {
                let mut free = vec![];
                for e in args {
                    free.extend(e.free_non_globals(vars))
                }
                free
            }
        }
    }

    fn extract_funcs(
        self,
        id: &String,
        types: &mut HashMap<String, (LLVMType, LLVMType)>,
        globals: &HashSet<String>,
        subs: &HashMap<String, LLVMType>
    ) -> (LIRExpression, HashMap<String, LIRExpression>,) {
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
                    _ => panic!()
                };

                // must modify function type to include closure variables
                let mut from = match *from {
                    LLVMType::Struct(a) => a,
                    LLVMType::Void => vec![],
                    a => vec![a]
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

                let (mut e, mut funcs) = body.extract_funcs(&crate::gen_var("lambda"), types, globals, subs);
                if argl == 1 && free.len() > 0 {
                    e = e.replace(
                        "arg.0",
                        LIRExpression::GetTuple(
                            Box::new(LIRExpression::Identifier(
                                "arg.0".to_string(),
                                LLVMType::Struct(from.clone())
                            )),
                            0,
                            from[0].clone()
                        )
                    );
                }


                // create let statements for formals
                for (i, (var, t)) in free.iter().enumerate() {
                    let et = e.ty();
                    let exp = LIRExpression::Let1(
                        var.clone(),
                        Box::new(
                            LIRExpression::GetTuple(
                                Box::new(LIRExpression::Identifier("arg.0".to_string(), LLVMType::Struct(from.clone()))),
                                argl+i,
                                t.clone()
                            )
                        ),
                        Box::new(e),
                        et
                    );
                    e = exp;
                }

                funcs.insert(id.clone(), e);


                types.insert(id.clone(), (LLVMType::Struct(from) , *to));

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
                    LLVMType::Struct(ts) => {
                        match &ts[0] {
                            LLVMType::Func(_, b) => b.clone(),
                            a => panic!("wha? {a:?} {e:?}")
                        }
                    }
                    a => panic!("{a:?}")
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
                (Self::Identifier(s, t), HashMap::new())
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

                (Self::List(newes, LLVMType::Struct(ts)), cs)
            }
            Self::GetTuple(tup, i, t) => {
                let (tup, cs) = tup.extract_funcs(id, types, globals, subs);
                (Self::GetTuple(Box::new(tup), i, t), cs)
            },
            Self::CheckTuple(tup, i, t) => {
                let (tup, cs) = tup.extract_funcs(id, types, globals, subs);
                (Self::CheckTuple(Box::new(tup), i, t), cs)
            },
            Self::CastTuple(tup, name, _) => {
                let (tup, cs) = tup.extract_funcs(id, types, globals, subs);
                let t = LLVMType::Named(name.clone());
                (Self::CastTuple(Box::new(tup), name, t), cs)
            },
            _ => (self, HashMap::new())
        }
    }

    pub fn ty(&self) -> LLVMType {
        match self {
            Self::GetTuple(_, _, t) => t.clone(),
            Self::Unit => LLVMType::Void,
            Self::Call(_, _, t) => t.clone(),
            Self::GlobalCall(_, _, t) => t.clone(),
            Self::Error(_) => LLVMType::Void,
            Self::Identifier(_, t) => t.clone(),
            Self::Lambda1(_, _, t) => t.clone(),
            Self::Str(..) => LLVMType::Ptr,
            Self::Let1(_, _, _, t) => t.clone(),
            Self::If(_, _, _, t) => t.clone(),
            Self::Num(_) => LLVMType::I32,
            Self::Tuple(_, t) => t.clone(),
            Self::List(_, t) => t.clone(),
            Self::CheckTuple(_, _, t) => t.clone(),
            Self::CastTuple(_, _, t) => t.clone(),
            Self::ExternCall(_, _, t) => t.clone()
        }
    }

    fn replace(self, id: &str, e: LIRExpression) -> Self {
        match self {
            Self::Identifier(n, t) => {
                if n==id {
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
            Self::CastTuple(tup, n, t) => {
                Self::CastTuple(Box::new(tup.replace(id, e)), n, t)
            }
            Self::CheckTuple(tup, i, t) => {
                Self::CheckTuple(Box::new(tup.replace(id, e)), i, t)
            }
            Self::GetTuple(tup, i, t) => {
                Self::GetTuple(Box::new(tup.replace(id, e)), i, t)
            }
            Self::GlobalCall(n, args, t) => {
                Self::GlobalCall(n, Box::new(args.replace(id, e)), t)
            }
            Self::If(cond, yes, no, t) => {
                let cond = Box::new(cond.replace(id, e.clone()));
                let yes = Box::new(yes.replace(id, e.clone()));
                let no = Box::new(no.replace(id, e));

                Self::If(cond, yes, no ,t)
            }
            Self::Lambda1(arg, body, t) => {
                Self::Lambda1(arg, Box::new(body.replace(id, e)), t)
            }
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
            a => a
        }
    }
}

impl MIRExpression {
    pub fn lower(
        self,
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        global: &HashSet<String>,
        externs: &HashSet<String>
    ) -> LIRExpression {
        match self {
            Self::Call(f, args, _, t) => {
                let f = f.lower(vars, global, externs);
                let args = args.lower(vars, global, externs);

                if let LIRExpression::Identifier(n, func_t) = &f {
                    if externs.contains(n) {
                        let args = match args {
                            LIRExpression::Unit => vec![],
                            LIRExpression::Tuple(es, _) => es,
                            a => vec![a]
                        };

                        return LIRExpression::ExternCall(n.clone(), args, LLVMType::from_type(t.unwrap()));
                    }

                    if global.contains(n) {
                        return LIRExpression::GlobalCall(n.clone(), Box::new(args), LLVMType::from_type(t.unwrap()))
                    }

                    if let Some((_, b)) = n.split_once(".") {
                        let out_t = match func_t {
                            LLVMType::Func(_, out) => match &**out {
                                LLVMType::Named(n) => n,
                                _ => panic!()
                            },
                            _ => panic!()
                        };

                        // this should mean we are calling a constructor on a enum type
                        return LIRExpression::GlobalCall(format!("{out_t}.{b}"), Box::new(args), LLVMType::from_type(t.unwrap()))
                    }
                }

                LIRExpression::Call(Box::new(f), Box::new(args), LLVMType::from_type(t.unwrap()))
            },
            Self::Str(s, _, _) => LIRExpression::Str(s),
            Self::Lambda1(arg, body, _, t) => {
                let (in_t, out_t) = match t.clone().unwrap() {
                    Type::Arrow(in_t, out_t) => (LLVMType::from_type(*in_t),LLVMType::from_type(*out_t)),
                    _ => panic!()
                };

                if let Some(arg) = arg {
                    LIRExpression::Lambda1(
                        Some(arg.clone()),
                        Box::new(LIRExpression::Let1(
                            arg, 
                            Box::new(LIRExpression::Identifier("arg.0".to_string(), in_t)),
                            Box::new(body.lower(vars, global, externs)), 
                            out_t
                        )),
                        LLVMType::from_type(t.unwrap())
                    )
                } else {
                    LIRExpression::Lambda1(
                        arg,
                        Box::new(body.lower(vars, global, externs)), 
                        LLVMType::from_type(t.unwrap())
                    )
                }

            }
            Self::Match(m, pats, _, t) => {
                if pats.len() == 1 {
                    // unit type always passes the pattern match
                    if let (Pattern::Unit(..), expr) = &pats[0] {
                        return expr.clone().lower(vars, global, externs);
                    }

                    // Single var pattern just becomes a let expression
                    if let (Pattern::Var(s, _, t2), expr) = &pats[0] {
                        return LIRExpression::Let1(s.clone(), Box::new(m.lower(vars, global, externs)), Box::new(expr.clone().lower(vars, global, externs)), LLVMType::from_type(t2.clone().unwrap()))
                    }

                }

                // transform if statements
                // TODO

                // General case
                if let Self::Identifier(n, _, _) = *m {
                    Self::match_code(n, &pats, LLVMType::from_type(t.unwrap()), vars, global, externs)
                } else {
                    let n = crate::gen_var("match");
                    LIRExpression::Let1(n.clone(), Box::new(m.lower(vars, global, externs)), Box::new(Self::match_code(n, &pats, LLVMType::from_type(t.clone().unwrap()), vars, global, externs)), LLVMType::from_type(t.unwrap()))
                }
            }
            Self::Identifier(s, _, t) => LIRExpression::Identifier(s, LLVMType::from_type(t.unwrap())),
            Self::Num(n, _, _) => LIRExpression::Num(n),
            Self::Tuple(es, _, t) => LIRExpression::Tuple(es.into_iter().map(|e| e.lower(vars, global, externs)).collect(), LLVMType::from_type(t.unwrap())),
            Self::List(es, _, t) => LIRExpression::List(es.into_iter().map(|e| e.lower(vars, global, externs)).collect(), LLVMType::from_type(t.unwrap())),
            Self::Unit(_, _) => LIRExpression::Unit,
            a => unimplemented!("{a:?}")
        }

    }

    fn match_code(
        x: String,
        pats: &[(Pattern, MIRExpression)],
        ty: LLVMType,
        vars: &HashMap<String, Vec<(String, LLVMType)>>,
        global: &HashSet<String>,
        externs: &HashSet<String>,
    ) -> LIRExpression {
        if pats.is_empty() {
            LIRExpression::Error("No patterns matched".to_string())
        } else {
            let fail = Self::match_code(x.clone(), &pats[1..], ty.clone(), vars, global, externs);
            let (pat, exp) = &pats[0];

            Self::match_pattern(
                pat.clone(),
                LIRExpression::Identifier(x, LLVMType::from_type(pat.ty())),
                exp.clone().lower(vars, global, externs),
                fail,
                ty,
                vars
            )
        }
    }

    fn match_pattern(pat: Pattern, exp: LIRExpression, yes: LIRExpression, no: LIRExpression, ty: LLVMType, vars: &HashMap<String, Vec<(String, LLVMType)>>) -> LIRExpression {
        match pat {
            Pattern::Unit(_, _) => {
                // since this passed type checking this always evaluates to true
                yes
            }
            Pattern::Num(n, _, _) => {
                LIRExpression::If(
                    Box::new(LIRExpression::Call(
                        Box::new(LIRExpression::Identifier(
                            "eq".into(),
                            LLVMType::Func(
                                Box::new(LLVMType::Struct(vec![LLVMType::I32, LLVMType::I32])),
                                Box::new(LLVMType::I1)
                            )
                        )), 
                        Box::new(LIRExpression::Tuple(vec![
                            exp,
                            LIRExpression::Num(n),
                        ], LLVMType::Struct(vec![LLVMType::I32, LLVMType::I32]))),
                        LLVMType::I1
                    )),
                    Box::new(yes),
                    Box::new(no),
                    ty
                )
            },
            Pattern::Var(x, _, t) => {
                LIRExpression::Let1(x, Box::new(exp), Box::new(yes), LLVMType::from_type(t.unwrap()))
            }
            Pattern::Tuple(ps, _, _) => {
                // due to type checking this is already guaranteed to be a tuple, so instead we
                // just verify/gen ir for the components
                Self::match_components(&ps, 0, exp, yes, no, vars)
            }
            Pattern::Cons(n, args, _, t) => {
                let t = t.unwrap();
                if let Some((_, b)) = n.split_once(".") {
                    let (enum_id, (_, enum_t)) = vars[&t.to_string()].iter().enumerate()
                        .find(|s| s.1.0 == format!("{}.{b}", t.to_string()))
                        .unwrap();

                    let ps = match *args {
                        Pattern::Tuple(ps, _, _) => ps,
                        _ => vec![*args]
                    };

                    let v = crate::gen_var("f");

                    LIRExpression::If(
                        Box::new(LIRExpression::CheckTuple(Box::new(exp.clone()), enum_id, LLVMType::I1)),
                        Box::new(LIRExpression::Let1(
                            v.clone(),
                            Box::new(LIRExpression::CastTuple(
                                Box::new(exp),
                                format!("{}.{b}", t.to_string()),
                                enum_t.clone(),
                            )),
                            Box::new(Self::match_components(
                                &ps,
                                1,
                                LIRExpression::Identifier(
                                    v.clone(),
                                    enum_t.clone()
                                ),
                                yes.clone(),
                                no.clone(),
                                vars
                            )),
                            ty.clone()
                        )),
                        Box::new(no),
                        ty
                    )
                } else {
                    Self::match_pattern(*args, exp, yes, no, ty, vars)
                }
            }
            a => unimplemented!("{a:?}")
        }
    }

    fn match_components(ps: &[Pattern], n: usize, exp: LIRExpression, yes: LIRExpression, no: LIRExpression, vars: &HashMap<String, Vec<(String, LLVMType)>>) -> LIRExpression {
        if ps.is_empty() {
            yes
        } else {
            let p = &ps[0];
            let rest = Self::match_components(&ps[1..], n+1, exp.clone(), yes, no.clone(), vars);

            Self::match_pattern(
                p.clone(),
                LIRExpression::GetTuple(Box::new(exp.clone()), n, LLVMType::from_type(p.ty())),
                rest,
                no,
                exp.ty(),
                vars
            )
        }
    }
}


