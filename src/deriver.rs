use std::{
    collections::{HashMap, HashSet},
    error,
    fmt::{self},
    hash::Hash,
    rc::Rc,
};
use thiserror::Error;

use crate::{
    expr::{fmt_context, identifier_names, Context, Expr},
    parser::parse_judgement,
};

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Rule {
    Sort,
    Var,
    Weak,
    Form(Rc<Expr>, Rc<Expr>),
    Appl,
    Abst,
    // Conv,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Use `self.number` to refer to each positional data point.
        // write!(f, "({}, {})", self.0, self.1)
        let s = match self {
            // Rule::Var => " (var)".to_string(),
            Self::Form(s1, s2) => format!("(form ({s1},{s2}))"),
            _ => format!("({self:?})").to_lowercase(),
        };
        write!(f, "{s}")
    }
}

// type DerivationCache = HashMap<>

#[derive(PartialEq, Debug, Clone)]
struct Derivation {
    conclusion: Expr,
    rule: Rule,
    premiss_one: Option<Rc<Result<Derivation, DeriveError>>>,
    premiss_two: Option<Rc<Result<Derivation, DeriveError>>>,
}

#[derive(Hash, Debug, Error, PartialEq, Eq, Clone)]
pub enum DeriveError {
    #[error("Derivation not implemented for judgement {0}.")]
    NotImplemented(Rc<Expr>),

    #[error("Unexpected type {0} in judgement {1}.\nThe type of a Pi abstraction must be a sort (either ∗ or □).")]
    UnexpectedPiAbstractionType(Rc<Expr>, Rc<Expr>),

    #[error("Can't infer identifier {0} in context {}.", fmt_context(.1))]
    InferIdentifier(Rc<Expr>, Context),

    #[error("Can't infer the type of □.")]
    InferBox,

    #[error("Unexpected type in application {0} in context {}.\nExpected {1} to be a Pi abstraction but found {1} : {2}.", fmt_context(.3))]
    InferApplicationLHS(Rc<Expr>, Rc<Expr>, Rc<Expr>, Context),

    #[error("Unexpected type in application {0} in context {}.\nExpected {1} : {2}, but found {1} : {3}.", fmt_context(.4))]
    InferApplicationRHS(Rc<Expr>, Rc<Expr>, Rc<Expr>, Rc<Expr>, Context),

    #[error(
        "Form rule inferred (s1,s2) = ({0},{1}), \nbut s1 and s2 can only be sorts (either ∗ or □)."
    )]
    InferForm(Rc<Expr>, Rc<Expr>),

    #[error("Inferred type for judgement {0} was {2}, but {2} ≠ {1}.")]
    InferJudgement(Rc<Expr>, Rc<Expr>, Rc<Expr>),

    #[error("infer error")]
    InferError,
}

fn append_to_context(ident: Rc<Expr>, etype: Rc<Expr>, context: &Context) -> Context {
    let fv = Expr::FreeVariable { ident, etype };
    context
        .iter()
        .cloned()
        .chain(std::iter::once(fv.into()))
        .collect()
}

// fn determine_sort(expr: Expr, context: Context) -> Expr {
//     match expr {
//         Expr::Star => Expr::Box,
//         _ => Expr::Star, // this is most likely wrong
//     }
// }

fn find_type_in_context(ident: &Expr, context: &Context) -> Option<Rc<Expr>> {
    for expr in context {
        if let Expr::FreeVariable { ident: fv, etype } = expr.as_ref() {
            if ident == fv.as_ref() {
                return Some(etype.clone());
            }
        }
    }
    None
}

fn infer_type(context: &Context, expr: Rc<Expr>) -> Result<Rc<Expr>, DeriveError> {
    match expr.as_ref() {
        Expr::Identifier(_) => find_type_in_context(&expr, context)
            .ok_or_else(|| DeriveError::InferIdentifier(expr, context.clone())),
        Expr::Star => Ok(Rc::new(Expr::Box)),
        Expr::Box => Err(DeriveError::InferBox),
        Expr::Bottom => todo!(),
        Expr::Application { lhs, rhs } => match infer_type(context, lhs.clone()) {
            Ok(lhs_type) => match lhs_type.as_ref() {
                Expr::PiAbstraction {
                    ident,
                    etype: type_of_rhs,
                    body,
                } => {
                    let inferred_type_of_rhs = infer_type(context, rhs.clone())?;
                    if type_of_rhs.clone() != inferred_type_of_rhs {
                        let rc = Err(DeriveError::InferApplicationRHS(
                            expr.clone(),
                            rhs.clone(),
                            type_of_rhs.clone(),
                            inferred_type_of_rhs,
                            context.clone(),
                        ));
                        return rc;
                    };
                    let new_body = ident
                        .as_ref()
                        .map_or_else(|| body.clone(), |i| substitute(&body, &i, rhs));
                    Ok(new_body)
                }
                _ => Err(DeriveError::InferApplicationLHS(
                    expr.clone(),
                    lhs.clone(),
                    lhs_type,
                    context.clone(),
                )),
            },
            Err(err) => Err(err),
        },
        Expr::LambdaAbstraction { ident, etype, body } => {
            let new_context = append_to_context(ident.clone(), etype.clone(), context);
            match infer_type(&new_context, body.clone()) {
                Ok(body) => Ok(Rc::new(Expr::new_pi(ident, etype.clone(), &body))),

                err => err,
            }
        }
        Expr::PiAbstraction { ident, etype, body } => {
            let new_context = ident.as_ref().map_or_else(
                || context.clone(),
                |ident| append_to_context(ident.clone(), etype.clone(), context),
            );
            infer_type(&new_context, body.clone())
        }
        _ => unreachable!(),
    }
}

fn all_except_last(context: &Context) -> Context {
    if context.is_empty() {
        vec![]
    } else {
        context[..context.len() - 1].to_vec()
    }
}

// #[test]
// fn test_all_except_last() {
//     let x = vec![Expr::Box, Expr::Star, Expr::Identifier("a".to_string())];
//     assert_eq!(all_except_last(x), vec![Expr::Box, &Expr::Star]);

//     let x: Context = vec![];
//     assert_eq!(all_except_last(x), vec![]);
// }

fn derive(judgement: Rc<Expr>) -> Result<Derivation, DeriveError> {
    let global_ident_names = identifier_names(&judgement);

    let judgement = match judgement.as_ref() {
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            if **etype == Expr::Infer {
                let inferred_type = infer_type(context, expr.clone())?;
                Expr::Judgement {
                    context: context.clone(),
                    expr: expr.clone(),
                    etype: inferred_type,
                }
                .into()
            } else {
                judgement
            }
        }
        _ => unreachable!(),
    };

    derive_h(judgement, &global_ident_names)
}

fn derive_h(
    judgement: Rc<Expr>,
    global_ident_names: &HashSet<String>,
) -> Result<Derivation, DeriveError> {
    match (*judgement).clone() {
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            let inferred_type = infer_type(&context, expr.clone())?;
            if etype != inferred_type {
                return Err(DeriveError::InferJudgement(judgement, etype, inferred_type));
            }

            // let context = context.as_slice();
            let judgement_expr = expr;
            let judgement_type = etype;

            // Sort
            if let ([], Expr::Star, Expr::Box) = (
                context.as_slice(),
                judgement_expr.as_ref(),
                judgement_type.as_ref(),
            ) {
                return Ok(Derivation {
                    rule: Rule::Sort,
                    conclusion: Expr::Judgement {
                        context: context.clone(),
                        expr: (judgement_expr),
                        etype: (judgement_type),
                    },
                    premiss_one: None,
                    premiss_two: None,
                });
            }

            // Example usage
            if let Some(expr) = context.last() {
                match &**expr {
                    Expr::FreeVariable {
                        ident,
                        etype: ident_type,
                    } => {
                        // (Some(*ident.clone()), Some(*etype.clone()))
                        // println!("{ident:?}, {expr:?}, {ident_type:?}, {etype:?}");
                        let last_fv = ident;
                        let last_fv_type = ident_type;
                        let new_context = all_except_last(&context);

                        // println!(
                        //     "\n{:?}\n{:?}\n{:?}\n{:?}\n",
                        //     last_fv, judgement_expr, last_fv_type, judgement_type
                        // );
                        // Var rule
                        if *last_fv == judgement_expr && *last_fv_type == judgement_type {
                            // TODO x \not\in\ context
                            let aa = infer_type(&context, last_fv_type.clone());
                            let p1 = match aa {
                                Ok(t) => Some(Rc::new(derive_h(
                                    Expr::Judgement {
                                        context: new_context,
                                        expr: (last_fv_type.clone()),
                                        etype: (t),
                                    }
                                    .into(),
                                    global_ident_names,
                                ))),
                                Err(e) => Some(Rc::new(Err(e))),
                            };

                            return Ok(Derivation {
                                rule: Rule::Var,
                                conclusion: Expr::Judgement {
                                    context: context.clone(),
                                    expr: (judgement_expr),
                                    etype: (judgement_type),
                                },
                                premiss_one: p1,
                                premiss_two: None,
                            });
                        }

                        match *judgement_expr {
                            Expr::Identifier(_) | Expr::Star => {
                                let conclusion = Expr::Judgement {
                                    context: context.clone(),
                                    expr: (judgement_expr.clone()),
                                    etype: (judgement_type.clone()),
                                };

                                let premiss_one = Some(Rc::new(derive_h(
                                    Expr::Judgement {
                                        context: new_context.clone(),
                                        expr: (judgement_expr.clone()),
                                        etype: (judgement_type),
                                    }
                                    .into(),
                                    global_ident_names,
                                )));

                                let premiss_two = match infer_type(&context, last_fv_type.clone()) {
                                    Ok(t) => Some(Rc::new(derive_h(
                                        Expr::Judgement {
                                            context: new_context,
                                            expr: (last_fv_type.clone()),
                                            etype: (t),
                                        }
                                        .into(),
                                        global_ident_names,
                                    ))),
                                    Err(e) => Some(Rc::new(Err(e))),
                                };

                                return Ok(Derivation {
                                    rule: Rule::Weak,
                                    conclusion,
                                    premiss_one,
                                    premiss_two,
                                });
                            }
                            _ => (),
                        }
                    }
                    _ => unreachable!(),
                }
            };

            // Form rule
            if let Expr::PiAbstraction {
                ident: pi_ident,
                etype: pi_type,
                body: pi_body,
            } = judgement_expr.as_ref()
            {
                if *judgement_type != Expr::Star && *judgement_type != Expr::Box {
                    return Err(DeriveError::UnexpectedPiAbstractionType(
                        judgement_type,
                        judgement,
                    ));
                }
                let p1_type = infer_type(&context, pi_type.clone());

                let premiss_one = match p1_type.clone() {
                    Ok(t) => Some(Rc::new(derive_h(
                        Expr::Judgement {
                            context: context.clone(),
                            expr: pi_type.clone(),
                            etype: (t),
                        }
                        .into(),
                        global_ident_names,
                    ))),
                    Err(e) => Some(Rc::new(Err(e))),
                };

                let pi_ident = pi_ident.as_ref().map_or_else(
                    || {
                        let new_ident_name = new_ident_name(&judgement, global_ident_names);
                        Expr::Identifier(new_ident_name).into()
                    },
                    std::clone::Clone::clone,
                );

                let premiss_two = Some(Rc::new(derive_h(
                    Expr::Judgement {
                        context: append_to_context(pi_ident, pi_type.clone(), &context),
                        expr: pi_body.clone(),
                        etype: (judgement_type.clone()),
                    }
                    .into(),
                    global_ident_names,
                )));
                let s2 = judgement_type.clone();

                match p1_type {
                    Ok(s1) => match (s1.as_ref(), s2.as_ref()) {
                        (Expr::Star | Expr::Box, Expr::Star | Expr::Box) => {
                            return Ok(Derivation {
                                rule: Rule::Form(s1, s2),
                                conclusion: Expr::Judgement {
                                    context,
                                    expr: (judgement_expr),
                                    etype: (judgement_type),
                                },
                                premiss_one,
                                premiss_two,
                            })
                        }
                        (_, _) => return Err(DeriveError::InferForm(s1, s2)),
                    },
                    Err(e) => return Err(e),
                }
            }

            // Appl
            if let Expr::Application { lhs, rhs } = judgement_expr.as_ref() {
                let p1_type = infer_type(&context, lhs.clone());
                let p2_type = infer_type(&context, rhs.clone());

                let p1 = Some(match p1_type {
                    Ok(p1_type) => Rc::new(derive_h(
                        Expr::Judgement {
                            context: context.clone(),
                            expr: lhs.clone(),
                            etype: (p1_type),
                        }
                        .into(),
                        global_ident_names,
                    )),
                    Err(err) => Err(err).into(),
                });

                let p2 = Some(match p2_type {
                    Ok(p2_type) => Rc::new(derive_h(
                        Expr::Judgement {
                            context: context.clone(),
                            expr: rhs.clone(),
                            etype: (p2_type),
                        }
                        .into(),
                        global_ident_names,
                    )),
                    Err(err) => Err(err).into(),
                });

                return Ok(Derivation {
                    rule: Rule::Appl,
                    conclusion: Expr::Judgement {
                        context,
                        expr: (judgement_expr),
                        etype: (judgement_type),
                    },
                    premiss_one: p1,
                    premiss_two: p2,
                });
            }

            if let Expr::LambdaAbstraction {
                ident: lambda_ident,
                etype: lambda_ident_type,
                body: lambda_body,
            } = judgement_expr.as_ref()
            {
                let p1_body = lambda_body;
                let p1_type = match judgement_type.as_ref() {
                    Expr::PiAbstraction {
                        ident: _,
                        etype: _,
                        body,
                    } => Ok(body),
                    _ => Err(DeriveError::InferError),
                }?;
                let p1_new_fv = lambda_ident;
                let p1_new_fv_type = lambda_ident_type;
                let p1_new_context =
                    append_to_context(p1_new_fv.clone(), p1_new_fv_type.clone(), &context);
                let p1 = Some(Rc::new(derive_h(
                    Expr::Judgement {
                        context: p1_new_context,
                        expr: p1_body.clone(),
                        etype: p1_type.clone(),
                    }
                    .into(),
                    global_ident_names,
                )));

                let s = (infer_type(&context, judgement_type.clone()))?;
                let p2 = Some(Rc::new(derive_h(
                    Expr::Judgement {
                        context: context.clone(),
                        expr: judgement_type.clone(),
                        etype: s,
                    }
                    .into(),
                    global_ident_names,
                )));

                return Ok(Derivation {
                    rule: Rule::Abst,
                    conclusion: Expr::Judgement {
                        context,
                        expr: (judgement_expr),
                        etype: (judgement_type),
                    },
                    premiss_one: p1,
                    premiss_two: p2,
                });
            }

            Err(DeriveError::NotImplemented(judgement))
            // panic!(
            //     "ctx:  {:?}\nexpr: {:?}\ntype: {:?}",
            //     context, judgement_expr, judgement_type
            // )
        }
        _ => unreachable!(),
    }
}

// #[test]
// fn sort() {
//     let e = parser::parse_judgement("C |- * : #").unwrap();
//     assert_eq!("[0] Γ ⊢ ∗ : □        (Sort)", stringify(derive(e).unwrap()));
// }

// #[test]
// fn var() {
//     let e = parser::parse_judgement("C, A: *, x: A |- x : A").unwrap();

//     let r = stringify(derive(e).unwrap());
//     println!("{r}");
//     assert_eq!(r, "[0] A : ∗, x : A ⊢ x : A     (Var) on [1]\n[1] A : ∗ ⊢ A : ∗            (Var) on [2]\n[2] Γ ⊢ ∗ : □                (Sort)\n\n");

//     // let e = parser::parse_judgement("C, x: A -> B -> C |- x : A -> B -> C").unwrap();
// }

// #[test]
// fn form() {
//     let e = parser::parse_judgement("a: *, b:* |- a -> b : *").unwrap();
//     let e = parser::parse_judgement("{} |- /a: * . a : *").unwrap();
//     let e = parser::parse_judgement("{} |- (/a: * . a) -> (/b:*.b) : *").unwrap();
//     let r = stringify(derive(e).unwrap());
//     println!("{r}");
//     assert_eq!(r, "[0] A : ∗, x : A ⊢ x : A     (Var) on [1]\n[1] A : ∗ ⊢ A : ∗            (Var) on [2]\n[2] Γ ⊢ ∗ : □                (Sort)\n\n");
// }

// #[test]
// fn moo() {
//     let x = derivation("{} |- \\a:*. a : *");
//     assert_eq!("", x);
// }

// fn stringify(derivation: Derivation) -> String {
//     stringify_h(derivation, 0, 0).1
// }

// fn stringify_h(derivation: Derivation, counter: u32, width: usize) -> (u32, String) {
//     let conclusion = parser::stringify(derivation.conclusion.clone());
//     let counter = counter + 1;

//     let width = width.max(conclusion.len());
//     // println!("{} {}", width, conclusion.len());
//     match (derivation.premiss_one, derivation.premiss_two) {
//         (Some(p1), Some(p2)) => {
//             let (p1_counter, p1s) = stringify_h(*(p1.clone()), counter, width);
//             let (p2_counter, p2s) = stringify_h(*p2, p1_counter, width);
//             let rule = match derivation.rule {
//                 Rule::Form(_, _) => {
//                     format!("{}", derivation.rule)
//                 }
//                 rule => format!("{}", rule),
//             };
//             (
//                 p2_counter,
//                 format!(
//                     "{:>5} {:width$} ({}) on [{}] and [{}]\n{}\n{}\n",
//                     format!("[{counter}]"),
//                     conclusion,
//                     rule,
//                     counter + 1,
//                     p1_counter + 1,
//                     p1s,
//                     p2s,
//                 ),
//             )
//         }
//         (Some(p1), None) => {
//             let (p1_counter, p1s) = stringify_h(*p1, counter, width);
//             (
//                 p1_counter,
//                 format!(
//                     "{:>5} {:width$} {} on [{}]\n{}\n",
//                     format!("[{counter}]"),
//                     conclusion,
//                     derivation.rule,
//                     counter + 1,
//                     p1s,
//                 ),
//             )
//         }
//         _ => (
//             counter,
//             // "".to_string(),
//             format!(
//                 "{:>5} {:width$} ({})",
//                 format!("[{counter}]"),
//                 conclusion,
//                 derivation.rule,
//             ),
//         ),
//     }
// }
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum RuleRef {
    None(Rule),
    One(Rule, i32),
    Two(Rule, i32, i32),
}

impl fmt::Display for RuleRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Self::None(r) => format!("{r}"),
            Self::One(r, p1) => format!("{r} on [{p1}]"),
            Self::Two(r, p1, p2) => format!("{r} on [{p1}] and [{p2}]"),
        };
        write!(f, "{s}")
    }
}

type DerivationCache = HashMap<CacheEntry, (i32, Option<RuleRef>)>;

#[derive(Hash, PartialEq, Eq, Debug, Clone)]
pub enum CacheEntry {
    Expr(Expr),
    DeriveError(DeriveError),
}

// impl CacheEntry {
//     fn new()
// }

fn deduplicate(
    d: Result<Derivation, DeriveError>,
) -> Vec<(CacheEntry, (i32, std::option::Option<RuleRef>))> {
    let mut cache: DerivationCache = HashMap::new();

    deduplicate_h(&d.into(), &mut cache, &mut 0);

    // println!("{cache:?}");
    // println!("{:?}", cache.values());
    let mut s = cache.drain().collect::<Vec<_>>();

    s.sort_unstable_by(|(_, v1), (_, v2)| v1.0.cmp(&v2.0));
    s
    // s.iter()
    //     .map(|(k, v)| format!("{} {:?}", parser::stringify(k.clone()), v))
    //     .collect::<Vec<_>>()
    //     .join("\n")
}

#[test]
fn dedup() {
    let e = crate::parser::parse_judgement("a: *, b:*,c:*,d:* |- a -> b -> c->d : *").unwrap();
    let d = derive(e.into());
    let s = deduplicate(d);
    println!("{s:?}");
    // panic!();
}

fn deduplicate_h(
    d: &Rc<Result<Derivation, DeriveError>>,
    c: &mut DerivationCache,
    id: &mut i32,
) -> i32 {
    match d.as_ref() {
        Ok(d) => {
            let e = CacheEntry::Expr(d.conclusion.clone());
            c.entry(e).or_insert_with(|| {
                let x = *id;
                *id += 1;
                (x, None)
            });
            let rule_ref = match (d.premiss_one.clone(), d.premiss_two.clone()) {
                (Some(p1), Some(p2)) => {
                    let p1_id = deduplicate_h(&p1, c, id);
                    let p2_id = deduplicate_h(&p2, c, id);
                    Some(RuleRef::Two(d.rule.clone(), p1_id, p2_id))
                }
                (Some(p1), None) => {
                    let p1_id = deduplicate_h(&p1, c, id);
                    Some(RuleRef::One(d.rule.clone(), p1_id))
                }
                _ => Some(RuleRef::None(d.rule.clone())),
            };

            if let Some(k) = c.get_mut(&CacheEntry::Expr(d.conclusion.clone())) {
                k.1 = rule_ref;
                return k.0;
            }
            unreachable!()
        }
        Err(e) => {
            let e = CacheEntry::DeriveError((*e).clone());
            let x = c.entry(e).or_insert_with(|| {
                let x = *id;
                *id += 1;
                (x, None)
            });
            x.0
        }
    }
}

// pub fn derivation(s: &str) -> String {
//     match parser::parse_judgement(s) {
//         Ok(j) => match derive(j) {
//             Ok(d) => stringify(d),
//             Err(e) => format!("{}", e),
//         },
//         Err(e) => format!("{}", e),
//     }
// }
pub type DedupedDerivation = Vec<(CacheEntry, (i32, Option<RuleRef>))>;
pub type DedupedDerivationResult = Result<DedupedDerivation, Box<dyn error::Error>>;

pub fn derivation(s: &str) -> DedupedDerivationResult {
    let j = parse_judgement(s)?;
    let d = derive(j.into());
    let nodes = deduplicate(d);
    Ok(nodes)
}

pub fn derivation_dot(d: &DedupedDerivationResult) -> String {
    let base_fontsize = 20;
    match d {
        Ok(d) => {
            let nodes = d.iter()
                .map(|(k, (id, ruleref))| match k {
                    CacheEntry::Expr(e) => {
                        let (rulename, refs) = match ruleref {
                            Some(r) => match r {
                                RuleRef::None(r) => (r, String::new()),
                                RuleRef::One(r, ref1) => (r, format!("{ref1} -> {id} [labeldistance=2 headlabel=\"1\"];" )),
                                RuleRef::Two(r, ref1, ref2) => {
                                    (r, format!("{ref1} -> {id} [labeldistance=2 headlabel=\"1\"];\n{ref2} -> {id} [labeldistance=2 headlabel=\"2\"];"))
                                }
                            },
                            None => todo!(),
                        };
                        let (style,size_normal, size_big) = match rulename {
                            Rule::Var |Rule::Weak=> ("dotted".to_string(), base_fontsize-4, base_fontsize),
                            _ => (String::new(), base_fontsize+4, base_fontsize+10)
                        };
                        match e {
                            Expr::Judgement {
                                context,
                                expr,
                                etype,
                            } => {
                                format!(
                                    "{} [label=<{{{}<br/>⊤<br/><font point-size=\"{}\">{}</font><br/>··<br/>{}|<font face=\"DejaVuSerif\" point-size=\"{}\"><i>{}</i></font>}}> style=\"{}\" fontsize={}];\n{}",
                                    id,
                                    fmt_context(context),
                                    size_big,
                                    expr,
                                    etype,
                                    base_fontsize-6,
                                    rulename,
                                    style,
                                    size_normal,
                                    refs
                                )
                            }
                            _ => unreachable!(),
                        }
                    }
                    CacheEntry::DeriveError(e) => {
                        let e = format!("{e}").replace("\n", "\\n");
                        format!("{id} [label=\"{}\" fillcolor=\"#ff000030\" margin=\"1.0\" fontsize={} style=\"filled\"]\n;", e, base_fontsize+10 )
                    }
                })
                .collect::<Vec<_>>()
                .join("\n");
            format!("digraph derivation_tree {{\n\nrankdir=BT\nedge [fontsize={base_fontsize} fontname=\"Euler Math\"]\nnode [fontname=\"Euler Math\" shape=Mrecord, style=rounded]\n{nodes}\n}}")
        }
        Err(e) => format!("{e}"),
    }
}

pub fn derivation_html(d: &DedupedDerivationResult) -> String {
    match d {
        Ok(d) => d
            .iter()
            .map(|(k, (id, rule))| match k {
                CacheEntry::Expr(e) => {
                    format!(
                        r#"<span class="id">[{}]</span> {} <span class="rule">{}</span>"#,
                        id,
                        crate::expr::htmlify(e),
                        rule.as_ref().expect("unreachable")
                    )
                }
                CacheEntry::DeriveError(e) => {
                    format!(r#"<span class="id">[{id}]</span> <code class="error">{e}</code>"#)
                }
            })
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => format!("<code>{e}</code>"),
    }
}

#[test]
fn derive_html() {
    let s ="a:*,b:*,S : ∗, Q : S → S → ∗ |- (Πx:S. /y : S . (Q x y → Q y x → (/a:*.a))) → Πz : S . (Q z z → (/b:*.b)) : *";
    let _d = derivation(s);
    let _d = derivation(s);
    let _d = derivation(s);
    let _d = derivation(s);
    // derivation_html(&d);
}

fn substitute(expr: &Rc<Expr>, target: &Rc<Expr>, replacement: &Rc<Expr>) -> Rc<Expr> {
    let target_name = match target.as_ref() {
        Expr::Identifier(x) => x,
        _ => unreachable!(),
    };
    match expr.as_ref() {
        Expr::Identifier(name) if name == target_name => replacement.clone(),
        Expr::Application { lhs, rhs } => Rc::new(Expr::Application {
            lhs: substitute(lhs, target, replacement),
            rhs: substitute(rhs, target, replacement),
        }),
        Expr::LambdaAbstraction { ident, etype, body } => Rc::new(Expr::LambdaAbstraction {
            ident: ident.clone(),
            etype: substitute(etype, target, replacement),
            body: substitute(body, target, replacement),
        }),
        Expr::PiAbstraction { ident, etype, body } => Rc::new(Expr::PiAbstraction {
            ident: ident.clone(),
            etype: substitute(etype, target, replacement),
            body: substitute(body, target, replacement),
        }),
        Expr::FreeVariable { ident: _, etype: _ }
        | Expr::Judgement {
            context: _,
            expr: _,
            etype: _,
        } => unreachable!(),
        _ => expr.clone(),
    }
}

#[test]
fn subst() {
    let s = "S : ∗, P : S → ∗, A : ∗ |- (Πx : S . (A → P x)) → A → Πy : S . P y : *";
    // let s = "S : ∗, P : S → ∗, A : ∗ |- (Πx : S . (A → P x)) → A → Πy : S . P y : *";
    let j = crate::parser::parse_judgement(s).unwrap();
    let mut ns = identifier_names(&Rc::new(j));
    let mut ns = ns.drain().collect::<Vec<_>>();
    ns.sort();
    assert_eq!(ns, vec!["A", "P", "S", "x", "y"]);
}

fn new_ident_name(expr: &Rc<Expr>, global_ident_names: &HashSet<String>) -> String {
    let local_ident_names = identifier_names(expr);
    let ident_names: HashSet<_> = local_ident_names.union(global_ident_names).collect();
    let ranges = vec!['x'..='z', 'u'..='w', 'p'..='t', 'a'..='z'];
    for range in ranges {
        for c in range {
            let new_char = c.to_string();
            if !ident_names.contains(&new_char) {
                return new_char;
            }
        }
    }

    panic!()
}

#[test]
fn ident_name() {
    let _s = "a:*,b:*,x:*,y:*,z:*|-a:*";

    let s = "S : ∗, P : S → ∗, A : ∗ |- (Πx : S . (A → P x)) → A → Πy : S . P y : *";
    let j = crate::parser::parse_judgement(s).unwrap();
    // let ns = identifier_names(Rc::new(j));
    let new_i = new_ident_name(&Rc::new(j), &HashSet::new());
    assert_eq!(new_i, "z");
    // let mut ns = ns.drain().collect::<Vec<_>>();
    // ns.sort();
    // assert_eq!(ns, vec!["A", "P", "S", "x", "y"]);
}

// a:*,b:*,m:a->b,n:a |- m n : b
// S : ∗, P : S → ∗, A : ∗ |- (Πx : S . (A → P x)) → A → Πy : S . P y : *
// S : ∗, Q : S → S → ∗ |- (Πx:S. /y : S . (Q x y → Q y x → (/a:*.a))) → Πz : S . (Q z z → (/b:*.b)) : *
// b:* |- (\a:b.a a) : (/a:b.b)    cant infer a
// a:*,b:*,x:a,y:a->b |- (\x:c.(y x)) :b   TODO sanity check (lambda using x as free variable)
// a:*,b:a->*,m:(/x:a.b x),n:a |- m n : ?
// S : ∗, Q : S → S → ∗ ⊢ λz : (Πx : S . Πy : S . Q x y) . λu : S . z u u : ?
// a:*,b:*,n:b,m:a->b|-m n:? fail
