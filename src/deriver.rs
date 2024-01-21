use std::fmt::format;

use crate::parser::{self, Expr};

#[derive(PartialEq, Debug)]
enum DRule {
    Sort,
    Var,
    Weak,
    Form,
    Appl,
    Abst,
    Conv,
}

#[derive(PartialEq, Debug)]
struct DStep {
    conclusion: Expr,
    rule: DRule,
    premiss_one: Option<Box<DStep>>,
    premiss_two: Option<Box<DStep>>,
}

pub fn derive(e: Expr) {
    todo!()
}

fn append_to_context(ident: Expr, etype: Expr, context: Vec<Expr>) -> Vec<Expr> {
    let fv = Expr::FreeVariable {
        ident: Box::new(ident),
        etype: Box::new(etype),
    };
    context.iter().cloned().chain(std::iter::once(fv)).collect()
}

fn determine_sort(expr: Expr, context: Vec<Expr>) -> Expr {
    match expr {
        Expr::Star => Expr::Box,
        _ => Expr::Star, // this is most likely wrong

                         // Expr::Identifier(_) => todo!(),
                         // Expr::Box => todo!(),
                         // Expr::Bottom => todo!(),
                         // Expr::Application { lhs, rhs } => todo!(),
                         // Expr::LambdaAbstraction { ident, etype, body } => todo!(),
                         // Expr::PiAbstraction { ident, etype, body } => todo!(),
                         // Expr::FreeVariable { ident, etype } => todo!(),
                         // Expr::Judgement {
                         //     context,
                         //     expr,
                         //     etype,
                         // } => todo!(),
    }
}

fn find_type_in_context(ident: Expr, context: Vec<Expr>) -> Option<Expr> {
    for expr in context {
        match expr {
            Expr::FreeVariable { ident: fv, etype } => {
                if ident == *fv {
                    return Some(*etype);
                }
            }
            _ => (),
        }
    }
    None
}

fn all_except_last<Expr: std::clone::Clone>(context: Vec<Expr>) -> Vec<Expr> {
    if context.len() > 0 {
        context[..context.len() - 1].to_vec()
    } else {
        vec![]
    }
}

#[test]
fn test_all_except_last() {
    let x = vec![Expr::Box, Expr::Star, Expr::Identifier("a".to_string())];
    assert_eq!(all_except_last(x), vec![Expr::Box, Expr::Star]);

    let x: Vec<Expr> = vec![];
    assert_eq!(all_except_last(x), vec![]);
}

fn step(judgement: Expr) -> DStep {
    match judgement {
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            let context = context.as_slice();
            let judgement_expr = *expr;
            let judgement_type = *etype;

            if let ([], Expr::Star, Expr::Box) = (context, &judgement_expr, &judgement_type) {
                return DStep {
                    rule: DRule::Sort,
                    conclusion: Expr::Judgement {
                        context: context.to_vec(),
                        expr: Box::new(judgement_expr),
                        etype: Box::new(judgement_type),
                    },
                    premiss_one: None,
                    premiss_two: None,
                };
            }

            match context.last() {
                Some(Expr::FreeVariable {
                    ident,
                    etype: ident_type,
                }) => {
                    // (Some(*ident.clone()), Some(*etype.clone()))
                    // println!("{ident:?}, {expr:?}, {ident_type:?}, {etype:?}");
                    let last_fv = *ident.clone();
                    let last_fv_type = *ident_type.clone();
                    let new_context = all_except_last(context.to_vec());

                    // Var rule
                    if last_fv == judgement_expr && last_fv_type == judgement_type {
                        // let ident_type_sort = match ident_type {
                        //     Expr::Star => Expr::Box,
                        //     Expr::Identifier(_) => {
                        //         // TODO could this possibly lead to s \not\in {*, #} ? (illegal for var rule)
                        //         find_type_in_context(ident_type.clone(), context.to_vec())
                        //             .expect(&format!("not in context: {ident_type:?}"))
                        //     }

                        //     ref x => panic!("ident_type_sort: {:?}", ident_type),
                        // };

                        // TODO x \not\in\ context
                        return DStep {
                            rule: DRule::Var,
                            conclusion: Expr::Judgement {
                                context: context.to_vec(),
                                expr: Box::new(judgement_expr),
                                etype: Box::new(judgement_type),
                            },
                            premiss_one: Some(Box::new(step(Expr::Judgement {
                                context: new_context,
                                expr: Box::new(last_fv_type.clone()),
                                etype: Box::new(determine_sort(last_fv_type, context.to_vec())),
                            }))),
                            premiss_two: None,
                        };
                    }

                    match judgement_expr {
                        Expr::Identifier(_) | Expr::Star => {
                            let conclusion = Expr::Judgement {
                                context: context.to_vec(),
                                expr: Box::new(judgement_expr.clone()),
                                etype: Box::new(judgement_type.clone()),
                            };

                            let premiss_one = Some(Box::new(step(Expr::Judgement {
                                context: new_context.clone(),
                                expr: Box::new(judgement_expr),
                                etype: Box::new(judgement_type),
                            })));

                            let premiss_two = Some(Box::new(step(Expr::Judgement {
                                context: new_context,
                                expr: Box::new(last_fv_type.clone()),
                                etype: Box::new(determine_sort(last_fv_type, context.to_vec())),
                            })));

                            return DStep {
                                rule: DRule::Weak,
                                conclusion,
                                premiss_one,
                                premiss_two,
                            };
                        }
                        _ => (),
                    }
                    // TODO how to match weak? later?
                }
                Some(_) => unreachable!(),
                None => (),
            };

            // Form rule
            if let Expr::PiAbstraction {
                ident: pi_ident,
                etype: pi_type,
                body: pi_body,
            } = judgement_expr.clone()
            {
                if judgement_type != Expr::Star && judgement_type != Expr::Box {
                    panic!("pi type is {:?}", judgement_type);
                }

                let premiss_one = Some(Box::new(step(Expr::Judgement {
                    context: context.to_vec(),
                    expr: pi_type.clone(),
                    etype: Box::new(determine_sort(*pi_type.clone(), context.to_vec())),
                })));

                let pi_ident = match pi_ident {
                    Some(i) => *i,
                    None => Expr::Identifier("_".to_string()), // TODO search free variables, pick a new one?
                };

                let premiss_two = Some(Box::new(step(Expr::Judgement {
                    context: append_to_context(pi_ident, *pi_type.clone(), context.to_vec()),
                    expr: pi_body,
                    etype: Box::new(judgement_type.clone()),
                })));

                return DStep {
                    rule: DRule::Form,
                    conclusion: Expr::Judgement {
                        context: context.to_vec(),
                        expr: Box::new(judgement_expr),
                        etype: Box::new(judgement_type),
                    },
                    premiss_one,
                    premiss_two,
                };
            }

            panic!(
                "ctx:  {:?}\nexpr: {:?}\ntype: {:?}",
                context, judgement_expr, judgement_type
            )
        }
        _ => panic!("b"),
    }
}

#[test]
fn sort() {
    let e = parser::parse_judgement("C |- * : #").unwrap();
    assert_eq!("[0] Γ ⊢ ∗ : □        (Sort)", stringify(step(e)));
}

#[test]
fn var() {
    let e = parser::parse_judgement("C, A: *, x: A |- x : A").unwrap();
    let r = stringify(step(e));
    println!("{r}");
    assert_eq!(r, "[0] A : ∗, x : A ⊢ x : A     (Var) on [1]\n[1] A : ∗ ⊢ A : ∗            (Var) on [2]\n[2] Γ ⊢ ∗ : □                (Sort)\n\n");

    // let e = parser::parse_judgement("C, x: A -> B -> C |- x : A -> B -> C").unwrap();
    // assert_eq!(stringify(step(e)), "");
}

#[test]
fn form() {
    let e = parser::parse_judgement("a: *, b:* |- a -> b : *").unwrap();
    let r = stringify(step(e));
    println!("{r}");
    assert_eq!(r, "[0] A : ∗, x : A ⊢ x : A     (Var) on [1]\n[1] A : ∗ ⊢ A : ∗            (Var) on [2]\n[2] Γ ⊢ ∗ : □                (Sort)\n\n");
}

fn stringify(derivation: DStep) -> String {
    stringify_h(derivation, 0, 0)
}

fn stringify_h(derivation: DStep, counter: u32, width: usize) -> String {
    let conclusion = parser::stringify(derivation.conclusion);

    let width = width.max(conclusion.len());
    // println!("{} {}", width, conclusion.len());
    match (derivation.premiss_one, derivation.premiss_two) {
        (Some(p1), Some(p2)) => {
            let p1s = stringify_h(*p1, counter + 1, width);
            let p2s = stringify_h(*p2, counter + 2, width);
            format!(
                "[{}] {:width$} ({:?}) on [{}] and [{}]\n{}\n{}\n",
                counter,
                conclusion,
                derivation.rule,
                counter + 1,
                counter + 2,
                p1s,
                p2s,
            )
        }
        (Some(p1), None) => {
            let p1s = stringify_h(*p1, counter + 1, width);
            format!(
                "[{}] {:width$} ({:?}) on [{}]\n{}\n",
                counter,
                conclusion,
                derivation.rule,
                counter + 1,
                p1s,
            )
        }
        _ => {
            format!(
                "[{}] {:width$} ({:?})",
                counter, conclusion, derivation.rule,
            )
        }
    }
}
