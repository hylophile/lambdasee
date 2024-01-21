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
            let expr = *expr;
            let etype = *etype;

            if let ([], Expr::Star, Expr::Box) = (context, &expr, &etype) {
                return DStep {
                    rule: DRule::Sort,
                    conclusion: Expr::Judgement {
                        context: context.to_vec(),
                        expr: Box::new(expr),
                        etype: Box::new(etype),
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
                    let ident = *ident.clone();
                    let ident_type = *ident_type.clone();
                    let new_context = all_except_last(context.to_vec());

                    // Var rule
                    if ident == expr && ident_type == etype {
                        let ident_type_type = match ident_type {
                            Expr::Star => Expr::Box,
                            Expr::Identifier(_) => {
                                // TODO could this possibly lead to s \not\in {*, #} ? (illegal for var rule)
                                find_type_in_context(ident_type.clone(), context.to_vec())
                                    .expect(&format!("not in context: {ident_type:?}"))
                            }

                            ref x => panic!("ident_type_type: {:?}", ident_type),
                        };

                        // TODO x \not\in\ context
                        return DStep {
                            rule: DRule::Var,
                            conclusion: Expr::Judgement {
                                context: context.to_vec(),
                                expr: Box::new(expr),
                                etype: Box::new(etype),
                            },
                            premiss_one: Some(Box::new(step(Expr::Judgement {
                                context: new_context,
                                expr: Box::new(ident_type),
                                etype: Box::new(ident_type_type),
                            }))),
                            premiss_two: None,
                        };
                    }
                    // TODO how to match weak? later?
                }
                Some(_) => unreachable!(),
                None => (),
            };

            // if let (Some(last_ident), Some(last_etype)) =

            panic!("{context:?}\n{expr:?}\n{etype:?}")
        }
        _ => panic!("b"),
    }
}

fn stringify(derivation: DStep) -> String {
    stringify_h(derivation, 0, 0)
}

fn stringify_h(derivation: DStep, counter: u32, width: usize) -> String {
    let conclusion = parser::stringify(derivation.conclusion);
    let width = width.max(conclusion.len());

    match (derivation.premiss_one, derivation.premiss_two) {
        (Some(p1), Some(p2)) => {
            let p1s = stringify_h(*p1, counter + 1, width);
            let p2s = stringify_h(*p2, counter + 2, width);
            format!(
                "[{}] {} \t({:?}) on [{}] and [{}]\n{}\n{}",
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

#[test]
fn sort() {
    let e = parser::parse_judgement("C |- * : #").unwrap();
    // assert_eq!("Γ ⊢ ∗ : □ (Sort)\n\n", stringify(step(e)));
    // assert_eq!(step(e), DRule::Sort);
}

#[test]
fn var() {
    let e = parser::parse_judgement("C, A: *, x: A |- x : A").unwrap();
    let r = stringify(step(e));
    println!("{r}");
    assert_eq!(r, "");

    // let e = parser::parse_judgement("C, x: A -> B -> C |- x : A -> B -> C").unwrap();
    // assert_eq!(stringify(step(e)), "");
}
