use std::{
    collections::{HashMap, HashSet},
    fmt::{self, format},
};
use thiserror::Error;

use crate::parser::{self, Expr};

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum Rule {
    Sort,
    Var,
    Weak,
    Form,
    Appl,
    Abst,
    Conv,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Use `self.number` to refer to each positional data point.
        // write!(f, "({}, {})", self.0, self.1)
        let s = match self {
            Rule::Var => " (var)".to_string(),
            _ => format!("{:?}", self).to_lowercase(),
        };
        write!(f, "{}", s)
    }
}

// type DerivationCache = HashMap<>

#[derive(PartialEq, Debug, Clone)]
struct Derivation {
    conclusion: Expr,
    rule: Rule,
    premiss_one: Option<Box<Derivation>>,
    premiss_two: Option<Box<Derivation>>,
}

#[derive(Debug, Error)]
enum DeriveError {
    #[error("Derivation unimplemented for judgement: {0}")]
    Unimplemented(String),
    #[error(r#"Unexpected Pi type "{0}" in judgement "{1}""#)]
    UnexpectedPiType(String, String),
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

fn derive(judgement: Expr) -> Result<Derivation, DeriveError> {
    match judgement.clone() {
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            let context = context.as_slice();
            let judgement_expr = *expr;
            let judgement_type = *etype;

            if let ([], Expr::Star, Expr::Box) = (context, &judgement_expr, &judgement_type) {
                return Ok(Derivation {
                    rule: Rule::Sort,
                    conclusion: Expr::Judgement {
                        context: context.to_vec(),
                        expr: Box::new(judgement_expr),
                        etype: Box::new(judgement_type),
                    },
                    premiss_one: None,
                    premiss_two: None,
                });
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
                        return Ok(Derivation {
                            rule: Rule::Var,
                            conclusion: Expr::Judgement {
                                context: context.to_vec(),
                                expr: Box::new(judgement_expr),
                                etype: Box::new(judgement_type),
                            },
                            premiss_one: Some(Box::new(derive(Expr::Judgement {
                                context: new_context,
                                expr: Box::new(last_fv_type.clone()),
                                etype: Box::new(determine_sort(last_fv_type, context.to_vec())),
                            })?)),
                            premiss_two: None,
                        });
                    }

                    match judgement_expr {
                        Expr::Identifier(_) | Expr::Star => {
                            let conclusion = Expr::Judgement {
                                context: context.to_vec(),
                                expr: Box::new(judgement_expr.clone()),
                                etype: Box::new(judgement_type.clone()),
                            };

                            let premiss_one = Some(Box::new(derive(Expr::Judgement {
                                context: new_context.clone(),
                                expr: Box::new(judgement_expr),
                                etype: Box::new(judgement_type),
                            })?));

                            let premiss_two = Some(Box::new(derive(Expr::Judgement {
                                context: new_context,
                                expr: Box::new(last_fv_type.clone()),
                                etype: Box::new(determine_sort(last_fv_type, context.to_vec())),
                            })?));

                            return Ok(Derivation {
                                rule: Rule::Weak,
                                conclusion,
                                premiss_one,
                                premiss_two,
                            });
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

                let premiss_one = Some(Box::new(derive(Expr::Judgement {
                    context: context.to_vec(),
                    expr: pi_type.clone(),
                    etype: Box::new(determine_sort(*pi_type.clone(), context.to_vec())),
                })?));

                let pi_ident = match pi_ident {
                    Some(i) => *i,
                    None => Expr::Identifier("_".to_string()), // TODO search free variables, pick a new one?
                };

                let premiss_two = Some(Box::new(derive(Expr::Judgement {
                    context: append_to_context(pi_ident, *pi_type.clone(), context.to_vec()),
                    expr: pi_body,
                    etype: Box::new(judgement_type.clone()),
                })?));

                return Ok(Derivation {
                    rule: Rule::Form,
                    conclusion: Expr::Judgement {
                        context: context.to_vec(),
                        expr: Box::new(judgement_expr),
                        etype: Box::new(judgement_type),
                    },
                    premiss_one,
                    premiss_two,
                });
            }
            Err(DeriveError::Unimplemented(parser::stringify(judgement)))
            // panic!(
            //     "ctx:  {:?}\nexpr: {:?}\ntype: {:?}",
            //     context, judgement_expr, judgement_type
            // )
        }
        _ => unreachable!(),
    }
}

#[test]
fn sort() {
    let e = parser::parse_judgement("C |- * : #").unwrap();
    assert_eq!("[0] Γ ⊢ ∗ : □        (Sort)", stringify(derive(e).unwrap()));
}

#[test]
fn var() {
    let e = parser::parse_judgement("C, A: *, x: A |- x : A").unwrap();

    let r = stringify(derive(e).unwrap());
    println!("{r}");
    assert_eq!(r, "[0] A : ∗, x : A ⊢ x : A     (Var) on [1]\n[1] A : ∗ ⊢ A : ∗            (Var) on [2]\n[2] Γ ⊢ ∗ : □                (Sort)\n\n");

    // let e = parser::parse_judgement("C, x: A -> B -> C |- x : A -> B -> C").unwrap();
}

#[test]
fn form() {
    let e = parser::parse_judgement("a: *, b:* |- a -> b : *").unwrap();
    let e = parser::parse_judgement("{} |- /a: * . a : *").unwrap();
    let e = parser::parse_judgement("{} |- (/a: * . a) -> (/b:*.b) : *").unwrap();
    let r = stringify(derive(e).unwrap());
    println!("{r}");
    assert_eq!(r, "[0] A : ∗, x : A ⊢ x : A     (Var) on [1]\n[1] A : ∗ ⊢ A : ∗            (Var) on [2]\n[2] Γ ⊢ ∗ : □                (Sort)\n\n");
}

#[test]
fn moo() {
    let x = derivation("{} |- \\a:*. a : *");
    assert_eq!("", x);
}

fn stringify(derivation: Derivation) -> String {
    stringify_h(derivation, 0, 0).1
}

fn stringify_h(derivation: Derivation, counter: u32, width: usize) -> (u32, String) {
    let conclusion = parser::stringify(derivation.conclusion.clone());
    let counter = counter + 1;

    let width = width.max(conclusion.len());
    // println!("{} {}", width, conclusion.len());
    match (derivation.premiss_one, derivation.premiss_two) {
        (Some(p1), Some(p2)) => {
            let (p1_counter, p1s) = stringify_h(*(p1.clone()), counter, width);
            let (p2_counter, p2s) = stringify_h(*p2, p1_counter, width);
            let s2 = match derivation.conclusion {
                Expr::Judgement {
                    context: _,
                    expr: _,
                    etype,
                } => *etype,
                _ => unreachable!(),
            };
            let s1 = match p1.conclusion {
                Expr::Judgement {
                    context: _,
                    expr: _,
                    etype,
                } => *etype,
                _ => unreachable!(),
            };
            let rule = match derivation.rule {
                Rule::Form => {
                    format!(
                        "{} ({}, {})",
                        Rule::Form,
                        parser::stringify(s1),
                        parser::stringify(s2)
                    )
                }
                rule => format!("{}", rule),
            };
            (
                p2_counter,
                format!(
                    "{:>5} {:width$} ({}) on [{}] and [{}]\n{}\n{}\n",
                    format!("[{counter}]"),
                    conclusion,
                    rule,
                    counter + 1,
                    p1_counter + 1,
                    p1s,
                    p2s,
                ),
            )
        }
        (Some(p1), None) => {
            let (p1_counter, p1s) = stringify_h(*p1, counter, width);
            (
                p1_counter,
                format!(
                    "{:>5} {:width$} {} on [{}]\n{}\n",
                    format!("[{counter}]"),
                    conclusion,
                    derivation.rule,
                    counter + 1,
                    p1s,
                ),
            )
        }
        _ => (
            counter,
            // "".to_string(),
            format!(
                "{:>5} {:width$} ({})",
                format!("[{counter}]"),
                conclusion,
                derivation.rule,
            ),
        ),
    }
}

type DerivationCache = HashMap<Expr, (i32, Option<RuleRef>)>;

fn deduplicate(d: Derivation) {
    let mut cache: DerivationCache = HashMap::new();

    deduplicate_h(d, &mut cache, &mut 0);

    let mut s = cache.drain().collect::<Vec<_>>();
    s.sort_unstable_by(|(_, v1), (_, v2)| v1.0.cmp(&v2.0));
    for (k, v) in s {
        println!("{} {:?}", parser::stringify(k), v);
    }

    println!("{:?}", cache);
    println!("{:?}", cache.values());
}
#[test]
fn dedup() {
    let e = parser::parse_judgement("a: *, b:*,c:*,d:* |- a -> b -> c->d : *").unwrap();
    let d = derive(e).unwrap();
    deduplicate(d);
    panic!();
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum RuleRef {
    One(Rule, i32),
    Two(Rule, i32, i32),
}

fn deduplicate_h(d: Derivation, c: &mut DerivationCache, id: &mut i32) -> i32 {
    c.entry(d.conclusion.clone()).or_insert_with(|| {
        let x = *id;
        *id = *id + 1;
        (x, None)
    });

    let rule_ref = match (d.premiss_one, d.premiss_two) {
        (Some(p1), Some(p2)) => {
            let p1_id = deduplicate_h(*p1, c, id);
            let p2_id = deduplicate_h(*p2, c, id);
            Some(RuleRef::Two(d.rule, p1_id, p2_id))
        }
        (Some(p1), None) => {
            let p1_id = deduplicate_h(*p1, c, id);
            Some(RuleRef::One(d.rule, p1_id))
        }
        _ => None,
    };

    if let Some(k) = c.get_mut(&d.conclusion) {
        k.1 = rule_ref;
        return k.0;
    }
    unreachable!()
}

pub fn derivation(s: &str) -> String {
    match parser::parse_judgement(s) {
        Ok(j) => match derive(j) {
            Ok(d) => stringify(d),
            Err(e) => format!("{}", e),
        },
        Err(e) => format!("{}", e),
    }
}
