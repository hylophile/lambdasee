extern crate pest;

use std::borrow::Borrow;
use std::rc::Rc;

use pest::iterators::Pairs;
use pest::pratt_parser::PrattParser;
use pest::Parser;

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"]
pub struct LambdaCParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::{Left, Right}, Op};
        use Rule::{appl, arrow};

        // Precedence is defined lowest to highest
        PrattParser::new()
            // Addition and subtract have equal precedence
            .op(Op::infix(arrow, Right))
            .op(Op::infix(appl, Left))
    };
}

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum Expr {
    Identifier(String),
    Star,
    Box,
    Bottom,
    Application {
        lhs: Rc<Expr>,
        rhs: Rc<Expr>,
    },
    LambdaAbstraction {
        ident: Rc<Expr>,
        etype: Rc<Expr>,
        body: Rc<Expr>,
    },
    PiAbstraction {
        ident: Option<Rc<Expr>>,
        etype: Rc<Expr>,
        body: Rc<Expr>,
    },
    FreeVariable {
        ident: Rc<Expr>,
        etype: Rc<Expr>,
    },
    Judgement {
        context: Vec<Expr>,
        expr: Rc<Expr>,
        etype: Rc<Expr>,
    },
}

fn parse_expr(pairs: Pairs<Rule>) -> Expr {
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            // Rule::integer => Expr::Integer(primary.as_str().parse::<i32>().unwrap()),
            Rule::star => Expr::Star,
            Rule::ebox => Expr::Box,
            Rule::bottom => Expr::Bottom,
            Rule::lambda => {
                let mut inner = primary.into_inner();
                let ident = Rc::new(parse_expr(pest::iterators::Pairs::single(
                    inner.next().unwrap(),
                )));
                let etype = Rc::new(parse_expr(inner.next().unwrap().into_inner()));
                let body = Rc::new(parse_expr(inner.next().unwrap().into_inner()));
                Expr::LambdaAbstraction { ident, etype, body }
            }
            Rule::pi => {
                let mut inner = primary.into_inner();
                let ident = Rc::new(parse_expr(pest::iterators::Pairs::single(
                    inner.next().unwrap(),
                )));
                let etype = Rc::new(parse_expr(inner.next().unwrap().into_inner()));
                let body = Rc::new(parse_expr(inner.next().unwrap().into_inner()));
                Expr::PiAbstraction {
                    ident: Some(ident),
                    etype,
                    body,
                }
            }
            Rule::expr => parse_expr(primary.into_inner()),
            Rule::ident => Expr::Identifier(primary.as_str().into()),
            Rule::free_var => {
                let mut inner = primary.into_inner();
                let ident = Rc::new(parse_expr(pest::iterators::Pairs::single(
                    inner.next().unwrap(),
                )));
                let etype = Rc::new(parse_expr(inner.next().unwrap().into_inner()));
                Expr::FreeVariable { ident, etype }
            }
            Rule::judgement => {
                let mut inner = primary.into_inner();

                let context = inner.next().unwrap().into_inner();
                let context: Vec<_> = context
                    .map(|pair| parse_expr(Pairs::single(pair)))
                    .collect();

                let expr = Rc::new(parse_expr(inner.next().unwrap().into_inner()));
                let etype = Rc::new(parse_expr(inner.next().unwrap().into_inner()));

                Expr::Judgement {
                    context,
                    expr,
                    etype,
                }
            }

            rule => unreachable!("Expr::parse expected atom, found {:?}", rule),
        })
        // .map_body
        .map_infix(|lhs, op, rhs| match op.as_rule() {
            Rule::arrow => {
                let ident = None;
                let etype = Rc::new(lhs);
                let body = Rc::new(rhs);
                Expr::PiAbstraction { ident, etype, body }
            }
            Rule::appl => Expr::Application {
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
            },
            rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
        })
        .parse(pairs)
}

#[test]
fn it_works() {
    let line = "a:b ⊢ a : b";
    let x = parse_judgement(line);
    assert_eq!(
        format!("{x:?}"),
        r#"Ok(Judgement { context: [FreeVariable { ident: Identifier("a"), etype: Identifier("b") }], expr: Identifier("a"), etype: Identifier("b") })"#
    );
    // println!("{x:?}");

    // let line = "C ⊢ λα : ∗ . λβ : (∗ → ∗) . β(β α) : ∗ → (∗ → ∗) → ∗";
    // println!("{:#?}", p(line));
    // panic!();
}

pub fn stringify(e: Rc<Expr>) -> String {
    match (*e).borrow() {
        Expr::Identifier(s) => s.to_string(),
        Expr::Star => "∗".to_string(),
        Expr::Box => "□".to_string(),
        Expr::Bottom => "⊥".to_string(),
        Expr::Application { lhs, rhs } => {
            format!("({} {})", stringify(lhs.clone()), stringify(rhs.clone()))
        }
        Expr::LambdaAbstraction { ident, etype, body } => {
            format!(
                "(λ{} : {} . {})",
                stringify(ident.clone()),
                stringify(etype.clone()),
                stringify(body.clone())
            )
        }
        Expr::PiAbstraction { ident, etype, body } => match ident {
            Some(i) => {
                format!(
                    "(Π{} : {} . {})",
                    stringify(i.clone()),
                    stringify(etype.clone()),
                    stringify(body.clone())
                )
            }
            None => {
                match ((*etype).borrow(), (*body).borrow()) {
                    (Expr::Identifier(s1), Expr::Identifier(s2)) => format!("({s1} → {s2})"),
                    (Expr::Star | Expr::Box, Expr::Star | Expr::Box) => {
                        format!(
                            "({} → {})",
                            stringify(etype.clone()),
                            stringify(body.clone())
                        )
                    }
                    _ => format!(
                        "({} → {})",
                        stringify(etype.clone()),
                        stringify(body.clone())
                    ),
                }

                // format!("{} → {}", f(*etype), x)
            }
        },
        Expr::FreeVariable { ident, etype } => {
            format!(
                "{} : {}",
                stringify(ident.clone()),
                stringify(etype.clone())
            )
        }
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            let mut context = context
                .iter()
                .map(|e| stringify(Rc::new(e.clone())))
                .collect::<Vec<_>>()
                // .join(",\n");
                .join(", ");
            if context.is_empty() {
                context = "∅".to_string();
            }
            format!(
                // "{} \n\n⊢ {} \n\n: {}",
                "{} ⊢ {} : {}",
                context,
                stringify(expr.clone()),
                stringify(etype.clone())
            )
        }
    }
}

pub fn htmlify(e: Expr) -> String {
    match e {
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            let mut context = context
                .iter()
                .map(|e| stringify(Rc::new(e.clone())))
                .collect::<Vec<_>>()
                // .join(",\n");
                .join(", ");
            if context.is_empty() {
                context = "∅".to_string();
            }
            format!(
                r#"<code class="context">{}</code><code class="turnstile"> ⊢ </code><code class="expr">{}</code><code class="type-symbol"> : </code><code class="type">{}</code>"#,
                (context),
                stringify(expr),
                stringify(etype)
            )
        }
        _ => stringify(Rc::new(e)),
    }
}

// #[test]
// fn e() {
//     let line = "a:b⊢a : (b)";
//     assert_eq!("a : b ⊢ a : b", stringify(parse_judgement(line).unwrap()));

//     let _line = "C ⊢ λα : ∗ . λβ : (∗ → ∗) . a b β(β α) : ∗ → (∗ → ∗) → ∗";
//     let _line = "C ⊢ λα : ∗ . λβ : (∗ → ∗) . a b β(β α) : ∗ → ∗ → ∗ → ∗";
//     let line = "C |- (Πx : S . (A → P x)) → A → Πy : S . P y : kp";
//     // let line = "C |- (Πx : S . (A → P x)) : p";
//     // let line = "C |- A → P x : p";
//     // let line = "C ⊢ a : ∗ → (∗ → ∗) → ∗";
//     // let line = "C ⊢ a : a -> (* -> b) -> d";
//     let r = parse_judgement(line).unwrap();
//     println!("{r:#?}");
//     assert_eq!("a : b ⊢ a : b", stringify(r));
//     panic!();
// }

pub fn parse_judgement(input: &str) -> Result<Expr, pest::error::Error<Rule>> {
    match LambdaCParser::parse(Rule::judgement_program, input) {
        Ok(mut pairs) => {
            let a = pairs
                .next()
                .unwrap()
                .into_inner()
                .next()
                .unwrap()
                .into_inner();

            let x = parse_expr(a);
            Ok(x)
        }
        Err(e) => Err(e),
    }
}

// fn p_program(input: &str) -> Result<String, pest::error::Error<Rule>> {
//     // let line = "(Πx : S . (A → P x)) → A → Πy : S . P y";
//     // let line = "∅ ⊢ λα : ∗ . λβ : (∗ → ∗) . β(β α) : ∗ → (∗ → ∗) → ∗";
//     // let line = "α : ∗ . λβ : ∗ . α → β : e";
//     // let line = "(λα : ∗ . α → α) (γ → β)";
//     // let line = "(λα : ∗ . α → α) γ";
//     // let line = "(Πy : S . P y)";
//     // let line = "a -> b";
//     // let line = "a";
//     // let line = "a b";
//     // let line = "a b c";

//     match CalculatorParser::parse(Rule::program, &input) {
//         Ok(mut pairs) => {
//             // let a = pairs.next().unwrap();
//             println!("p: {pairs}");
//             let a = pairs.next().unwrap().into_inner();
//             let x = parse_expr(a);
//             let s = format!("{:#?}", x);
//             Ok(s)
//         }
//         Err(e) => Err(e),
//     }
// }

// fn miain() -> io::Result<()> {
//     let line = "(Πx : S . (A → P x)) → A → Πy : S . P y";
//     // let line = "∅ ⊢ λα : ∗ . λβ : (∗ → ∗) . β(β α) : ∗ → (∗ → ∗) → ∗";
//     // let line = "α : ∗ . λβ : ∗ . α → β : e";
//     // let line = "(λα : ∗ . α → α) (γ → β)";
//     // let line = "(λα : ∗ . α → α) γ";
//     // let line = "(Πy : S . P y)";
//     // let line = "a -> b";
//     // let line = "a";
//     // let line = "a b";
//     // let line = "a b c";

//     match CalculatorParser::parse(Rule::judgement_program, &line) {
//         Ok(mut pairs) => {
//             // let a = pairs.next().unwrap();
//             println!("p: {pairs}");
//             let a = pairs.next().unwrap();
//             println!("a: {a}");
//             println!(
//                 "Parsed: \n\n{:#?}",
//                 // inner of expr
//                 parse_expr(a)
//             );
//         }
//         Err(e) => {
//             eprintln!("Parse failed: {:?}", e);
//         } // }
//     }
//     Ok(())
// }
