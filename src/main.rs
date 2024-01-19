extern crate pest;

use pest::iterators::Pairs;
use pest::pratt_parser::PrattParser;
use pest::Parser;
use std::{
    error::Error,
    io::{self},
};

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"]
pub struct CalculatorParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        // Precedence is defined lowest to highest
        PrattParser::new()
            // Addition and subtract have equal precedence
            .op(Op::infix(arrow, Right))
            .op(Op::infix(appl, Left))
    };
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Identifier(String),
    Star,
    Box,
    Bottom,
    Application {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    LambdaAbstraction {
        ident: Box<Expr>,
        etype: Box<Expr>,
        body: Box<Expr>,
    },
    PiAbstraction {
        ident: Option<Box<Expr>>,
        etype: Box<Expr>,
        body: Box<Expr>,
    },
    FreeVariable {
        ident: Box<Expr>,
        etype: Box<Expr>,
    },
    Judgement {
        context: Vec<Expr>,
        expr: Box<Expr>,
        etype: Box<Expr>,
    },
}

pub fn parse_expr(pairs: Pairs<Rule>) -> Expr {
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            // Rule::integer => Expr::Integer(primary.as_str().parse::<i32>().unwrap()),
            Rule::star => Expr::Star,
            Rule::bottom => Expr::Bottom,
            Rule::lambda => {
                let mut inner = primary.into_inner();
                let ident = Box::new(parse_expr(pest::iterators::Pairs::single(
                    inner.next().unwrap(),
                )));
                let etype = Box::new(parse_expr(inner.next().unwrap().into_inner()));
                let body = Box::new(parse_expr(inner.next().unwrap().into_inner()));
                Expr::LambdaAbstraction { ident, etype, body }
            }
            Rule::pi => {
                let mut inner = primary.into_inner();
                let ident = Box::new(parse_expr(pest::iterators::Pairs::single(
                    inner.next().unwrap(),
                )));
                let etype = Box::new(parse_expr(inner.next().unwrap().into_inner()));
                let body = Box::new(parse_expr(inner.next().unwrap().into_inner()));
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
                let ident = Box::new(parse_expr(pest::iterators::Pairs::single(
                    inner.next().unwrap(),
                )));
                let etype = Box::new(parse_expr(inner.next().unwrap().into_inner()));
                Expr::FreeVariable { ident, etype }
            }
            Rule::judgement => {
                let mut inner = primary.into_inner();

                let context = inner.next().unwrap().into_inner();
                let context: Vec<_> = context
                    .map(|pair| parse_expr(Pairs::single(pair)))
                    .collect();

                let expr = Box::new(parse_expr(inner.next().unwrap().into_inner()));
                let etype = Box::new(parse_expr(inner.next().unwrap().into_inner()));

                Expr::Judgement {
                    context,
                    expr,
                    etype,
                }
            }
            Rule::gamma => Expr::Star,

            rule => unreachable!("Expr::parse expected atom, found {:?}", rule),
        })
        // .map_body
        .map_infix(|lhs, op, rhs| match op.as_rule() {
            Rule::arrow => {
                let ident = None;
                let etype = Box::new(lhs);
                let body = Box::new(rhs);
                Expr::PiAbstraction { ident, etype, body }
            }
            Rule::appl => Expr::Application {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
        })
        .parse(pairs)
}

#[test]
fn it_works() {
    let line = "a:b ⊢ a : b";
    let x = p(line);
    assert_eq!(
        format!("{x:?}"),
        r#"Ok(Judgement { context: [FreeVariable { ident: Identifier("a"), etype: Identifier("b") }], expr: Identifier("a"), etype: Identifier("b") })"#
    );
    // println!("{x:?}");

    // let line = "C ⊢ λα : ∗ . λβ : (∗ → ∗) . β(β α) : ∗ → (∗ → ∗) → ∗";
    // println!("{:#?}", p(line));
    // panic!();
}

fn f(e: Expr) -> String {
    match e {
        Expr::Identifier(s) => s.to_string(),
        Expr::Star => "∗".to_string(),
        Expr::Box => "□".to_string(),
        Expr::Bottom => "⊥".to_string(),
        Expr::Application { lhs, rhs } => {
            format!("({} {})", f(*lhs), f(*rhs))
        }
        Expr::LambdaAbstraction { ident, etype, body } => {
            format!("(λ{} : {} . {})", f(*ident), f(*etype), f(*body))
        }
        Expr::PiAbstraction { ident, etype, body } => match ident {
            Some(i) => {
                format!("(Π{} : {} . {})", f(*i), f(*etype), f(*body))
            }
            None => {
                match (&*etype, &*body) {
                    (Expr::Identifier(s1), Expr::Identifier(s2)) => format!("({s1} → {s2})"),
                    (Expr::Star | Expr::Box, Expr::Star | Expr::Box) => {
                        format!("({} → {})", f(*etype), f(*body))
                    }
                    _ => format!("({} → {})", f(*etype), f(*body)),
                }

                // format!("{} → {}", f(*etype), x)
            }
        },
        Expr::FreeVariable { ident, etype } => {
            format!("{} : {}", f(*ident), f(*etype))
        }
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            let mut context = context
                .iter()
                .map(|e| f((*e).clone()))
                .collect::<Vec<_>>()
                .join(",\n");
            if context == "" {
                context = "Γ".to_string();
            }
            format!("{} \n\n⊢ {} \n\n: {}", context, f(*expr), f(*etype))
        }
    }
}

#[test]
fn e() {
    let line = "a:b⊢a : (b)";
    assert_eq!("a : b ⊢ a : b", f(p(line).unwrap()));

    let line = "C ⊢ λα : ∗ . λβ : (∗ → ∗) . a b β(β α) : ∗ → (∗ → ∗) → ∗";
    let line = "C ⊢ λα : ∗ . λβ : (∗ → ∗) . a b β(β α) : ∗ → ∗ → ∗ → ∗";
    let line = "C |- (Πx : S . (A → P x)) → A → Πy : S . P y : kp";
    // let line = "C |- (Πx : S . (A → P x)) : p";
    // let line = "C |- A → P x : p";
    // let line = "C ⊢ a : ∗ → (∗ → ∗) → ∗";
    // let line = "C ⊢ a : a -> (* -> b) -> d";
    let r = p(line).unwrap();
    println!("{r:#?}");
    assert_eq!("a : b ⊢ a : b", f(r));
    panic!();
}

fn p(input: &str) -> Result<Expr, pest::error::Error<Rule>> {
    match CalculatorParser::parse(Rule::judgement_program, &input) {
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

fn p_program(input: &str) -> Result<String, pest::error::Error<Rule>> {
    // let line = "(Πx : S . (A → P x)) → A → Πy : S . P y";
    // let line = "∅ ⊢ λα : ∗ . λβ : (∗ → ∗) . β(β α) : ∗ → (∗ → ∗) → ∗";
    // let line = "α : ∗ . λβ : ∗ . α → β : e";
    // let line = "(λα : ∗ . α → α) (γ → β)";
    // let line = "(λα : ∗ . α → α) γ";
    // let line = "(Πy : S . P y)";
    // let line = "a -> b";
    // let line = "a";
    // let line = "a b";
    // let line = "a b c";

    match CalculatorParser::parse(Rule::program, &input) {
        Ok(mut pairs) => {
            // let a = pairs.next().unwrap();
            println!("p: {pairs}");
            let a = pairs.next().unwrap().into_inner();
            let x = parse_expr(a);
            let s = format!("{:#?}", x);
            Ok(s)
        }
        Err(e) => Err(e),
    }
}

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

#[macro_use]
extern crate rocket;
use rocket::fs::FileServer;
#[post("/hi")]
fn index() -> &'static str {
    "Hello, world!"
}

#[get("/parse?<query>")]
fn parse(query: &str) -> String {
    // format!("Hello, {}!", query)
    match p(query) {
        Ok(s) => {
            format!("{}", f(s))
        }
        Err(e) => format!("<span class='error'>Error!</span><pre>{:?}</pre>", e),
    }
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![index, parse])
        .mount("/", FileServer::from("src/html/"))
}
