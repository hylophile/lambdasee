extern crate pest;

use pest::iterators::Pairs;
use pest::pratt_parser::PrattParser;
use pest::Parser;
use std::io::{self};

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
            .op(Op::infix(appl, Left))
            .op(Op::infix(arrow, Right))
    };
}

#[derive(Debug)]
pub enum Expr {
    Ident(String),
    Star,
    Box,
    BinOp {
        lhs: Box<Expr>,
        op: Op,
        rhs: Box<Expr>,
    },
    LambdaAbstraction {
        ident: Box<Expr>,
        etype: Box<Expr>,
        body: Box<Expr>,
    },
    PiAbstraction {
        ident: Box<Expr>,
        etype: Box<Expr>,
        body: Box<Expr>,
    },
}

#[derive(Debug)]
pub enum Op {
    Application,
    Arrow,
}

pub fn parse_expr(pairs: Pairs<Rule>) -> Expr {
    // println!("{}", pairs);
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            // Rule::integer => Expr::Integer(primary.as_str().parse::<i32>().unwrap()),
            Rule::star => Expr::Star,
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
                Expr::PiAbstraction { ident, etype, body }
            }
            Rule::expr => parse_expr(primary.into_inner()),
            Rule::ident => Expr::Ident(primary.as_str().into()),
            rule => unreachable!("Expr::parse expected atom, found {:?}", rule),
        })
        // .map_body
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::arrow => Op::Arrow, // TODO convert to PiAbstraction
                Rule::appl => Op::Application,
                rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
            };
            Expr::BinOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            }
        })
        // .map_prefix(|op, rhs| match op.as_rule() {
        //     Rule::unary_minus => Expr::UnaryMinus(Box::new(rhs)),
        //     _ => unreachable!(),
        // })
        .parse(pairs)
}

fn miain() -> io::Result<()> {
    let line = "(Πx : S . (A → P x)) → A → Πy : S . P y";
    // let line = "∅ ⊢ λα : ∗ . λβ : (∗ → ∗) . β(β α) : ∗ → (∗ → ∗) → ∗";
    // let line = "α : ∗ . λβ : ∗ . α → β : e";
    // let line = "(λα : ∗ . α → α) (γ → β)";
    // let line = "(λα : ∗ . α → α) γ";
    // let line = "(Πy : S . P y)";
    // let line = "a -> b";
    // let line = "a";
    // let line = "a b";
    // let line = "a b c";

    match CalculatorParser::parse(Rule::program, &line) {
        Ok(mut pairs) => {
            // let a = pairs.next().unwrap();
            println!("p: {pairs}");
            let a = pairs.next().unwrap().into_inner();
            println!("a: {a}");
            println!(
                "Parsed: \n\n{:#?}",
                // inner of expr
                parse_expr(a)
            );
        }
        Err(e) => {
            eprintln!("Parse failed: {:?}", e);
        } // }
    }
    Ok(())
}

#[macro_use]
extern crate rocket;
use rocket::fs::FileServer;
#[post("/hi")]
fn index() -> &'static str {
    "Hello, world!"
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/api", routes![index])
        .mount("/", FileServer::from("src/html/"))
}
