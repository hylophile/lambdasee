extern crate pest;

use std::rc::Rc;

use pest::iterators::Pairs;
use pest::pratt_parser::PrattParser;
use pest::Parser;

use crate::expr::Expr;

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"]
pub struct LambdaC;

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

fn parse_expr(pairs: Pairs<Rule>) -> Expr {
    #[allow(clippy::unwrap_used)]
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
                Expr::new_pi(&ident, etype, &body)
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
                    .map(|pair| Rc::new(parse_expr(Pairs::single(pair))))
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

pub fn parse_judgement(input: &str) -> Result<Expr, pest::error::Error<Rule>> {
    match LambdaC::parse(Rule::judgement_program, input) {
        Ok(mut pairs) => {
            #[allow(clippy::unwrap_used)]
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
