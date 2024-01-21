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

struct DStep {
    rule: DRule,
    conclusion: Expr,
}

pub fn derive(e: Expr) {
    todo!()
}

fn step(expr: Expr) -> DRule {
    match expr {
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            let context = context.as_slice();
            let expr = *expr;
            let etype = *etype;

            if let ([], Expr::Star, Expr::Box) = (context, &expr, &etype) {
                return DRule::Sort;
            }

            match context.last() {
                Some(Expr::FreeVariable {
                    ident,
                    etype: itype,
                }) => {
                    // (Some(*ident.clone()), Some(*etype.clone()))
                    let ident = *ident.clone();
                    let itype = *itype.clone();
                    if ident == expr && itype == etype {
                        // TODO x \not\in\ context
                        return DRule::Var;
                    }
                }
                Some(_) => unreachable!(),
                None => (),
            };

            // if let (Some(last_ident), Some(last_etype)) =

            panic!()
        }
        _ => panic!(),
    }
}

#[test]
fn sort() {
    let e = parser::parse_judgement("C |- * : #").unwrap();
    assert_eq!(step(e), DRule::Sort);
}

#[test]
fn var() {
    let e = parser::parse_judgement("C, x: A |- x : A").unwrap();
    assert_eq!(step(e), DRule::Var);

    let e = parser::parse_judgement("C, x: A -> B -> C |- x : A -> B -> C").unwrap();
    assert_eq!(step(e), DRule::Var);
}
