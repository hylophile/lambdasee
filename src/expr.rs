use std::{borrow::Borrow, collections::HashSet, fmt, rc::Rc};

use crate::parser;

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
        context: Vec<Rc<Expr>>,
        expr: Rc<Expr>,
        etype: Rc<Expr>,
    },
}

impl Expr {
    pub fn new_pi(ident: Rc<Expr>, etype: Rc<Expr>, body: Rc<Expr>) -> Self {
        let ident_name = match (*ident).borrow() {
            Expr::Identifier(x) => x,
            _ => unreachable!(),
        };
        let ident = if identifier_names(body.clone()).contains(ident_name) {
            Some(Rc::new(Expr::Identifier(ident_name.to_string())))
        } else {
            None
        };
        Self::PiAbstraction {
            ident,
            etype: etype.clone(),
            body: body.clone(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Identifier(s) => write!(f, "{}", s.to_string()),
            Expr::Star => write!(f, "∗"),
            Expr::Box => write!(f, "□"),
            Expr::Bottom => write!(f, "⊥"),
            Expr::Application { lhs, rhs } => {
                write!(f, "({} {})", lhs, rhs)
            }
            Expr::LambdaAbstraction { ident, etype, body } => {
                write!(f, "(λ{} : {} . {})", ident, etype, body)
            }
            Expr::PiAbstraction { ident, etype, body } => match ident {
                Some(i) => {
                    write!(f, "(Π{} : {} . {})", i, etype, body)
                }
                None => {
                    write!(f, "{} → {}", etype, body)
                }
            },
            Expr::FreeVariable { ident, etype } => {
                write!(f, "{} : {}", ident, etype)
            }
            Expr::Judgement {
                context,
                expr,
                etype,
            } => {
                write!(f, "{} ⊢ {} : {}", fmt_context(context), expr, etype)
            }
        }
    }
}

pub type Context = Vec<Rc<Expr>>;

pub fn fmt_context(context: &Context) -> String {
    let mut c = context
        .iter()
        .map(|u| format!("{u}"))
        .collect::<Vec<_>>()
        .join(", ");
    if c.is_empty() {
        c = "∅".to_string();
    }
    c
}

pub fn htmlify(e: &Expr) -> String {
    match e {
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            format!(
                r#"<code class="context">{}</code><code class="turnstile"> ⊢ </code><code class="expr">{}</code><code class="type-symbol"> : </code><code class="type">{}</code>"#,
                fmt_context(&context),
                expr,
                etype
            )
        }
        _ => format!("{e}"),
    }
}

#[test]
fn idnames() {
    let s = "S : ∗, P : S → ∗, A : ∗ |- (Πx : S . (A → P x)) → A → Πy : S . P y : *";
    let j = parser::parse_judgement(s).unwrap();
    let mut ns = identifier_names(Rc::new(j));
    let mut ns = ns.drain().collect::<Vec<_>>();
    ns.sort();
    assert_eq!(ns, vec!["A", "P", "S", "x", "y"]);
}

fn identifier_names_h(expr: Rc<Expr>, names: &mut HashSet<String>) {
    match (*expr).borrow() {
        Expr::Identifier(x) => {
            names.insert(x.to_string());
        }
        Expr::Application { lhs, rhs } => {
            identifier_names_h(lhs.clone(), names);
            identifier_names_h(rhs.clone(), names);
        }
        Expr::LambdaAbstraction { ident, etype, body } => {
            identifier_names_h(ident.clone(), names);
            identifier_names_h(etype.clone(), names);
            identifier_names_h(body.clone(), names);
        }
        Expr::PiAbstraction { ident, etype, body } => {
            if let Some(ident) = ident {
                identifier_names_h(ident.clone(), names);
            }
            identifier_names_h(etype.clone(), names);
            identifier_names_h(body.clone(), names);
        }
        Expr::FreeVariable { ident, etype } => {
            identifier_names_h(ident.clone(), names);
            identifier_names_h(etype.clone(), names);
        }
        Expr::Judgement {
            context,
            expr,
            etype,
        } => {
            for x in context {
                identifier_names_h(x.clone(), names);
            }
            identifier_names_h(expr.clone(), names);
            identifier_names_h(etype.clone(), names);
        }
        _ => (),
    }
}
pub fn identifier_names(expr: Rc<Expr>) -> HashSet<String> {
    let mut names = HashSet::new();

    identifier_names_h(expr, &mut names);

    names
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
