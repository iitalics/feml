use std::borrow::Cow;
use std::fmt;
use std::rc::Rc;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    TypeType,
    TypeNat,
    Z,
    S,
}

pub type TermBox<'s> = Rc<Term<'s>>;

#[derive(Debug)]
pub enum Term<'s> {
    // c
    Cst(Constant),
    // x
    Var(usize),
    // f a
    App(TermBox<'s>, TermBox<'s>),
    // fn x => e
    Lam(Abs<'s>),
    // (x : t) -> s
    Pi(TermBox<'s>, Abs<'s>),
}

#[derive(Debug, Clone)]
pub struct Abs<'s> {
    pub id: &'s str, // only for pretty printing
    pub body: TermBox<'s>,
}

// == Constructors ==

pub fn cst(c: Constant) -> TermBox<'static> {
    Rc::new(Term::Cst(c))
}

pub fn var(i: usize) -> TermBox<'static> {
    Rc::new(Term::Var(i))
}

pub fn app<'s>(fun: TermBox<'s>, arg: TermBox<'s>) -> TermBox<'s> {
    Rc::new(Term::App(fun, arg))
}

pub fn lam<'s>(id: &'s str, body: TermBox<'s>) -> TermBox<'s> {
    Rc::new(Term::Lam(Abs { id, body }))
}

pub fn pi<'s>(dom: TermBox<'s>, id: &'s str, rng: TermBox<'s>) -> TermBox<'s> {
    Rc::new(Term::Pi(dom, Abs { id, body: rng }))
}

// == Pretty printing ==

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TypeNat => write!(f, "nat"),
            Self::TypeType => write!(f, "type"),
            Self::Z => write!(f, "Z"),
            Self::S => write!(f, "S"),
        }
    }
}

struct DisplayTermContext<'s> {
    // convert debruijn indices into strings
    names: Vec<Cow<'s, str>>,
}

impl<'s> DisplayTermContext<'s> {
    fn new() -> Self {
        Self { names: vec![] }
    }

    fn fresh(&self, id: &'s str) -> Cow<'s, str> {
        let mut new_id = Cow::Borrowed(id);
        let mut tries = 0;
        'in_use: loop {
            for prev_id in self.names.iter() {
                if prev_id == &new_id {
                    // add integer suffix to generate new name
                    // x -> x1 -> x2 -> ...
                    tries += 1;
                    new_id = Cow::Owned(format!("{id}{tries}"));
                    continue 'in_use;
                }
            }
            return new_id;
        }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, exp: &Term<'s>, prec: u32) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match exp {
            Term::Cst(c) => write!(f, "{c}"),
            Term::Var(i) => {
                let id = &self.names[self.names.len() - i - 1];
                write!(f, "{id}")
            }
            Term::App(fun, arg) => {
                open(f, prec, 2)?;
                self.fmt(f, fun, 2)?;
                write!(f, " ")?;
                self.fmt(f, arg, 3)?;
                close(f, prec, 2)
            }
            Term::Lam(lam) => {
                open(f, prec, 0)?;
                let id = self.fresh(lam.id);
                write!(f, "fn {id}")?;
                self.names.push(id);
                let result = write!(f, " => ")
                    .and_then(|_| self.fmt(f, &lam.body, 0))
                    .and_then(|_| close(f, prec, 0));
                self.names.pop();
                result
            }
            Term::Pi(dom, rng) => {
                open(f, prec, 1)?;
                // TODO: if rng is constant in its argument, don't name the domain at all
                let id = self.fresh(rng.id);
                write!(f, "({id} : ")?;
                self.fmt(f, dom, 0)?;
                write!(f, ") -> ")?;
                self.names.push(id);
                let result = self.fmt(f, &rng.body, 1).and_then(|_| close(f, prec, 1));
                self.names.pop();
                result
            }
        }
    }
}

impl fmt::Display for Term<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        DisplayTermContext::new().fmt(f, self, 0)
    }
}
