use crate::domain::Term;
use crate::gc::Hndl;
use crate::intern::{self, Symbol};

use core::fmt;
use std::borrow::Cow;

pub struct DisplayTerm<'s, 'c, 'gc> {
    intern_pool: &'s intern::Pool,
    scope: &'c [Option<Symbol>],
    term: Hndl<'gc>,
}

pub fn display_term<'s, 'c, 'gc>(
    intern_pool: &'s intern::Pool,
    scope: &'c [Option<Symbol>],
    term: Hndl<'gc>,
) -> DisplayTerm<'s, 'c, 'gc> {
    DisplayTerm {
        intern_pool,
        scope,
        term,
    }
}

impl fmt::Display for DisplayTerm<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut cx = DisplayTermContext::new(&self.intern_pool);
        for binding in self.scope.iter() {
            let name = binding.map_or(BLANK, |n| cx.fresh(n));
            cx.names.push(name);
        }
        cx.fmt(f, self.term, 0)
    }
}

struct DisplayTermContext<'s> {
    intern_pool: &'s intern::Pool,
    names: Vec<Cow<'s, str>>,
}

const BLANK: Cow<str> = Cow::Borrowed("");

impl<'s> DisplayTermContext<'s> {
    fn new(intern_pool: &'s intern::Pool) -> Self {
        Self {
            intern_pool,
            names: vec![],
        }
    }

    fn fresh(&self, symbol: Symbol) -> Cow<'s, str> {
        let orig_id = self.intern_pool.get(symbol);
        let mut new_id = Cow::Borrowed(orig_id);
        let mut tries = 1;
        'retry: loop {
            for prev_id in self.names.iter() {
                if prev_id == &new_id {
                    // add integer suffix to generate new name
                    // x -> x.2 -> x.3 -> ...
                    tries += 1;
                    new_id = Cow::Owned(format!("{orig_id}.{tries}"));
                    continue 'retry;
                }
            }
            return new_id;
        }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, term: Hndl<'_>, prec: u32) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match term.into() {
            Term::Con(t) => write!(f, "{}", self.intern_pool.get(t.con())),
            Term::Var(t) => {
                let idx = t.idx() as usize;
                if idx >= self.names.len() {
                    write!(f, "?{}", idx - self.names.len())
                } else {
                    write!(f, "{}", self.names[self.names.len() - idx - 1])
                }
            }
            Term::App(t) => {
                open(f, prec, 2)?;
                self.fmt(f, t.fun(), 2)?;
                write!(f, " ")?;
                self.fmt(f, t.arg(), 3)?;
                close(f, prec, 2)
            }
            Term::Fn(t) => {
                let name = t.var().map_or(BLANK, |n| self.fresh(n));
                open(f, prec, 0)?;
                write!(f, "fn {name} => ")?;
                self.names.push(name);
                let result = self.fmt(f, t.body(), 0);
                self.names.pop();
                result?;
                close(f, prec, 0)
            }
            Term::Pi(t) => {
                open(f, prec, 1)?;
                match t.var() {
                    Some(n) => {
                        let name = self.fresh(n);
                        write!(f, "({name} : ")?;
                        self.fmt(f, t.dom(), 0)?;
                        write!(f, ") -> ")?;
                        self.names.push(name);
                        let result = self.fmt(f, t.rng(), 1);
                        self.names.pop();
                        result?;
                    }
                    None => {
                        self.fmt(f, t.dom(), 2)?;
                        write!(f, " -> ")?;
                        self.names.push(BLANK);
                        let result = self.fmt(f, t.rng(), 1);
                        self.names.pop();
                        result?;
                    }
                }
                close(f, prec, 1)
            }
        }
    }
}
