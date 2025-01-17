use std::fmt;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    Z,
    S,
}

#[derive(Clone, Debug)]
pub enum Exp<'s> {
    Const(Constant),
    Var(usize),
    App(Box<Exp<'s>>, Box<Exp<'s>>),
    Abs(&'s str, Box<Exp<'s>>),
}

// == Pretty printing ==

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::S => write!(f, "S"),
            Constant::Z => write!(f, "Z"),
        }
    }
}

struct ExpDisplayContext<'s> {
    names: Vec<&'s str>,
}

fn open(f: &mut fmt::Formatter<'_>, prec: u32, min_prec: u32) -> fmt::Result {
    if prec > min_prec {
        write!(f, "(")?;
    }
    Ok(())
}

fn close(f: &mut fmt::Formatter<'_>, prec: u32, min_prec: u32) -> fmt::Result {
    if prec > min_prec {
        write!(f, ")")?;
    }
    Ok(())
}

impl<'s> ExpDisplayContext<'s> {
    fn new() -> Self {
        Self { names: vec![] }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, exp: &Exp<'s>, prec: u32) -> fmt::Result {
        match exp {
            Exp::Const(c) => write!(f, "{c}"),
            Exp::Var(i) => {
                let name = self.names[self.names.len() - i - 1];
                write!(f, "{name}")
            }
            Exp::App(fun, arg) => {
                open(f, prec, 2)?;
                self.fmt(f, fun, 2)?;
                write!(f, " ")?;
                self.fmt(f, arg, 3)?;
                close(f, prec, 2)
            }
            Exp::Abs(name, body) => {
                open(f, prec, 0)?;
                write!(f, "fn {name}")?;
                self.names.push(name);
                let result = write!(f, " => ")
                    .and_then(|_| self.fmt(f, body, 0))
                    .and_then(|_| close(f, prec, 0));
                self.names.pop();
                result
            }
        }
    }
}

impl fmt::Display for Exp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        ExpDisplayContext::new().fmt(f, self, 0)
    }
}
