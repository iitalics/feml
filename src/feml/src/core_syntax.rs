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
