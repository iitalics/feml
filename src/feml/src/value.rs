use crate::core_syntax as stx;
use crate::intern::Symbol;

use std::fmt;
use std::rc::Rc;

pub type ValBox = Rc<Val>;

pub enum Val {
    // type
    TypeType,
    // nat
    TypeNat,
    // nat value
    Nat(u64),
    // nat S constructor
    CtorS,
    // function value
    Fun(Clos),
    // function type
    Pi(ValBox, Clos),
    // neutral
    Neu(usize),
}

#[derive(Clone)]
pub struct Clos {
    pub sym: Symbol,
    pub exp: stx::TermBox,
    pub env: Env,
}

impl Clos {
    fn new(abs: stx::Abs, env: Env) -> Self {
        Self {
            sym: abs.param,
            exp: abs.body,
            env,
        }
    }
}

#[derive(Clone)]
pub enum Env {
    Neutral(usize),
    Cons(ValBox, Rc<Env>),
}

impl Env {
    pub fn nth(&self, mut i: usize) -> ValBox {
        let mut env = self;
        loop {
            match (env, i) {
                (Env::Neutral(n), i) => {
                    assert!(i < *n);
                    return neu(*n - i);
                }
                (Env::Cons(v, _), 0) => return v.clone(),
                (Env::Cons(_, rest), _) => {
                    env = rest;
                    i -= 1;
                }
            }
        }
    }
}

// == Constructors ==

pub fn type_type() -> ValBox {
    ValBox::new(Val::TypeType)
}

pub fn type_nat() -> ValBox {
    ValBox::new(Val::TypeNat)
}

pub fn nat(n: u64) -> ValBox {
    ValBox::new(Val::Nat(n))
}

pub fn ctor_s() -> ValBox {
    ValBox::new(Val::CtorS)
}

pub fn pi(dom: ValBox, rng: stx::Abs, env: Env) -> ValBox {
    ValBox::new(Val::Pi(dom, Clos::new(rng, env)))
}

pub fn arrow(dom: ValBox, rng: ValBox) -> ValBox {
    // (T -> U) == Pi (_ : T). U
    let env = env_cons(rng, env_empty());
    let rng = stx::Abs {
        param: Symbol::UNDERSCORE,
        body: stx::var(1),
    };
    pi(dom, rng, env)
}

pub fn fun(lam: stx::Abs, env: Env) -> ValBox {
    ValBox::new(Val::Fun(Clos::new(lam, env)))
}

pub fn neu(lvl: usize) -> ValBox {
    ValBox::new(Val::Neu(lvl))
}

pub fn env_empty() -> Env {
    env_neutral(0)
}

pub fn env_neutral(n: usize) -> Env {
    Env::Neutral(n)
}

pub fn env_cons(v: ValBox, env: Env) -> Env {
    Env::Cons(v, Rc::new(env))
}

// == Pretty printing ==

pub struct DisplayVal<'v> {
    val: &'v Val,
}

impl Val {
    // FIXME: pretty printing values is not really appropriate. you should reify values
    // back into terms and then pretty print terms. this would enable printing closures
    // and neutral terms.
    pub fn display(&self) -> DisplayVal<'_> {
        DisplayVal { val: self }
    }
}

impl fmt::Display for DisplayVal<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.val {
            Val::TypeType => write!(f, "type"),
            Val::TypeNat => write!(f, "nat"),
            Val::Nat(n) => write!(f, "{n}"),
            Val::Neu(lvl) => write!(f, "?{lvl}"),
            Val::CtorS | Val::Fun(_) => write!(f, "<Fun>"),
            Val::Pi(_, _) => write!(f, "<Pi>"),
        }
    }
}
