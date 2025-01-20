use crate::intern::Symbol;

pub type Con = Symbol;
pub type Lvl = u32;
pub type Idx = u32;

pub type Term = &'static TermT;
pub type Val = &'static ValT;
pub type Type = Val;
pub type Env = &'static EnvT;

pub enum TermT {
    // c
    Con(Con),
    // x
    Var(Idx),
    // f e
    App(Term, Term),
    // fn x => e
    Fn(Abs),
    // (x : t) -> s
    Pi(Term, Abs),
}

// x => e
#[derive(Copy, Clone)]
pub struct Abs {
    pub name: Option<Symbol>,
    pub body: Term,
}

impl TermT {
    pub fn alpha_eq(&self, rhs: &TermT) -> bool {
        // FIXME: make tail recursive
        match (self, rhs) {
            (TermT::Con(c1), TermT::Con(c2)) => *c1 == *c2,
            (TermT::Var(x1), TermT::Var(x2)) => *x1 == *x2,
            (TermT::App(f1, a1), TermT::App(f2, a2)) => f1.alpha_eq(f2) && a1.alpha_eq(a2),
            (TermT::Fn(a1), TermT::Fn(a2)) => a1.body.alpha_eq(a2.body),
            (TermT::Pi(dom1, rng1), TermT::Pi(dom2, rng2)) => {
                dom2.alpha_eq(dom1) && rng1.alpha_eq(rng2)
            }
            (_, _) => false,
        }
    }
}

impl Abs {
    pub fn alpha_eq(&self, rhs: &Abs) -> bool {
        // self.name ignored
        self.body.alpha_eq(rhs.body)
    }
}

pub enum ValT {
    // c
    Con(ConVal),
    // u
    Neu(NeuVal),
    // (λx.e)ρ
    Fn(Clos),
    // (Π(x:T).e)ρ
    Pi(Val, Clos),
}

// c V1 … Vn
pub struct ConVal {
    pub head: Con,
    pub args: &'static [Val],
}

#[derive(Copy, Clone)]
pub struct Clos {
    pub abs: Abs,
    pub env: Env,
}

// type Arg = Val;

// En[…E1[v]]
pub struct NeuVal {
    pub head: Lvl,
    pub elims: &'static [Elim],
}

#[derive(Copy, Clone)]
pub enum Elim {
    // u V
    App(Val),
}

pub enum EnvT {
    // ρ(i) = v_{n-i}
    Neu(Lvl),
    // (ρ,V)
    Ext(Env, Val),
}

pub fn term_var(idx: Idx) -> Term {
    Box::leak(Box::new(TermT::Var(idx)))
}

pub fn term_con(con: Con) -> Term {
    Box::leak(Box::new(TermT::Con(con)))
}

pub fn term_app(fun: Term, arg: Term) -> Term {
    Box::leak(Box::new(TermT::App(fun, arg)))
}

pub fn term_fn(abs: Abs) -> Term {
    Box::leak(Box::new(TermT::Fn(abs)))
}

pub fn term_pi(dom: Term, rng: Abs) -> Term {
    Box::leak(Box::new(TermT::Pi(dom, rng)))
}

pub fn val_con(head: Con) -> Val {
    Box::leak(Box::new(ValT::Con(ConVal { head, args: &[] })))
}

pub fn val_neu(head: Lvl) -> Val {
    Box::leak(Box::new(ValT::Neu(NeuVal { head, elims: &[] })))
}

pub fn val_fn(abs: Abs, env: Env) -> Val {
    Box::leak(Box::new(ValT::Fn(Clos { abs, env })))
}

pub fn val_pi(dom: Val, rng: Abs, env: Env) -> Val {
    Box::leak(Box::new(ValT::Pi(dom, Clos { abs: rng, env })))
}

pub fn val_arrow(dom: Val, rng: Val) -> Val {
    let const_abs = Abs {
        name: None,
        body: &TermT::Var(1),
    };
    let const_env = env_ext(env_empty(), rng);
    val_pi(dom, const_abs, const_env)
}

pub fn con_app(con: &ConVal, arg: Val) -> Val {
    let mut args = Vec::with_capacity(con.args.len() + 1);
    args.extend_from_slice(con.args);
    args.push(arg);
    Box::leak(Box::new(ValT::Con(ConVal {
        head: con.head,
        args: Box::leak(args.into_boxed_slice()),
    })))
}

pub fn neu_app(neu: &NeuVal, arg: Val) -> Val {
    let mut elims = Vec::with_capacity(neu.elims.len() + 1);
    elims.extend_from_slice(neu.elims);
    elims.push(Elim::App(arg));
    Box::leak(Box::new(ValT::Neu(NeuVal {
        head: neu.head,
        elims: Box::leak(elims.into_boxed_slice()),
    })))
}

pub fn env_empty() -> Env {
    &EnvT::Neu(0)
}

pub fn env_neutral(lvl: Lvl) -> Env {
    Box::leak(Box::new(EnvT::Neu(lvl)))
}

pub fn env_ext(env: Env, v: Val) -> Env {
    Box::leak(Box::new(EnvT::Ext(env, v)))
}
