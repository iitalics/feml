use crate::core_syntax::{self, Term, TermBox};
use crate::value::{self, Env, Val, ValBox};

pub fn evaluate<'e>(env: Env<'e>, exp: TermBox<'e>) -> ValBox<'e> {
    use core_syntax::Constant::*;
    match &*exp {
        Term::Var(i) => env_ref(&env, *i),
        Term::Cst(TypeType) => value::type_type(),
        Term::Cst(TypeNat) => value::type_nat(),
        Term::Cst(Z) => value::nat(0),
        Term::Cst(S) => value::ctor_s(),
        Term::App(f, a) => apply(evaluate(env.clone(), f.clone()), evaluate(env, a.clone())),
        Term::Lam(lam) => value::abs(lam.clone(), env),
    }
}

fn env_ref<'e>(mut env: &Env<'e>, mut i: usize) -> ValBox<'e> {
    loop {
        match (env, i) {
            (Env::Cons(v, _), 0) => return v.clone(),
            (Env::Cons(_, rest), _) => {
                env = rest;
                i -= 1;
            }
            (Env::Empty, _) => panic!("variable index out of range"),
        }
    }
}

fn apply<'e>(fun: ValBox<'e>, arg: ValBox<'e>) -> ValBox<'e> {
    match &*fun {
        Val::Abs(lam, env) => {
            let env = value::cons(arg, env.clone());
            // lam.arg_id ...?
            evaluate(env, lam.body.clone())
        }
        Val::CtorS => match &*arg {
            Val::Nat(n) => value::nat(n.checked_add(1).expect("successor overflow")),
            _ => panic!("bad argument to S, expected nat"),
        },
        _ => panic!("invalid function application"),
    }
}
