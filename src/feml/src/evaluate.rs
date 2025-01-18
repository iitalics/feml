use crate::core_syntax::{self, Term};
use crate::value::{self, Env, Val, ValBox};

pub fn evaluate<'e>(env: Env<'e>, exp: &'e Term<'e>) -> ValBox<'e> {
    use core_syntax::Constant::*;
    match exp {
        Term::Var(i) => env_ref(&env, *i),
        Term::Cst(TypeType) => value::type_type(),
        Term::Cst(TypeNat) => value::type_nat(),
        Term::Cst(Z) => value::nat(0),
        Term::Cst(S) => value::ctor_s(),
        Term::App(f, a) => apply(evaluate(env.clone(), f), evaluate(env, a)),
        Term::Lam(lam) => value::abs(lam, env),
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
            (Env::Empty, _) => panic!("invalid variable index"),
        }
    }
}

fn apply<'e>(fun: ValBox<'e>, arg: ValBox<'e>) -> ValBox<'e> {
    match &*fun {
        Val::Abs(core_syntax::Lam(_, body), env) => {
            let env = value::cons(arg, env.clone());
            evaluate(env, body)
        }
        Val::CtorS => match &*arg {
            Val::Nat(n) => value::nat(n.checked_add(1).expect("successor overflow")),
            _ => panic!("bad argument to S, expected nat"),
        },
        _ => panic!("invalid function application"),
    }
}
