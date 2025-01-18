use crate::core_syntax as stx;
use crate::core_syntax::Ex;
use crate::value as val;
use crate::value::{Env, Va, Val};

pub fn evaluate<'e>(env: Env<'e>, exp: &'e Ex<'e>) -> Val<'e> {
    use stx::Constant::*;
    match exp {
        Ex::Var(i) => env_ref(&env, *i),
        Ex::Cst(TypeType) => val::type_type(),
        Ex::Cst(TypeNat) => val::type_nat(),
        Ex::Cst(Z) => val::nat(0),
        Ex::Cst(S) => val::ctor_s(),
        Ex::App(f, a) => apply(evaluate(env.clone(), f), evaluate(env, a)),
        Ex::Lam(lam) => val::abs(lam, env),
    }
}

fn env_ref<'e>(mut env: &Env<'e>, mut i: usize) -> Val<'e> {
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

fn apply<'e>(fun: Val<'e>, arg: Val<'e>) -> Val<'e> {
    match &*fun {
        Va::Abs(lam, env) => {
            let env = val::cons(arg, env.clone());
            evaluate(env, &lam.1)
        }
        Va::CtorS => match &*arg {
            Va::Nat(n) => val::nat(n.checked_add(1).expect("successor overflow")),
            _ => panic!("bad argument to S, expected nat"),
        },
        _ => panic!("invalid function application"),
    }
}
