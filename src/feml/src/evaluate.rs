use crate::core_syntax::{Constant, Exp};
use crate::value::{Env, Environ, Val, Value};

pub fn evaluate<'e>(env: Environ<'e>, exp: &'e Exp<'e>) -> Value<'e> {
    match exp {
        Exp::Var(i) => env_ref(&env, *i),
        Exp::Const(Constant::Z) => Value::new(Val::Nat(0)),
        Exp::Const(Constant::S) => Value::new(Val::S),
        Exp::Abs(_, b) => Value::new(Val::Abs(env, b)),
        Exp::App(f, a) => apply(evaluate(env.clone(), f), evaluate(env, a)),
    }
}

fn env_ref<'e>(mut env: &Env<'e>, mut i: usize) -> Value<'e> {
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

fn apply<'e>(fun: Value<'e>, arg: Value<'e>) -> Value<'e> {
    match &*fun {
        Val::Abs(env, body) => {
            let env = Environ::new(Env::Cons(arg, env.clone()));
            // FIXME: this is a tail call
            evaluate(env, body)
        }
        Val::S => match &*arg {
            Val::Nat(n) => Value::new(Val::Nat(suc(*n))),
            _ => panic!("bad argument to S, expected nat"),
        },
        _ => panic!("invalid function application"),
    }
}

fn suc(n: u64) -> u64 {
    n.checked_add(1).expect("integer overflow in successor")
}
