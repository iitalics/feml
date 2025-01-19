use crate::core_syntax::{self, Term, TermBox};
use crate::value::{self, Clos, Env, Val, ValBox};

pub fn evaluate(env: Env, exp: TermBox) -> ValBox {
    use core_syntax::Constant::*;
    match &*exp {
        Term::Var(i) => env.nth(*i),
        Term::Cst(TypeType) => value::type_type(),
        Term::Cst(TypeNat) => value::type_nat(),
        Term::Cst(Z) => value::nat(0),
        Term::Cst(S) => value::ctor_s(),
        Term::Lam(lam) => {
            let lam = lam.clone();
            value::fun(lam, env)
        }
        Term::Pi(dom, rng) => {
            let dom = evaluate(env.clone(), dom.clone());
            let rng = rng.clone();
            value::pi(dom, rng.clone(), env)
        }
        Term::App(fun, arg) => {
            let fun = evaluate(env.clone(), fun.clone());
            let arg = evaluate(env, arg.clone());
            apply(fun, arg)
        }
    }
}

pub fn apply(fun: ValBox, arg: ValBox) -> ValBox {
    match &*fun {
        Val::Fun(clos) => apply_closure(clos, arg),
        Val::CtorS => match &*arg {
            Val::Nat(n) => value::nat(n.checked_add(1).expect("successor overflow")),
            _ => panic!("bad argument to S, expected nat"),
        },
        _ => panic!("invalid function application"),
    }
}

pub fn apply_closure(clos: &Clos, arg: ValBox) -> ValBox {
    let env = value::env_cons(arg, clos.env.clone());
    evaluate(env, clos.exp.clone())
}
