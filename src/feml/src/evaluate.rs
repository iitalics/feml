use crate::core_syntax::{Term, TermBox};
use crate::value::{self, Clos, Env, Val, ValBox};

pub fn evaluate(env: Env, exp: TermBox) -> ValBox {
    match &*exp {
        Term::Con(c) => value::con(*c),
        Term::Var(i) => env.nth(*i),
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
        Val::Con(c, args) => value::con_extend(*c, args, arg),
        _ => {
            assert!(matches!(&*fun, Val::NeVar(_) | Val::NeApp(_, _)));
            ValBox::new(Val::NeApp(fun, arg))
        }
    }
}

pub fn apply_closure(clos: &Clos, arg: ValBox) -> ValBox {
    let env = value::env_cons(arg, clos.env.clone());
    evaluate(env, clos.exp.clone())
}
