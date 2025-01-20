use crate::domain as dmn;
use crate::domain::{Env, EnvT, Idx, Lvl, Term, TermT, Val, ValT};

// == NbE ==

pub fn eval(env: Env, tm: Term) -> Val {
    // FIXME: make tail (mutual-)recursive, with apply and close
    match tm {
        TermT::Con(con) => dmn::val_con(*con),
        TermT::Var(idx) => index(env, *idx),
        TermT::App(fun, arg) => apply(eval(env, fun), eval(env, arg)),
        TermT::Fn(abs) => dmn::val_fn(*abs, env),
        TermT::Pi(dom, rng_abs) => dmn::val_pi(eval(env, dom), *rng_abs, env),
    }
}

pub fn index(mut env: Env, mut idx: Idx) -> Val {
    loop {
        match *env {
            EnvT::Ext(next, v) => {
                if idx == 0 {
                    return v;
                }
                env = next;
                idx -= 1;
            }
            EnvT::Neu(lvl) => {
                assert!(idx < lvl);
                return dmn::val_neu(lvl - idx);
            }
        }
    }
}

pub fn apply(fun: Val, arg: Val) -> Val {
    match fun {
        ValT::Fn(clos) => close(clos, arg),
        ValT::Con(con) => dmn::con_app(con, arg),
        ValT::Neu(neu) => dmn::neu_app(neu, arg),
        _ => todo!(),
    }
}

pub fn close(clos: &dmn::Clos, arg: Val) -> Val {
    eval(dmn::env_ext(clos.env, arg), clos.abs.body)
}

pub fn reify(ctx: Lvl, val: Val) -> Term {
    match val {
        ValT::Con(con) => {
            let mut tm = dmn::term_con(con.head);
            for &arg in con.args {
                tm = dmn::term_app(tm, reify(ctx, arg));
            }
            tm
        }
        ValT::Neu(neu) => {
            let lvl = neu.head;
            assert!(lvl <= ctx);
            let mut tm = dmn::term_var(ctx - lvl);
            for elim in neu.elims {
                match elim {
                    dmn::Elim::App(arg) => {
                        tm = dmn::term_app(tm, reify(ctx, arg));
                    }
                }
            }
            tm
        }
        ValT::Fn(body) => {
            let body_val = close(body, dmn::val_neu(ctx + 1));
            let body_tm = reify(ctx + 1, body_val);
            let body = dmn::Abs {
                name: body.abs.name,
                body: body_tm,
            };
            dmn::term_fn(body)
        }
        ValT::Pi(dom_ty, rng) => {
            let dom_tm = reify(ctx, dom_ty);
            let rng_ty = close(rng, dmn::val_neu(ctx + 1));
            let rng_tm = reify(ctx + 1, rng_ty);
            let rng = dmn::Abs {
                name: rng.abs.name,
                body: rng_tm,
            };
            dmn::term_pi(dom_tm, rng)
        }
    }
}
