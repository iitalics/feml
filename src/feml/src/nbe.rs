use crate::domain::{self, Env, Idx, Lvl, Term, Val};
use crate::gc::{self, Gc};

/* term env :: val */
pub fn eval(gc: &mut Gc, stash: &gc::RootSet) {
    // FIXME: make tail (mutual-)recursive, with apply and close
    let env = stash.restore(gc);
    let tm = stash.restore(gc);
    match tm.into() {
        Term::Con(t) => {
            stash.save(domain::con_val(gc, t.con()));
        }
        Term::Var(t) => {
            stash.save(env);
            index(gc, stash, t.idx());
        }
        Term::App(t) => {
            stash.save(t.fun());
            stash.save(env);
            stash.save(t.arg());
            stash.save(env);
            eval(gc, stash);
            // :: fun env arg
            let arg = stash.restore(gc);
            let env = stash.restore(gc);
            let fun = stash.restore(gc);
            stash.save(arg);
            stash.save(fun);
            stash.save(env);
            eval(gc, stash);
            // :: arg fun
            apply(gc, stash);
        }
        Term::Fn(t) => {
            stash.save(t.body());
            stash.save(env);
            stash.save(domain::fn_val(gc, t.var(), stash));
        }
        Term::Pi(t) => {
            let var = t.var();
            stash.save(t.rng());
            stash.save(env);
            stash.save(t.dom());
            stash.save(env);
            eval(gc, stash);
            let dom = stash.restore(gc);
            let env = stash.restore(gc);
            let rng = stash.restore(gc);
            stash.save(dom);
            stash.save(rng);
            stash.save(env);
            stash.save(domain::pi_val(gc, var, stash));
        }
    }
}

/* env :: val */
pub fn index<'gc>(gc: &'gc mut Gc, stash: &gc::RootSet, mut idx: Idx) {
    let mut env = stash.restore(gc);
    loop {
        match env.into() {
            Env::Neu(e) => {
                assert!(idx < e.lvl());
                let lvl = e.lvl() - idx;
                stash.save(domain::neu_val(gc, lvl));
                return;
            }
            Env::Ext(e) => {
                if idx == 0 {
                    stash.save(e.top());
                    return;
                }
                env = e.pop();
                idx -= 1;
            }
        }
    }
}

/* arg fun :: val */
pub fn apply<'gc>(gc: &'gc mut Gc, stash: &gc::RootSet) {
    let fun = stash.restore(gc);
    let arg = stash.restore(gc);
    match fun.into() {
        Val::Fn(f) => {
            stash.save(f.body());
            stash.save(f.env());
            stash.save(arg);
            close(gc, stash)
        }
        Val::Con(_) | Val::Neu(_) | Val::App(_) => {
            stash.save(fun);
            stash.save(arg);
            stash.save(domain::app_val(gc, &stash));
        }
        Val::Pi(_) => panic!("invalid Pi application"),
    }
}

/* body env arg :: val */
pub fn close<'gc>(gc: &'gc mut Gc, stash: &gc::RootSet) {
    // TODO: if body is Var(0) return arg, if body is Var(n+1) then index from env
    stash.save(domain::ext_env(gc, stash)); // :: body env
    eval(gc, stash)
}

/* val :: term */
pub fn reify<'gc>(gc: &'gc mut Gc, ctx: Lvl, stash: &gc::RootSet) {
    let val = stash.restore(gc);
    match val.into() {
        Val::Con(v) => {
            stash.save(domain::con_term(gc, v.con()));
            //for arg in v.args() {...}
        }
        Val::Neu(v) => {
            let lvl = v.lvl();
            assert!(lvl <= ctx);
            let idx = ctx - lvl;
            stash.save(domain::var_term(gc, idx));
            //for elim in v.elims() {...}
        }
        Val::App(v) => {
            stash.save(v.arg());
            stash.save(v.head());
            reify(gc, ctx, stash);
            stash.swap();
            reify(gc, ctx, stash);
            stash.save(domain::app_term(gc, stash));
        }
        Val::Fn(v) => {
            let var = v.var();
            stash.save(v.body());
            stash.save(v.env());
            stash.save(domain::neu_val(gc, ctx + 1));
            close(gc, stash);
            reify(gc, ctx + 1, stash);
            stash.save(domain::fn_term(gc, var, stash));
        }
        Val::Pi(v) => {
            let var = v.var();
            stash.save(v.env());
            stash.save(v.rng());
            let dom = {
                stash.save(v.dom());
                reify(gc, ctx, stash);
                stash.restore(gc)
            };
            let rng = stash.restore(gc);
            let env = stash.restore(gc);
            stash.save(dom);
            stash.save(rng);
            stash.save(env);
            stash.save(domain::neu_val(gc, ctx + 1)); // :: dom rng env arg
            close(gc, stash); // :: dom rng
            reify(gc, ctx + 1, stash); // :: dom rng
            stash.save(domain::pi_term(gc, var, stash));
        }
    }
}
