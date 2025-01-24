use crate::domain;
use crate::elab;
use crate::format::{display_term, DisplayTerm};
use crate::gc::{self, Gc, Hndl};
use crate::intern::{self, Symbol};
use crate::nbe;
use crate::parse_tree;

use std::collections::HashMap;

pub struct Interpreter {
    intern_pool: intern::Pool,
    constants: HashMap<Symbol, usize>,
    constants_stash: gc::RootSet,
}

impl Interpreter {
    pub fn new(gc: &mut Gc) -> Self {
        let intern_pool = intern::Pool::new();
        let sym_type = intern_pool.intern("type");
        let sym_nat = intern_pool.intern("nat");
        let sym_s = intern_pool.intern("S");
        let sym_z = intern_pool.intern("Z");

        /* initialize constants */

        let mut constants = HashMap::new();
        let constants_stash = gc::RootSet::new(gc);
        let idx_type = constants_stash.save(domain::con_val(gc, sym_type));

        // type : type
        constants.insert(sym_type, idx_type);

        // nat : type
        constants.insert(sym_nat, idx_type);

        // Z : nat
        let idx_nat = constants_stash.save(domain::con_val(gc, sym_nat));
        constants.insert(sym_z, idx_nat);

        // S : nat -> nat
        let idx_arrow_nat_nat = {
            constants_stash.save(constants_stash.get(gc, idx_nat));
            constants_stash.save(constants_stash.get(gc, idx_nat));
            constants_stash.save(domain::arrow_val(gc, &constants_stash))
        };
        constants.insert(sym_s, idx_arrow_nat_nat);

        Self {
            intern_pool,
            constants,
            constants_stash,
        }
    }

    pub fn intern_pool(&self) -> &intern::Pool {
        &self.intern_pool
    }

    /// Display a term with no free variables.
    pub fn display<'gc>(&self, term: Hndl<'gc>) -> DisplayTerm<'_, 'static, 'gc> {
        display_term(&self.intern_pool, &[], term)
    }

    /// Get the type of a constant by the given symbol name.
    pub fn constant<'gc>(&self, gc: &'gc Gc, name: Symbol) -> Option<Hndl<'gc>> {
        let idx = *self.constants.get(&name)?;
        Some(self.constants_stash.get(gc, idx))
    }

    /// Normalize a term with no free variables.
    /* term :: term */
    pub fn normalize(&self, gc: &mut Gc, stash: &gc::RootSet) {
        stash.save(domain::empty_env());
        nbe::eval(gc, stash);
        nbe::reify(gc, 0, stash);
    }

    /* :: elab_term elab_type */
    pub fn elab_chk_assert(
        &self,
        gc: &mut Gc,
        ast: &parse_tree::Assert<'_, '_>,
        stash: &gc::RootSet,
    ) -> elab::Result<()> {
        let ref mut cx = elab::Context::new(self, gc);
        elab::elab_type(gc, cx, ast.ty)?;
        cx.stash().duplicate();
        elab::elab_term_chk(gc, cx, ast.exp)?;
        // :: ty tm
        cx.stash().transfer(stash);
        cx.reify(gc);
        cx.stash().transfer(stash);
        Ok(())
    }

    /* :: elab_type */
    pub fn elab_chk_def(
        &self,
        gc: &mut Gc,
        def: &parse_tree::Def<'_, '_>,
        stash: &gc::RootSet,
    ) -> elab::Result<()> {
        let ref mut cx = elab::Context::new(self, gc);

        // introduce parameters into scope
        for param in def.sig.params {
            elab::elab_type(gc, cx, param.ty)?;
            cx.stash().duplicate();
            cx.bind(Some(param.name));
        }

        // typecheck the body
        elab::elab_type(gc, cx, def.sig.ret_ty)?;
        cx.stash().duplicate();
        elab::elab_term_chk(gc, cx, def.body)?;
        cx.stash().transfer(stash);
        // :: param_tys ... ret_ty_tm

        // reconstruct full function type from each parameter
        // def f (x : t) ... : u  -->   (x : t) ... -> u
        cx.reify(gc);
        for param in def.sig.params.iter().rev() {
            // :: param_tys ... param_ty ret_ty_tm
            let var = Some(param.name.intern(&self.intern_pool));
            cx.unbind();
            cx.stash().swap();
            cx.reify(gc);
            cx.stash().swap();
            cx.stash().save(domain::pi_term(gc, var, cx.stash()));
            // :: param_tys ... pi_tm
        }
        // :: pi_tm
        cx.stash().transfer(stash);
        Ok(())
    }
}
