use crate::gc::{self, Gc, GcType, Hndl};
use crate::intern::Symbol;

pub type Con = Symbol;
pub type Lvl = u32;
pub type Idx = u32;

// == Terms ==

const TAG_TERM_CON: u32 = 0x101;
const TAG_TERM_VAR: u32 = 0x102;
const TAG_TERM_APP: u32 = 0x103;
const TAG_TERM_FN: u32 = 0x104;
const TAG_TERM_PI: u32 = 0x105;

#[derive(Copy, Clone)]
pub enum Term<'gc> {
    // c
    Con(&'gc ConTerm),
    // x
    Var(&'gc VarTerm),
    // f e
    App(&'gc AppTerm),
    // fn x => e
    Fn(&'gc FnTerm),
    // (x : t) -> s
    Pi(&'gc PiTerm),
}

impl<'gc> From<Hndl<'gc>> for Term<'gc> {
    fn from(hndl: Hndl<'gc>) -> Self {
        match hndl.tag() {
            TAG_TERM_CON => Self::Con(unsafe { hndl.as_ref() }),
            TAG_TERM_VAR => Self::Var(unsafe { hndl.as_ref() }),
            TAG_TERM_APP => Self::App(unsafe { hndl.as_ref() }),
            TAG_TERM_FN => Self::Fn(unsafe { hndl.as_ref() }),
            TAG_TERM_PI => Self::Pi(unsafe { hndl.as_ref() }),
            _ => panic!("invalid Term tag {:x}", hndl.tag()),
        }
    }
}

#[repr(transparent)]
pub struct ConTerm(gc::GcVariantI);

#[repr(transparent)]
pub struct VarTerm(gc::GcVariantI);

#[repr(transparent)]
pub struct AppTerm(gc::GcVariantHH);

#[repr(transparent)]
pub struct FnTerm(gc::GcVariantIH);

#[repr(transparent)]
pub struct PiTerm(gc::GcVariantIHH);

unsafe impl GcType for ConTerm {}
unsafe impl GcType for VarTerm {}
unsafe impl GcType for AppTerm {}
unsafe impl GcType for FnTerm {}
unsafe impl GcType for PiTerm {}

pub fn con_term(gc: &mut Gc, con: Con) -> Hndl<'_> {
    let tm = ConTerm(gc::GcVariantI::new(TAG_TERM_CON, con.to_integer()));
    gc.alloc(tm)
}

pub fn var_term(gc: &mut Gc, idx: Idx) -> Hndl<'_> {
    let tm = VarTerm(gc::GcVariantI::new(TAG_TERM_VAR, idx as i64));
    gc.alloc(tm)
}

pub fn app_term<'gc>(gc: &'gc mut Gc, stash: &gc::RootSet) -> Hndl<'gc> {
    let arg = stash.restore(gc);
    let fun = stash.restore(gc);
    let tm = AppTerm(gc::GcVariantHH::new(TAG_TERM_APP, fun, arg));
    gc.alloc(tm)
}

pub fn fn_term<'gc>(gc: &'gc mut Gc, var: Option<Symbol>, stash: &gc::RootSet) -> Hndl<'gc> {
    let var = var.map_or(0, Symbol::to_integer);
    let body = stash.restore(gc);
    let tm = FnTerm(gc::GcVariantIH::new(TAG_TERM_FN, var, body));
    gc.alloc(tm)
}

pub fn pi_term<'gc>(gc: &'gc mut Gc, var: Option<Symbol>, stash: &gc::RootSet) -> Hndl<'gc> {
    let var = var.map_or(0, Symbol::to_integer);
    let rng = stash.restore(gc);
    let dom = stash.restore(gc);
    let tm = PiTerm(gc::GcVariantIHH::new(TAG_TERM_PI, var, dom, rng));
    gc.alloc(tm)
}

impl ConTerm {
    pub fn con(&self) -> Con {
        Symbol::from_integer(self.0.field0()).unwrap()
    }
}

impl VarTerm {
    pub fn idx(&self) -> Idx {
        self.0.field0() as u32
    }
}

impl AppTerm {
    pub fn fun(&self) -> Hndl<'_> {
        self.0.field0()
    }

    pub fn arg(&self) -> Hndl<'_> {
        self.0.field1()
    }
}

impl FnTerm {
    pub fn var(&self) -> Option<Symbol> {
        Symbol::from_integer(self.0.field0())
    }

    pub fn body(&self) -> Hndl<'_> {
        self.0.field1()
    }
}

impl PiTerm {
    pub fn var(&self) -> Option<Symbol> {
        Symbol::from_integer(self.0.field0())
    }

    pub fn dom(&self) -> Hndl<'_> {
        self.0.field1()
    }

    pub fn rng(&self) -> Hndl<'_> {
        self.0.field2()
    }
}

// == Values ==

const TAG_VAL_CON: u32 = 0x201;
const TAG_VAL_NEU: u32 = 0x202;
const TAG_VAL_APP: u32 = 0x203;
const TAG_VAL_FN: u32 = 0x204;
const TAG_VAL_PI: u32 = 0x205;

#[derive(Copy, Clone)]
pub enum Val<'gc> {
    // c
    Con(&'gc ConVal),
    // u
    Neu(&'gc NeuVal),
    // u V | c V*
    App(&'gc AppVal),
    // (λx.e)ρ
    Fn(&'gc FnVal),
    // (Π(x:T).s)ρ
    Pi(&'gc PiVal),
}

impl<'gc> From<Hndl<'gc>> for Val<'gc> {
    fn from(hndl: Hndl<'gc>) -> Self {
        match hndl.tag() {
            TAG_VAL_CON => Self::Con(unsafe { hndl.as_ref() }),
            TAG_VAL_NEU => Self::Neu(unsafe { hndl.as_ref() }),
            TAG_VAL_APP => Self::App(unsafe { hndl.as_ref() }),
            TAG_VAL_FN => Self::Fn(unsafe { hndl.as_ref() }),
            TAG_VAL_PI => Self::Pi(unsafe { hndl.as_ref() }),
            _ => panic!("invalid Val tag {:x}", hndl.tag()),
        }
    }
}

#[repr(transparent)]
pub struct ConVal(gc::GcVariantI);

#[repr(transparent)]
pub struct NeuVal(gc::GcVariantI);

#[repr(transparent)]
pub struct AppVal(gc::GcVariantHH);

#[repr(transparent)]
pub struct FnVal(gc::GcVariantIHH);

#[repr(transparent)]
pub struct PiVal(gc::GcVariantIHHH);

unsafe impl GcType for ConVal {}
unsafe impl GcType for NeuVal {}
unsafe impl GcType for AppVal {}
unsafe impl GcType for FnVal {}
unsafe impl GcType for PiVal {}

impl ConVal {
    pub fn con(&self) -> Con {
        Symbol::from_integer(self.0.field0()).unwrap()
    }

    // TODO: fn args(&self) -> &[Hndl<'_>] ?
}

impl NeuVal {
    pub fn lvl(&self) -> Lvl {
        self.0.field0() as u32
    }

    // TODO: fn elims(&self) -> &[Hndl<'_>] ?
}

impl AppVal {
    pub fn head(&self) -> Hndl<'_> {
        self.0.field0()
    }

    pub fn arg(&self) -> Hndl<'_> {
        self.0.field1()
    }
}

impl FnVal {
    pub fn var(&self) -> Option<Symbol> {
        Symbol::from_integer(self.0.field0())
    }

    pub fn body(&self) -> Hndl<'_> {
        self.0.field1()
    }

    pub fn env(&self) -> Hndl<'_> {
        self.0.field2()
    }
}

impl PiVal {
    pub fn var(&self) -> Option<Symbol> {
        Symbol::from_integer(self.0.field0())
    }

    pub fn dom(&self) -> Hndl<'_> {
        self.0.field1()
    }

    pub fn rng(&self) -> Hndl<'_> {
        self.0.field2()
    }

    pub fn env(&self) -> Hndl<'_> {
        self.0.field3()
    }
}

pub fn con_val(gc: &mut Gc, head: Con) -> Hndl<'_> {
    let val = ConVal(gc::GcVariantI::new(TAG_VAL_CON, head.to_integer()));
    gc.alloc(val)
}

pub fn neu_val(gc: &mut Gc, head: Lvl) -> Hndl<'_> {
    let val = NeuVal(gc::GcVariantI::new(TAG_VAL_NEU, head as i64));
    gc.alloc(val)
}

pub fn app_val<'gc>(gc: &'gc mut Gc, stash: &gc::RootSet) -> Hndl<'gc> {
    let arg = stash.restore(gc);
    let head = stash.restore(gc);
    let val = AppVal(gc::GcVariantHH::new(TAG_VAL_APP, head, arg));
    gc.alloc(val)
}

pub fn fn_val<'gc>(gc: &'gc mut Gc, var: Option<Symbol>, stash: &gc::RootSet) -> Hndl<'gc> {
    let env = stash.restore(gc);
    let body = stash.restore(gc);
    let var = var.map_or(0, Symbol::to_integer);
    let val = FnVal(gc::GcVariantIHH::new(TAG_VAL_FN, var, body, env));
    gc.alloc(val)
}

pub fn pi_val<'gc>(gc: &'gc mut Gc, var: Option<Symbol>, stash: &gc::RootSet) -> Hndl<'gc> {
    let env = stash.restore(gc);
    let rng = stash.restore(gc);
    let dom = stash.restore(gc);
    let var = var.map_or(0, Symbol::to_integer);
    let val = PiVal(gc::GcVariantIHHH::new(TAG_VAL_PI, var, dom, rng, env));
    gc.alloc(val)
}

static VAR1: VarTerm = VarTerm(gc::GcVariantI::new_eternal(TAG_TERM_VAR, 1));

fn var1() -> Hndl<'static> {
    Hndl::from_static(&VAR1)
}

/* val val :: val */
pub fn arrow_val<'gc>(gc: &'gc mut Gc, stash: &gc::RootSet) -> Hndl<'gc> {
    // "T -> S" = (Π(_ : T).x)ρ   where x=1, ρ={},S
    stash.save(empty_env());
    stash.swap(); // :: dom empty_env rng
    stash.save(ext_env(gc, stash)); // :: dom env
    stash.save(var1());
    stash.swap(); // :: dom rng env
    pi_val(gc, None, stash)
}

// == Environments ==

const TAG_ENV_NEU: u32 = 0x301;
const TAG_ENV_EXT: u32 = 0x302;

#[derive(Copy, Clone)]
pub enum Env<'gc> {
    // u1,…,uN
    Neu(&'gc NeuEnv),
    // ρ,V
    Ext(&'gc ExtEnv),
}

impl<'gc> From<Hndl<'gc>> for Env<'gc> {
    fn from(hndl: Hndl<'gc>) -> Self {
        match hndl.tag() {
            TAG_ENV_NEU => Self::Neu(unsafe { hndl.as_ref() }),
            TAG_ENV_EXT => Self::Ext(unsafe { hndl.as_ref() }),
            _ => panic!("invalid Env tag {:x}", hndl.tag()),
        }
    }
}

#[repr(transparent)]
pub struct NeuEnv(gc::GcVariantI);

#[repr(transparent)]
pub struct ExtEnv(gc::GcVariantHH);

unsafe impl GcType for NeuEnv {}
unsafe impl GcType for ExtEnv {}

impl NeuEnv {
    pub fn lvl(&self) -> Lvl {
        self.0.field0() as u32
    }
}

impl ExtEnv {
    pub fn pop(&self) -> Hndl<'_> {
        self.0.field0()
    }

    pub fn top(&self) -> Hndl<'_> {
        self.0.field1()
    }
}

static EMPTY_ENV: NeuEnv = NeuEnv(gc::GcVariantI::new_eternal(TAG_ENV_NEU, 0));

pub fn empty_env() -> Hndl<'static> {
    Hndl::from_static(&EMPTY_ENV)
}

pub fn neu_env(gc: &mut Gc, lvl: Lvl) -> Hndl<'_> {
    if lvl == 0 {
        return empty_env();
    }
    let env = NeuEnv(gc::GcVariantI::new(TAG_ENV_NEU, lvl as i64));
    gc.alloc(env)
}

pub fn ext_env<'gc>(gc: &'gc mut Gc, stash: &gc::RootSet) -> Hndl<'gc> {
    let top = stash.restore(gc);
    let pop = stash.restore(gc);
    // TODO: (ρ(l), u_{l+1}) = ρ(l+1) ?
    let env = ExtEnv(gc::GcVariantHH::new(TAG_ENV_EXT, pop, top));
    gc.alloc(env)
}
