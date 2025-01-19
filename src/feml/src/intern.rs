use bumpalo::Bump;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::Hash;
use std::num::NonZeroU32;
use std::ptr::NonNull;

/// References a string inside a [`Pool`]. If two [`Symbols`]s in the same [`Pool`] are
/// the same, then they refer to the same string.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Symbol(NonZeroU32);

impl Symbol {
    /// The symbol for "_", which is always present.
    pub const UNDERSCORE: Symbol = Symbol(NonZeroU32::new(1).unwrap());
}

/// Maintains a list of interned strings, which can be referred to using cheap handles
/// ([`Symbol`]).
pub struct Pool {
    al: Bump,
    symbols: RefCell<Vec<RawStr>>,
    lookup: RefCell<HashMap<RawStr, Symbol>>,
}

impl Pool {
    /// Create a new symbol interning pool.
    pub fn new() -> Self {
        let mut symbols = Vec::with_capacity(128);
        let mut lookup = HashMap::with_capacity(1024);

        // register known string(s)
        let s = RawStr::from_static("_");
        symbols.push(s);
        lookup.insert(s, Symbol::UNDERSCORE);

        Self {
            al: Bump::new(),
            symbols: RefCell::new(symbols),
            lookup: RefCell::new(lookup),
        }
    }

    /// Get the string contents of an existing [`Symbol`].
    // XXX: we could do some sort of pointer tagging tricks as a debugging measure against
    // bad inter-Pool references, but that is quite overkill here.
    pub fn get(&self, sym: Symbol) -> &str {
        let symbols = self.symbols.borrow();
        let idx = sym.0.get() as usize;
        let raw_str = symbols.get(idx - 1).expect("invalid symbol");
        // SAFETY: strings in self.symbols are never freed, so the &str is valid to live
        // as long as the pool itself.
        unsafe { raw_str.as_str() }
    }

    /// Intern a string, either allocating a new [`Symbol`] or returning an existing one.
    pub fn intern(&self, s: &str) -> Symbol {
        if let Some(sym) = self.lookup.borrow().get(s) {
            return *sym;
        }
        let mut symbols = self.symbols.borrow_mut();
        let mut lookup = self.lookup.borrow_mut();
        // SAFETY: the memory allocated by self.al is never freed, so the RawStr may be
        // used within internal data structures.
        let raw_str = unsafe { RawStr::new(self.al.alloc_str(s)) };
        let idx = u32::try_from(symbols.len() + 1).expect("too many symbols created");
        let sym = Symbol(NonZeroU32::new(idx).unwrap());
        symbols.push(raw_str);
        lookup.insert(raw_str, sym);
        sym
    }
}

// Wrapper around `*const str` to allow storing in `HashMap`.
#[derive(Copy, Clone)]
struct RawStr(NonNull<str>);

impl RawStr {
    fn from_static(s: &'static str) -> Self {
        RawStr(NonNull::from(s))
    }

    unsafe fn new(s: &str) -> Self {
        RawStr(NonNull::from(s))
    }

    unsafe fn as_str<'a>(self) -> &'a str {
        self.0.as_ref()
    }
}

impl Borrow<str> for RawStr {
    fn borrow(&self) -> &str {
        unsafe { self.as_str() }
    }
}

impl Hash for RawStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { self.as_str().hash(state) }
    }
}

impl PartialEq for RawStr {
    fn eq(&self, other: &Self) -> bool {
        unsafe { self.as_str().eq(other.as_str()) }
    }
}

impl Eq for RawStr {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_intern_get_eq() {
        let pool = Pool::new();
        let a = pool.intern("hello");
        let b = pool.intern(&format!("wor{}d", "l"));
        let c = pool.intern("hello");
        assert_eq!(pool.get(a), "hello");
        assert_eq!(pool.get(b), "world");
        assert_eq!(pool.get(c), "hello");
        assert!(a == c, "{} vs {}", a.0, c.0);
        assert!(a != b, "{} vs {}", a.0, b.0);
        assert!(b != c, "{} vs {}", b.0, c.0);
        let d = pool.intern("hello");
        let e = pool.intern("world");
        assert!(a == d, "{} vs {}", a.0, d.0);
        assert!(b == e, "{} vs {}", b.0, e.0);
        assert!(b != d, "{} vs {}", b.0, d.0);
        assert!(a != e, "{} vs {}", a.0, e.0);
    }

    #[test]
    fn test_intern_known() {
        let pool = Pool::new();
        assert_eq!(pool.get(Symbol::UNDERSCORE), "_");
        assert_eq!(pool.intern("_"), Symbol::UNDERSCORE);
    }

    #[test]
    fn test_intern_as_hash_key() {
        let pool = Pool::new();
        let a = pool.intern("hello");
        let b = pool.intern("world");
        let c = pool.intern("hello");
        let mut map = HashMap::new();
        map.insert(a, "A");
        map.insert(b, "B");
        assert_eq!(map.get(&a), Some(&"A"));
        assert_eq!(map.get(&b), Some(&"B"));
        assert_eq!(map.get(&c), Some(&"A"));
    }

    #[test]
    #[should_panic]
    fn test_intern_bad_symbol_panic() {
        let pool = Pool::new();
        let pool2 = Pool::new();
        let a = pool.intern("hello");
        std::mem::drop(pool);
        // this access is improper but not unsafe
        pool2.get(a);
    }
}
