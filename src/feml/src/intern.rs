use std::cell::RefCell;
use std::collections::HashMap;

/// Collection of interned strings. This enables storing many copies of the same string
/// using the same memory, and allows for extremely cheap comparison of strings.
pub struct Intern {
    strings: RefCell<Vec<String>>,
    lookup: RefCell<HashMap<String, Handle>>,
}

type Handle = u32;

impl Intern {
    pub fn new() -> Self {
        Self {
            strings: RefCell::new(Vec::with_capacity(1024)),
            lookup: RefCell::new(HashMap::with_capacity(1024)),
        }
    }

    pub fn intern<'a>(&'a self, s: &str) -> Str<'a> {
        let mut map = self.lookup.borrow_mut();
        let index = match map.get(s) {
            Some(i) => *i,
            None => {
                let mut strs = self.strings.borrow_mut();
                let i = strs.len() as Handle;
                let s = s.to_owned();
                map.insert(s.clone(), i);
                strs.push(s);
                i
            }
        };
        Str::new(self, index)
    }

    pub fn get<'a>(&'a self, h: Str<'a>) -> &'a str {
        let s: &str = &self.strings.borrow()[h.handle as usize];
        // SAFETY:
        // - this is safe because we only ever push new Strings to the end of the vec, we
        //   do not modify earlier entries. therefore the pointer underlying the strings
        //   has lifetime of self
        unsafe { &*(s as *const str) }
    }
}

/// References a string that has been interned. This handle does not allow you to get the
/// string contents directly; for that you must use [`Intern::get`]. However you can
/// compare `Str`'s for equality cheaply which only compares an underlying `u32`.
#[derive(Copy, Clone)]
pub struct Str<'a> {
    _intern: std::marker::PhantomData<&'a Intern>,
    handle: Handle,
}

impl<'a> Str<'a> {
    fn new(_intern: &'a Intern, handle: Handle) -> Self {
        Self {
            _intern: std::marker::PhantomData,
            handle,
        }
    }
}

impl PartialEq for Str<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.handle == other.handle
    }
}

impl Eq for Str<'_> {}

impl std::hash::Hash for Str<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.handle.hash(state)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_intern_get_eq() {
        let int = Intern::new();
        let a = int.intern("hello");
        let b = int.intern("world");
        let c = int.intern("hello");
        assert_eq!(int.get(a), "hello");
        assert_eq!(int.get(b), "world");
        assert_eq!(int.get(c), "hello");
        assert!(a == c, "{} vs {}", a.handle, c.handle);
        assert!(a != b, "{} vs {}", a.handle, b.handle);
        assert!(b != c, "{} vs {}", b.handle, c.handle);
        let d = int.intern("hello");
        let e = int.intern("world");
        assert!(a == d, "{} vs {}", a.handle, d.handle);
        assert!(b == e, "{} vs {}", b.handle, e.handle);
        assert!(b != d, "{} vs {}", b.handle, d.handle);
        assert!(a != e, "{} vs {}", a.handle, e.handle);
    }

    #[test]
    fn test_intern_as_hash_key() {
        let int = Intern::new();
        let a = int.intern("hello");
        let b = int.intern("world");
        let c = int.intern("hello");
        let mut map = HashMap::new();
        map.insert(a, "A");
        map.insert(b, "B");
        assert_eq!(map.get(&a), Some(&"A"));
        assert_eq!(map.get(&b), Some(&"B"));
        assert_eq!(map.get(&c), Some(&"A"));
    }
}
