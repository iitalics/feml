use std::alloc::GlobalAlloc;
use std::cell::{Cell, RefCell};
use std::marker::PhantomData;
use std::rc::{Rc, Weak};
use std::{alloc, ptr};

const MIN_HEAP_SIZE: usize = 16 * 1024;

#[repr(C)]
pub struct Gc {
    bump: ptr::NonNull<u8>,
    heap: Heap,
    token: Rc<()>,
    roots: RefCell<Vec<Weak<InnerRootSet>>>,
}

impl Gc {
    pub fn new() -> Self {
        let token = Rc::new(());
        let heap = Heap::new(MIN_HEAP_SIZE);
        Self {
            bump: heap.start,
            heap,
            token,
            roots: RefCell::new(vec![]),
        }
    }

    #[inline]
    pub fn alloc<T: GcType>(&mut self, object: T) -> Hndl<'_> {
        unsafe {
            let hdr = *object.as_raw_hndl();
            let hndl = self.bump.as_ptr() as RawHndl;
            let end = self.bump.add(hdr.size());
            if end > self.heap.end {
                todo!("GC collect");
            }
            ptr::copy_nonoverlapping(&object, hndl.cast(), 1);
            self.bump = end;
            Hndl::from_raw(hndl)
        }
    }
}

/// Block of memory used to store the minor heap.
#[derive(Debug)]
struct Heap {
    end: ptr::NonNull<u8>,
    start: ptr::NonNull<u8>,
}

static ALLOCATOR: alloc::System = alloc::System;

impl Heap {
    const ALIGN: usize = align_of::<GcHeader>();

    fn new(size: usize) -> Self {
        let layout = alloc::Layout::from_size_align(size, Self::ALIGN).unwrap();
        unsafe {
            let buf = ALLOCATOR.alloc(layout);
            let start = ptr::NonNull::new(buf).unwrap();
            let end = start.add(size);
            Self { start, end }
        }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        unsafe {
            let size = self.end.offset_from(self.start) as usize;
            let layout = alloc::Layout::from_size_align_unchecked(size, Self::ALIGN);
            let buf = self.start.as_ptr();
            ALLOCATOR.dealloc(buf, layout)
        }
    }
}

/// Raw handle to a managed object. This is just a pointer to the header field at the
/// start of an object.
///
/// Raw handles may fall out of sync with the GC if they are not saved in a root set.
pub type RawHndl = *mut GcHeader;

/// Header field allocated at the front of all managed objects.
#[repr(C, align(8))]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct GcHeader {
    tag: u32,
    // bits  0..=16: size
    // bits 17..=30: hndls
    // bit       31: is_eternal
    shape: u32,
}

impl GcHeader {
    pub const unsafe fn from_tag_shape(tag: u32, shape: u32) -> Self {
        Self { tag, shape }
    }

    pub const fn from_tag_size_fields(tag: u32, size: usize, hndls: usize) -> Self {
        assert!(hndls < 0x4000, "too many handles");
        assert!(size < 0x20000, "too big");
        assert!(
            size > size_of::<GcHeader>()
                && size >= (size_of::<GcHeader>() + hndls * size_of::<RawHndl>()),
            "too small"
        );
        assert!((size % Heap::ALIGN) == 0, "not aligned");
        let shape = (size as u32) | ((hndls as u32) << 17);
        unsafe { Self::from_tag_shape(tag, shape) }
    }

    pub const fn eternal(self) -> Self {
        unsafe { Self::from_tag_shape(self.tag, self.shape | 0x80000000) }
    }

    pub fn tag(&self) -> u32 {
        self.tag
    }

    pub fn size(&self) -> usize {
        (self.shape & 0x1ffff) as usize
    }

    pub fn hndls(&self) -> usize {
        ((self.shape >> 17) & 0x3fff) as usize
    }

    pub fn is_eternal(&self) -> bool {
        self.shape & 0x80000000 != 0
    }
}

/// Trait for managed objects. Must have [`GcHeader`] at the beginning of the object, and
/// the header must accurately describe the following data.
pub unsafe trait GcType {
    fn as_raw_hndl(&self) -> RawHndl {
        self as *const Self as RawHndl
    }
}

unsafe impl GcType for GcHeader {}

/// Handle to a managed object tied to a [`Gc`]. Holding onto such a handle prevents
/// garbage collection cycles, therefore it is guarunteed that the handle remains valid.
///
/// If you need to allocate a new object, you need to save any [`Hndl`]'s you care about
/// to a [`RootSet`] to protect it from possible garbage collection.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Hndl<'gc> {
    raw: RawHndl,
    _gc: PhantomData<&'gc Gc>,
}

impl<'gc> Hndl<'gc> {
    pub unsafe fn from_raw(raw: RawHndl) -> Self {
        Self {
            raw,
            _gc: PhantomData,
        }
    }

    pub fn as_raw(&self) -> RawHndl {
        self.raw
    }

    pub fn hdr(&self) -> GcHeader {
        unsafe { *self.raw }
    }

    pub unsafe fn get<T: GcType>(&self) -> &'gc T {
        let ptr = ptr::NonNull::new(self.raw).unwrap();
        ptr.cast().as_ref()
    }
}

// managed object shape variants. uses the following mnemonics:
// - I: integer (i64)
// - H: managed handle (Hndl)

#[repr(C)]
pub struct GcVariantI(GcHeader, i64);

#[repr(C)]
pub struct GcVariantHH(GcHeader, Cell<RawHndl>, Cell<RawHndl>);

unsafe impl GcType for GcVariantI {}
unsafe impl GcType for GcVariantHH {}

impl GcVariantI {
    pub const fn new(tag: u32, field0: i64) -> Self {
        let hdr = GcHeader::from_tag_size_fields(tag, 16, 0);
        Self(hdr, field0)
    }

    pub fn field0(&self) -> i64 {
        self.1
    }
}

impl GcVariantHH {
    pub fn new(tag: u32, field0: Hndl<'_>, field1: Hndl<'_>) -> Self {
        let hdr = GcHeader::from_tag_size_fields(tag, 24, 2);
        Self(hdr, Cell::new(field0.as_raw()), Cell::new(field1.as_raw()))
    }

    pub fn field0(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.1.get()) }
    }

    pub fn field1(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.2.get()) }
    }
}

pub struct RootSet {
    inner: Rc<InnerRootSet>,
}

struct InnerRootSet {
    roots: RefCell<Vec<RawHndl>>,
}

impl RootSet {
    pub fn new(gc: &Gc) -> Self {
        let inner = Rc::new(InnerRootSet {
            roots: RefCell::new(vec![]),
        });
        gc.roots.borrow_mut().push(Rc::downgrade(&inner));
        Self { inner }
    }

    // FIXME: for this to be sound, the user needs to be provide "proof" that handles
    // originate from the same Gc, or make there be a maximum of one active Gc

    pub fn save(&self, hndl: Hndl<'_>) -> usize {
        let mut roots = self.inner.roots.borrow_mut();
        let idx = roots.len();
        roots.push(hndl.as_raw());
        idx
    }

    pub fn restore<'gc>(&self, _gc: &'gc Gc) -> Hndl<'gc> {
        let mut roots = self.inner.roots.borrow_mut();
        let raw = roots.pop().unwrap();
        unsafe { Hndl::from_raw(raw) }
    }

    pub fn get<'gc>(&self, _gc: &'gc Gc, idx: usize) -> Hndl<'gc> {
        let roots = self.inner.roots.borrow();
        let raw = roots[idx];
        unsafe { Hndl::from_raw(raw) }
    }

    pub fn last<'gc>(&self, _gc: &'gc Gc) -> Hndl<'gc> {
        let roots = self.inner.roots.borrow();
        let raw = *roots.last().unwrap();
        unsafe { Hndl::from_raw(raw) }
    }

    pub fn duplicate(&self) {
        // this is "self.save(self.last(gc))" but without requiring a `Gc`
        let mut roots = self.inner.roots.borrow_mut();
        let top = *roots.last().unwrap();
        roots.push(top);
    }

    pub fn forget<'gc>(&self) {
        // this is "let _ = self.restore(gc)" but without requiring a `Gc`
        let mut roots = self.inner.roots.borrow_mut();
        roots.pop();
    }

    pub fn forget_all(&self) {
        let mut roots = self.inner.roots.borrow_mut();
        roots.clear();
    }
}

// demo: tree data structure
pub mod tree {
    use super::*;

    pub const TAG_LEAF: u32 = 0x1;
    pub const TAG_NODE: u32 = 0x2;

    #[derive(Copy, Clone)]
    pub enum Tree<'gc> {
        Leaf(&'gc Leaf),
        Node(&'gc Node),
    }

    #[repr(transparent)]
    pub struct Leaf(GcVariantI);

    #[repr(transparent)]
    pub struct Node(GcVariantHH);

    unsafe impl GcType for Leaf {}
    unsafe impl GcType for Node {}

    impl<'gc> Tree<'gc> {
        pub fn from_hndl(h: Hndl<'gc>) -> Self {
            match h.hdr().tag() {
                TAG_LEAF => Self::Leaf(unsafe { h.get::<Leaf>() }),
                TAG_NODE => Self::Node(unsafe { h.get::<Node>() }),
                _ => panic!("type error: not a tree"),
            }
        }
    }

    impl std::fmt::Display for Tree<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match *self {
                Self::Leaf(l) => write!(f, "{}", l.data()),
                Self::Node(n) => write!(f, "[{}, {}]", n.left(), n.right()),
            }
        }
    }

    impl Leaf {
        pub fn data(&self) -> i64 {
            self.0.field0()
        }
    }

    impl Node {
        pub fn left(&self) -> Tree<'_> {
            Tree::from_hndl(self.0.field0())
        }

        pub fn right(&self) -> Tree<'_> {
            Tree::from_hndl(self.0.field1())
        }
    }

    pub fn leaf<'gc>(gc: &'gc mut Gc, data: i64) -> Hndl<'gc> {
        let leaf = Leaf(GcVariantI::new(TAG_LEAF, data));
        gc.alloc(leaf)
    }

    pub fn node<'gc>(gc: &'gc mut Gc, args: &RootSet) -> Hndl<'gc> {
        let right = args.restore(gc);
        let left = args.restore(gc);
        let node = Node(GcVariantHH::new(TAG_NODE, left, right));
        gc.alloc(node)
    }
}
