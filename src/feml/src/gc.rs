use std::alloc::GlobalAlloc;
use std::cell::{Cell, RefCell};
use std::marker::PhantomData;
use std::rc::{Rc, Weak};
use std::{alloc, fmt, mem, ptr};

macro_rules! debugln {
    //($($t:tt)*) => { eprintln!($($t)*) };
    ($($_t:tt)*) => {
        ()
    };
}

// == GC ==

const MINIMUM_HEAP_SIZE: usize = 4096;
const HEAP_SIZE_FACTOR: usize = 8;

pub struct Gc {
    bump_ptr: ptr::NonNull<u8>,
    heap: Heap,
    alt_heap: Option<Heap>,
    live_set_size: usize,
    roots: RefCell<Vec<Weak<InnerRootSet>>>,
    stats: GcStats,
}

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Hash)]
pub struct GcStats {
    pub collects: usize,
    pub alloc_count_total: usize,
    pub alloc_bytes_total: usize,
    pub alloc_count_this_period: usize,
    pub alloc_bytes_this_period: usize,
    pub reloc_count_this_collect: usize,
    pub reloc_bytes_this_collect: usize,
    pub heap_size: usize,
    pub live_set_size: usize,
}

#[inline]
fn should_record_gc_statistics() -> bool {
    cfg!(test) || cfg!(debug_assertions)
}

#[inline]
fn should_overwrite_with_debug_bytes() -> bool {
    cfg!(test) || cfg!(debug_assertions)
}

impl Gc {
    pub fn new() -> Self {
        Self::with_heap_size(MINIMUM_HEAP_SIZE)
    }

    pub fn with_heap_size(initial_heap_size: usize) -> Self {
        assert_eq!(initial_heap_size % Heap::ALIGN, 0, "unaligned");
        let heap = Heap::new(initial_heap_size);
        Self {
            bump_ptr: heap.start,
            heap,
            alt_heap: None,
            live_set_size: 0,
            roots: RefCell::new(vec![]),
            stats: GcStats {
                heap_size: initial_heap_size,
                ..GcStats::default()
            },
        }
    }

    pub fn stats(&self) -> GcStats {
        self.stats
    }

    pub fn reset_stats(&mut self) {
        self.stats = GcStats::default();
        self.stats.heap_size = self.heap.size();
    }

    #[inline]
    pub fn alloc<T: GcType>(&mut self, mut object: T) -> Hndl<'_> {
        let object_size = object.gc_header().size();
        debug_assert!(object_size >= size_of_val(&object));

        let new_hndl = loop {
            unsafe {
                let bump_end = self.bump_ptr.add(object_size);
                if bump_end <= self.heap.end {
                    let new_hndl: RawHndl = self.bump_ptr.cast();
                    self.bump_ptr.cast::<T>().write(object);
                    self.bump_ptr = bump_end;
                    break Hndl::from_raw(new_hndl);
                }
            }

            self.collect_with_additional_root(Some(object.as_raw_hndl()));
            // try to move the bump ptr again after making more space
        };

        if should_record_gc_statistics() {
            self.stats.alloc_count_this_period += 1;
            self.stats.alloc_bytes_this_period += object_size;
            self.stats.alloc_count_total += 1;
            self.stats.alloc_bytes_total += object_size;
        }

        new_hndl
    }

    pub fn collect(&mut self) {
        self.collect_with_additional_root(None);
    }

    fn collect_with_additional_root(&mut self, extra_hndl: Option<RawHndl>) {
        // allocate to-space or reuse existing alt heap
        let to_space_size = (self.live_set_size * HEAP_SIZE_FACTOR).max(MINIMUM_HEAP_SIZE);
        let to_space = match self.alt_heap.take() {
            // TODO: shrink the to_space if its unnecessarily big
            Some(heap) if heap.size() >= to_space_size => heap,
            _ => Heap::new(to_space_size),
        };

        if should_record_gc_statistics() {
            self.stats.heap_size = to_space_size;
            self.stats.reloc_bytes_this_collect = 0;
            self.stats.reloc_count_this_collect = 0;
        }

        // replace heap with to-space; the prev heap is now the from-space
        let mut from_space = mem::replace(&mut self.heap, to_space);
        self.bump_ptr = self.heap.start;

        debugln!("begin collect: {:?}", self.stats);
        debugln!("from-space: {:?}..{:?}", from_space.start, from_space.end);
        debugln!("to-space:   {:?}..{:?}", self.heap.start, self.heap.end);
        debugln!("fixing roots");

        // traverse roots to keep objects live and adjust their pointers
        let mut i = 0;
        let mut n_roots = 0;
        loop {
            // get self.roots[i] and try to promote the weak ptr. if the RootSet has been
            // dropped, remove self.roots[i] instead
            let mut root_sets = self.roots.borrow_mut();
            let Some(weak_root_set) = root_sets.get(i) else {
                break;
            };
            let Some(root_set) = weak_root_set.upgrade() else {
                root_sets.swap_remove(i);
                continue;
            };

            // release the borrow on self.roots for the next section
            drop(root_sets);
            i += 1;

            let mut roots = root_set.roots.borrow_mut();
            for root in roots.iter_mut() {
                unsafe { *root = self.copy(*root) };
                n_roots += 1;
            }
        }

        let _ = n_roots;
        debugln!("root sets scanned: {i}");
        debugln!("roots scanned: {n_roots}");

        // scan the extra handle as if it is already allocated. this will fixup its fields
        if let Some(extra_hndl) = extra_hndl {
            debugln!(" extra hndl = {extra_hndl:?}");
            unsafe { self.scan(extra_hndl.cast()) };
        }

        // incrementally scan each object in the to-space
        let mut scan_ptr = self.heap.start;
        while scan_ptr < self.bump_ptr {
            scan_ptr = unsafe { self.scan(scan_ptr) };
        }

        if should_overwrite_with_debug_bytes() {
            from_space.overwrite_with_debug_bytes();
        }

        self.alt_heap = Some(from_space);
        self.live_set_size = unsafe { self.bump_ptr.offset_from(self.heap.start) as usize };

        if should_record_gc_statistics() {
            self.stats.collects += 1;
            self.stats.live_set_size = self.live_set_size;
            self.stats.alloc_bytes_this_period = 0;
            self.stats.alloc_count_this_period = 0;
        }

        debugln!("end collect: {:?}", self.stats);
    }

    unsafe fn copy(&mut self, hndl: RawHndl) -> RawHndl {
        // don't copy eternal objects
        let hdr = hndl.read();
        if hdr.is_eternal() {
            debugln!(" {hndl:?} is_eternal");
            return hndl;
        }

        // follow forward pointer if object has already been collected
        let fwd: ptr::NonNull<RawHndl> = hndl.add(1).cast();
        if hdr.is_forwaded() {
            let fwd_hndl = fwd.read();
            debugln!(" {hndl:?} fwd -> {fwd_hndl:?}");
            return fwd_hndl;
        }

        // allocate shallow copy of object
        let new_hndl: RawHndl = self.bump_ptr.cast();
        let size = hdr.size();
        let bump_end = self.bump_ptr.add(size);
        self.bump_ptr.copy_from_nonoverlapping(hndl.cast(), size);
        self.bump_ptr = bump_end;

        debugln!(
            " {hndl:?} (tag {:x} size {}) copy -> {new_hndl:?}",
            hdr.tag(),
            hdr.size()
        );

        // replace old object with forward pointer
        hndl.write(GcHeader::forwaded());
        fwd.write(new_hndl);

        if should_record_gc_statistics() {
            self.stats.reloc_count_this_collect += 1;
            self.stats.reloc_bytes_this_collect += hdr.size();
        }

        new_hndl
    }

    unsafe fn scan(&mut self, ptr: ptr::NonNull<u8>) -> ptr::NonNull<u8> {
        let hdr = ptr.cast::<GcHeader>().read();
        debugln!(" scan {ptr:?} (tag {:x} size {})", hdr.tag(), hdr.size());

        let object_end = ptr.add(hdr.size());
        let mut object_hndls = object_end.cast::<Cell<RawHndl>>();
        for _ in 0..hdr.hndls() {
            object_hndls = object_hndls.offset(-1);
            let hndl: &Cell<RawHndl> = object_hndls.as_ref();
            hndl.set(self.copy(hndl.get()));
        }

        object_end
    }
}

// == (Minor) heap storage ==

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

    fn size(&self) -> usize {
        unsafe { self.end.offset_from(self.start) as usize }
    }

    fn layout(&self) -> alloc::Layout {
        unsafe { alloc::Layout::from_size_align_unchecked(self.size(), Self::ALIGN) }
    }

    fn overwrite_with_debug_bytes(&mut self) {
        unsafe { ptr::write_bytes(self.start.as_ptr(), 0xDE, self.size()) }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        if should_overwrite_with_debug_bytes() {
            self.overwrite_with_debug_bytes();
        }
        unsafe { ALLOCATOR.dealloc(self.start.as_ptr(), self.layout()) }
    }
}

// == Handles & headers ==

/// Raw handle to a managed object. This is just a pointer to the header field at the
/// start of an object.
///
/// Raw handles may fall out of sync with the GC if they are not saved in a root set.
// TODO: allow RawHndl to be nullable, and allow ptr-tagged ints
pub type RawHndl = ptr::NonNull<GcHeader>;

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

const TAG_FORWARDED: u32 = 0xFEFE;

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

    pub const fn forwaded() -> Self {
        unsafe { Self::from_tag_shape(TAG_FORWARDED, 0) }
    }

    pub fn tag(&self) -> u32 {
        debug_assert_ne!(self.tag, TAG_FORWARDED, "pointer has been forwaded");
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

    pub fn is_forwaded(&self) -> bool {
        self.tag == TAG_FORWARDED
    }
}

/// Trait for managed objects. Must have [`GcHeader`] at the beginning of the object, and
/// the header must accurately describe the following data.
pub unsafe trait GcType {
    fn as_raw_hndl(&mut self) -> RawHndl {
        ptr::NonNull::from(self).cast()
    }

    fn gc_header(&self) -> GcHeader {
        unsafe { *(self as *const Self as *const GcHeader) }
    }
}

unsafe impl GcType for GcHeader {}

/// Handle to a managed object tied to a [`Gc`]. Holding onto such a handle prevents
/// garbage collection cycles, therefore it is guarunteed that the handle remains valid.
///
/// If you need to allocate a new object, you need to save any [`Hndl`]'s you care about
/// to a [`RootSet`] to protect it from possible garbage collection.
#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct Hndl<'gc> {
    raw: RawHndl,
    _gc: PhantomData<&'gc Gc>,
}

impl fmt::Debug for Hndl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Hndl").field(&self.raw).finish()
    }
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

    pub fn tag(&self) -> u32 {
        unsafe { self.raw.read().tag() }
    }

    pub unsafe fn as_ref<T: GcType>(&self) -> &'gc T {
        self.raw.cast().as_ref()
    }

    // TODO: bring these functions back when RawHndl is allowed to be null

    // pub fn null() -> Self {
    //     Self {
    //         raw: ptr::null_mut(),
    //         _gc: PhantomData,
    //     }
    // }

    // pub fn is_null(&self) -> bool {
    //     self.tag() == 0
    // }

    // pub unsafe fn get<T: GcType>(&self) -> Option<&'gc T> {
    //     (self.raw as *const T).as_ref()
    // }
}

impl Hndl<'static> {
    pub fn from_static<T: GcType>(object: &'static T) -> Self {
        assert!(object.gc_header().is_eternal());
        let ptr = RawHndl::new(object as *const T as *mut GcHeader).unwrap();
        unsafe { Self::from_raw(ptr) }
    }
}

// == Object representations ==

// managed object shape variants. uses the following mnemonics:
// - I: integer (i64)
// - H: managed handle (Hndl)

#[repr(C)]
pub struct GcVariantHH(GcHeader, Cell<RawHndl>, Cell<RawHndl>);

#[repr(C)]
pub struct GcVariantI(GcHeader, i64);

#[repr(C)]
pub struct GcVariantIH(GcHeader, i64, Cell<RawHndl>);

#[repr(C)]
pub struct GcVariantIHH(GcHeader, i64, Cell<RawHndl>, Cell<RawHndl>);

#[repr(C)]
pub struct GcVariantIHHH(GcHeader, i64, Cell<RawHndl>, Cell<RawHndl>, Cell<RawHndl>);

unsafe impl GcType for GcVariantI {}
unsafe impl GcType for GcVariantIH {}
unsafe impl GcType for GcVariantHH {}
unsafe impl GcType for GcVariantIHH {}
unsafe impl GcType for GcVariantIHHH {}

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

impl GcVariantI {
    pub fn new(tag: u32, field0: i64) -> Self {
        let hdr = GcHeader::from_tag_size_fields(tag, 16, 0);
        Self(hdr, field0)
    }

    pub const fn new_eternal(tag: u32, field0: i64) -> Self {
        let hdr = GcHeader::from_tag_size_fields(tag, 16, 0).eternal();
        Self(hdr, field0)
    }

    pub fn field0(&self) -> i64 {
        self.1
    }
}

impl GcVariantIH {
    pub fn new(tag: u32, field0: i64, field1: Hndl<'_>) -> Self {
        let hdr = GcHeader::from_tag_size_fields(tag, 24, 1);
        Self(hdr, field0, Cell::new(field1.as_raw()))
    }

    pub fn field0(&self) -> i64 {
        self.1
    }

    pub fn field1(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.2.get()) }
    }
}

impl GcVariantIHH {
    pub fn new(tag: u32, field0: i64, field1: Hndl<'_>, field2: Hndl<'_>) -> Self {
        let hdr = GcHeader::from_tag_size_fields(tag, 32, 2);
        Self(
            hdr,
            field0,
            Cell::new(field1.as_raw()),
            Cell::new(field2.as_raw()),
        )
    }

    pub fn field0(&self) -> i64 {
        self.1
    }

    pub fn field1(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.2.get()) }
    }

    pub fn field2(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.3.get()) }
    }
}

impl GcVariantIHHH {
    pub fn new(
        tag: u32,
        field0: i64,
        field1: Hndl<'_>,
        field2: Hndl<'_>,
        field3: Hndl<'_>,
    ) -> Self {
        let hdr = GcHeader::from_tag_size_fields(tag, 40, 3);
        Self(
            hdr,
            field0,
            Cell::new(field1.as_raw()),
            Cell::new(field2.as_raw()),
            Cell::new(field3.as_raw()),
        )
    }

    pub fn field0(&self) -> i64 {
        self.1
    }

    pub fn field1(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.2.get()) }
    }

    pub fn field2(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.3.get()) }
    }

    pub fn field3(&self) -> Hndl<'_> {
        unsafe { Hndl::from_raw(self.4.get()) }
    }
}

// == Root sets ("stash") ==

pub struct RootSet {
    inner: Rc<InnerRootSet>,
}

struct InnerRootSet {
    roots: RefCell<Vec<RawHndl>>,
}

impl RootSet {
    pub fn new(gc: &Gc) -> Self {
        let inner = Rc::new(InnerRootSet {
            roots: RefCell::new(Vec::with_capacity(16)),
        });
        gc.roots.borrow_mut().push(Rc::downgrade(&inner));
        Self { inner }
    }

    pub fn len(&self) -> usize {
        self.inner.roots.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.roots.borrow().is_empty()
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

    pub fn swap(&self) {
        let mut roots = self.inner.roots.borrow_mut();
        let i = roots.len() - 1;
        let j = roots.len() - 2;
        roots.swap(i, j);
    }

    pub fn transfer(&self, dst: &RootSet) -> usize {
        let mut dst_roots = dst.inner.roots.borrow_mut();
        // if this fails we are trying to do self.transfer(self) which is a no-op
        if let Ok(mut roots) = self.inner.roots.try_borrow_mut() {
            dst_roots.push(roots.pop().unwrap());
        }
        dst_roots.len() - 1
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

impl fmt::Debug for RootSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RootSet[")?;
        let mut sep = "";
        for &raw in self.inner.roots.borrow().iter() {
            let hndl = unsafe { Hndl::from_raw(raw) };
            let tag = hndl.tag();
            write!(f, "{sep}{tag:x}")?;
            sep = ", ";
        }
        write!(f, "]")
    }
}

// demo: tree data structure
#[cfg(test)]
pub mod tree {
    use super::*;

    pub const TAG_LEAF: u32 = 0x0901;
    pub const TAG_NODE: u32 = 0x0902;

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

    impl<'gc> From<Hndl<'gc>> for Tree<'gc> {
        fn from(h: Hndl<'gc>) -> Self {
            match h.tag() {
                TAG_LEAF => Self::Leaf(unsafe { h.as_ref::<Leaf>() }),
                TAG_NODE => Self::Node(unsafe { h.as_ref::<Node>() }),
                _ => panic!("type error: not a tree"),
            }
        }
    }

    impl fmt::Display for Tree<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            self.0.field0().into()
        }

        pub fn right(&self) -> Tree<'_> {
            self.0.field1().into()
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

    pub fn leaf0() -> Hndl<'static> {
        static LEAF0: Leaf = Leaf(GcVariantI::new_eternal(TAG_LEAF, 0));
        Hndl::from_static(&LEAF0)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! assert_leaf {
        ($e:expr, $i:expr) => {
            ({
                let e = $e;
                let i = $i;
                match tree::Tree::from(e) {
                    tree::Tree::Leaf(l) => assert_eq!(l.data(), i),
                    tree::Tree::Node(_) => panic!("node != leaf ({i})"),
                }
            })
        };
    }

    macro_rules! assert_node {
        ($e:expr) => {
            ({
                match tree::Tree::from($e) {
                    tree::Tree::Node(n) => (n.left(), n.right()),
                    tree::Tree::Leaf(_) => panic!("leaf != node"),
                }
            })
        };
    }

    #[test]
    fn test_allocate_leaf_no_collect() {
        let ref mut gc = Gc::with_heap_size(1024);
        let stash = RootSet::new(gc);
        for i in 0..64 {
            let leaf = tree::leaf(gc, i);
            stash.save(leaf);
        }
        assert_eq!(gc.stats.heap_size, 1024);
        assert_eq!(gc.stats.collects, 0);
        assert_eq!(gc.stats.alloc_count_total, 64);
        assert_eq!(gc.stats.alloc_bytes_total, 1024);
        for i in (0..64).rev() {
            let leaf = stash.restore(gc);
            assert_leaf!(leaf, i);
        }
    }

    #[test]
    fn test_allocate_leaf_collect() {
        let ref mut gc = Gc::with_heap_size(1024);
        let useless_dropped_stash = RootSet::new(gc);
        let stash = RootSet::new(gc);
        for i in 0..24 {
            let leaf = tree::leaf(gc, i);
            stash.save(leaf);
            stash.duplicate();
        }
        for i in 24..48 {
            let _damned = tree::leaf(gc, i);
        }
        assert_eq!(gc.stats.collects, 0);
        assert_eq!(gc.stats.alloc_count_total, 48);
        assert_eq!(gc.stats.alloc_bytes_total, 768);

        // test refcounting of RootSet's
        drop(useless_dropped_stash);

        // at i=64 we trigger a collect
        for i in 48..72 {
            let leaf = tree::leaf(gc, i);
            stash.save(leaf);
            stash.duplicate();
        }
        assert_eq!(gc.stats.collects, 1);
        assert_eq!(gc.stats.alloc_count_total, 72);
        assert_eq!(gc.stats.alloc_bytes_total, 1152);
        assert_eq!(gc.stats.alloc_count_this_period, 8);
        assert_eq!(gc.stats.alloc_bytes_this_period, 128);
        assert_eq!(gc.stats.reloc_count_this_collect, 40);
        assert_eq!(gc.stats.reloc_bytes_this_collect, 640);
        assert_eq!(gc.stats.live_set_size, 640);

        for i in (0..72).rev() {
            if i >= 24 && i < 48 {
                continue;
            }
            let leaf = stash.restore(gc);
            let leaf2 = stash.restore(gc);
            assert_eq!(leaf, leaf2, "dup leaf ({i})");
            assert_leaf!(leaf, i);
        }
    }

    #[test]
    fn test_no_collect_eternals() {
        let ref mut gc = Gc::with_heap_size(1024);
        let stash = RootSet::new(gc);
        stash.save(tree::leaf0());
        for i in 0..65 {
            let _damned = tree::leaf(gc, i);
        }
        assert_eq!(gc.stats.collects, 1);
        let leaf0 = stash.restore(gc);
        assert_leaf!(leaf0, 0);
    }

    #[test]
    fn test_allocate_node() {
        let ref mut gc = Gc::with_heap_size(1024);
        let stash = RootSet::new(gc);
        for i in 0..25 {
            let leaf = tree::leaf(gc, i);
            stash.save(leaf);
            stash.duplicate();
            let node = tree::node(gc, &stash);
            stash.save(node);
        }
        assert_eq!(gc.stats.collects, 0);
        assert_eq!(gc.stats.alloc_count_total, 50);
        assert_eq!(gc.stats.alloc_bytes_total, 1000);
        for i in (0..25).rev() {
            let node = stash.get(gc, i as usize);
            let (left, right) = assert_node!(node);
            assert_leaf!(left, i);
            assert_leaf!(right, i);
        }
    }

    #[test]
    fn test_allocate_node_collect() {
        let ref mut gc = Gc::with_heap_size(1024);
        let stash = RootSet::new(gc);
        for i in 0..25 {
            let leaf = tree::leaf(gc, i);
            stash.save(leaf);
            stash.duplicate();
            let node = tree::node(gc, &stash);
            stash.save(node);
        }
        let _leaf = tree::leaf(gc, 0);
        let _leaf = tree::leaf(gc, 0);
        assert_eq!(gc.stats.collects, 1);
        assert_eq!(gc.stats.alloc_count_total, 52);
        assert_eq!(gc.stats.alloc_bytes_total, 1032);
        assert_eq!(gc.stats.reloc_count_this_collect, 50);
        assert_eq!(gc.stats.reloc_bytes_this_collect, 1000);
        for i in (0..25).rev() {
            let node = stash.get(gc, i as usize);
            let (left, right) = assert_node!(node);
            assert_leaf!(left, i);
            assert_leaf!(right, i);
        }
    }

    #[test]
    fn test_allocate_node_collect_full_and_scan_alloc() {
        let ref mut gc = Gc::with_heap_size(1024);
        let stash = RootSet::new(gc);
        for i in 0..40 {
            let leaf = tree::leaf(gc, i);
            stash.save(leaf);
            stash.duplicate();
            let node = tree::node(gc, &stash);
            stash.save(node);
        }
        assert_eq!(gc.stats.collects, 1);
        assert_eq!(gc.stats.alloc_count_total, 80);
        assert_eq!(gc.stats.alloc_bytes_total, 1600);
        assert_eq!(gc.stats.reloc_count_this_collect, 51);
        assert_eq!(gc.stats.reloc_bytes_this_collect, 1016);
        for i in (0..40).rev() {
            let node = stash.get(gc, i as usize);
            let (left, right) = assert_node!(node);
            assert_leaf!(left, i);
            assert_leaf!(right, i);
        }
    }
}
