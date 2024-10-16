#![allow(clippy::new_without_default)]

use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroUsize;
use core::ptr::{self, NonNull};

const D: usize = 10;
const CAPACITY: usize = MAX_KEYS;
const MAX_KEYS: usize = 2 * D - 1;
const MIN_KEYS: usize = D;

/// The common node data of leaf and internal nodes.
pub struct CommonData<K, V> {
    parent: Option<NonNull<InternalNode<K, V>>>,
    parent_idx: MaybeUninit<usize>,

    len: usize,
    keys: [MaybeUninit<K>; CAPACITY],
    _marker: PhantomData<V>,
}
/// A owned pointer to a leaf or internal node, however to be manually dropped.
pub type NodePtr<K, V> = NonNull<CommonData<K, V>>;

impl<K, V> core::fmt::Debug for CommonData<K, V>
where
    K: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut d = f.debug_struct("CommonData");
        d.field("parent", &self.parent);
        if self.parent.is_some() {
            d.field("parent_idx", &unsafe { self.parent_idx.assume_init() });
        }
        d.field("len", &self.len)
            .field("keys", &unsafe {
                MaybeUninit::slice_assume_init_ref(&self.keys[..self.len])
            })
            .finish()
    }
}

impl<K, V> CommonData<K, V> {
    /// Initialize the common data of a leaf or internal node in place.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid.
    unsafe fn init(this: *mut Self) {
        unsafe {
            ptr::addr_of_mut!((*this).parent).write(None);
            ptr::addr_of_mut!((*this).len).write(0);
        }
    }
}

/// The data of a internal node.
#[repr(C)]
pub(crate) struct InternalNode<K, V> {
    common: CommonData<K, V>,
    children: [MaybeUninit<NodePtr<K, V>>; CAPACITY],
}

impl<K, V> core::fmt::Debug for InternalNode<K, V>
where
    K: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("InternalNode")
            .field("common", &self.common)
            .field("children", &unsafe {
                MaybeUninit::slice_assume_init_ref(&self.children[..self.common.len])
            })
            .finish()
    }
}

impl<K, V> InternalNode<K, V> {
    /// Creates a new internal node.
    ///
    /// # Safety
    ///
    /// The caller must ensure that after initialization the node has at least one child.
    unsafe fn new() -> Box<Self> {
        let mut internal = Box::<Self>::new_uninit();
        // SAFE: `internal` is a valid pointer and access to `children` are controlled by
        // `common.len`.
        unsafe {
            CommonData::init(ptr::addr_of_mut!((*internal.as_mut_ptr()).common));
            internal.assume_init()
        }
    }
}

/// The data of a leaf node.
#[repr(C)]
pub(crate) struct LeafNode<K, V> {
    common: CommonData<K, V>,
    vals: [MaybeUninit<V>; CAPACITY],
    prev: Option<NonNull<Self>>,
    next: Option<NonNull<Self>>,
}

impl<K, V> core::fmt::Debug for LeafNode<K, V>
where
    K: core::fmt::Debug,
    V: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LeafNode")
            .field("common", &self.common)
            .field("vals", &unsafe {
                MaybeUninit::slice_assume_init_ref(&self.vals[..self.common.len])
            })
            .field("prev", &self.prev)
            .field("next", &self.next)
            .finish()
    }
}

impl<K, V> LeafNode<K, V> {
    /// Creates a new leaf node.
    fn new() -> Box<Self> {
        let mut leaf = Box::<Self>::new_uninit();
        // SAFE: `leaf` is a valid pointer and access to `children` are controlled by
        // `common.len`.
        unsafe {
            CommonData::init(ptr::addr_of_mut!((*leaf.as_mut_ptr()).common));
            ptr::addr_of_mut!((*leaf.as_mut_ptr()).prev).write(None);
            ptr::addr_of_mut!((*leaf.as_mut_ptr()).next).write(None);
            leaf.assume_init()
        }
    }
}

// --------------------------------------------------------
// --------------------------------------------------------
// Node

/// A manual emulation of borrowing forms of a node. Imitated from the implementation of
/// `BTreeMap`.
pub struct Node<B, K, V, N> {
    height: usize,
    common_ptr: NodePtr<K, V>,
    _marker: PhantomData<(B, N)>,
}
/// The simplification of generic owned nodes.
pub type Root<K, V> = NodeOwned<K, V, marker::Generic>;

impl<B, K, V, N> core::fmt::Debug for Node<B, K, V, N>
where
    K: core::fmt::Debug,
    V: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut d = f.debug_struct("Node");
        d.field("height", &self.height);
        match self.reborrow().into_generic().into_typed() {
            TypedResult::Leaf(leaf) => d.field("data", &(self.common_ptr, leaf.as_ref())),
            TypedResult::Internal(internal) => {
                d.field("data", &(self.common_ptr, internal.as_ref()))
            }
        }
        .finish()
    }
}

/// An owned node.
pub type NodeOwned<K, V, N> = Node<marker::Owned, K, V, N>;
/// An immutable reference to a node.
pub type NodeRef<'a, K, V, N> = Node<marker::Ref<'a>, K, V, N>;
/// The mutable reference to a node.
pub type NodeMut<'a, K, V, N> = Node<marker::Mut<'a>, K, V, N>;

impl<'a, K: 'a, V: 'a, N> Copy for NodeRef<'a, K, V, N> {}
impl<'a, K: 'a, V: 'a, N> Clone for NodeRef<'a, K, V, N> {
    fn clone(&self) -> Self {
        *self
    }
}
unsafe impl<B, K: Sync, V: Sync, N> Sync for Node<B, K, V, N> {}

unsafe impl<'a, K: Sync + 'a, V: Sync + 'a, N> Send for NodeRef<'a, K, V, N> {}
unsafe impl<'a, K: Send + 'a, V: Send + 'a, N> Send for NodeMut<'a, K, V, N> {}
unsafe impl<K: Send, V: Send, N> Send for Node<marker::Owned, K, V, N> {}

// --------------------------------------------------------
// Unspecified nodes

impl<B, K, V, N> Node<B, K, V, N> {
    pub fn len(&self) -> usize {
        unsafe { self.common_ptr.as_ref().len }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get a immutable reference to the node.
    pub fn reborrow(&self) -> NodeRef<'_, K, V, N> {
        NodeRef {
            height: self.height,
            common_ptr: self.common_ptr,
            _marker: PhantomData,
        }
    }

    fn as_common_ptr(&self) -> *mut CommonData<K, V> {
        self.common_ptr.as_ptr()
    }

    pub fn into_generic(self) -> Node<B, K, V, marker::Generic> {
        Node {
            height: self.height,
            common_ptr: self.common_ptr,
            _marker: PhantomData,
        }
    }

    pub fn into_first(self) -> Result<Entry<Self>, Self> {
        if !self.is_empty() {
            Ok(Entry { node: self, idx: 0 })
        } else {
            Err(self)
        }
    }

    pub fn into_last(self, additive: bool) -> Result<Entry<Self>, Self> {
        if !self.is_empty() {
            let idx = if additive { self.len() } else { self.len() - 1 };
            Ok(Entry { node: self, idx })
        } else {
            Err(self)
        }
    }

    fn eq(&self, other: &Self) -> bool {
        let Self {
            height, common_ptr, ..
        } = self;
        if common_ptr.eq(&other.common_ptr) {
            debug_assert!(*height == other.height);
            true
        } else {
            false
        }
    }
}

impl<K, V, N> NodeOwned<K, V, N> {
    /// Get the mutable reference to the node.
    ///
    /// Only the owner of the node can modify its data.
    pub fn borrow_mut(&mut self) -> NodeMut<'_, K, V, N> {
        NodeMut {
            height: self.height,
            common_ptr: self.common_ptr,
            _marker: PhantomData,
        }
    }

    fn clear_parent(&mut self) {
        let mut self_mut = self.borrow_mut();
        let common = self_mut.common_mut();
        common.parent = None;
    }
}

impl<K, V, N> NodeRef<'_, K, V, N> {
    pub fn keys(&self) -> &[K] {
        let len = self.len();
        // SAFE: at all states `len` available keys are guaranteed.
        unsafe { MaybeUninit::slice_assume_init_ref(&self.common_ptr.as_ref().keys[..len]) }
    }

    pub fn max_key(&self) -> ManuallyDrop<K> {
        let len = self.len();
        // SAFE: The max key is guaranteed not to be dropped.
        ManuallyDrop::new(unsafe { self.common_ptr.as_ref().keys[len - 1].assume_init_read() })
    }
}

impl<K, V, N> NodeMut<'_, K, V, N> {
    /// Get another mutable reference to the present one.
    ///
    /// # Safety
    ///
    /// Double mutable reference is strictly forbidden in safe Rust, so its use is extremely
    /// dangerous. The caller must ensure that the returned value is not modified at the same
    /// time `self` is used.
    unsafe fn reborrow_mut(&mut self) -> NodeMut<'_, K, V, N> {
        NodeMut {
            height: self.height,
            common_ptr: self.common_ptr,
            _marker: PhantomData,
        }
    }

    fn keys_mut(&mut self) -> &mut [MaybeUninit<K>] {
        let len = self.len();
        unsafe { &mut self.common_ptr.as_mut().keys[..len] }
    }

    fn common_mut(&mut self) -> &mut CommonData<K, V> {
        unsafe { self.common_ptr.as_mut() }
    }

    fn set_parent(&mut self, parent: NonNull<InternalNode<K, V>>, idx: usize) {
        let common = self.common_mut();
        common.parent = Some(parent);
        common.parent_idx.write(idx);
    }
}

// --------------------------------------------------------
// Leaf nodes

impl<B, K, V> Node<B, K, V, marker::Leaf> {
    fn as_ptr(&self) -> *mut LeafNode<K, V> {
        self.common_ptr.as_ptr().cast()
    }
}

impl<K, V> NodeOwned<K, V, marker::Leaf> {
    fn new() -> Self {
        Self::from_new(LeafNode::new())
    }

    fn from_new(new_leaf: Box<LeafNode<K, V>>) -> Self {
        let leaf = Box::leak(new_leaf);
        let common = &mut leaf.common;
        NodeOwned {
            height: 0,
            common_ptr: NonNull::from(common),
            _marker: PhantomData,
        }
    }

    pub fn drop(this: Self) {
        let _ = unsafe { Box::from_raw(this.as_ptr()) };
    }
}

impl<K, V> NodeRef<'_, K, V, marker::Leaf> {
    fn as_ref(&self) -> &LeafNode<K, V> {
        unsafe { &*self.as_ptr() }
    }
}

impl<K, V> NodeMut<'_, K, V, marker::Leaf> {
    fn as_mut(&mut self) -> &mut LeafNode<K, V> {
        unsafe { &mut *self.as_ptr() }
    }

    fn vals_mut(&mut self) -> &mut [MaybeUninit<V>] {
        let len = self.len();
        unsafe { &mut (*self.as_ptr()).vals[..len] }
    }

    unsafe fn merge(mut self, mut other: Self) -> Self {
        assert!(self.len() + other.len() <= MAX_KEYS);
        assert!(!self.eq(&other));

        let offset = self.len();
        let new_len = offset + other.len();
        self.common_mut().len = new_len;

        move_to_slice(other.keys_mut(), &mut self.keys_mut()[offset..new_len]);
        move_to_slice(other.vals_mut(), &mut self.vals_mut()[offset..new_len]);

        self.as_mut().next = other.reborrow().as_ref().next;
        if let Some(mut next) = self.as_mut().next {
            unsafe { next.as_mut().prev = Some(NonNull::from(self.as_mut())) };
        }

        self
    }

    unsafe fn steal_from_left(&mut self, other: Self) {
        assert!(other.len() > MIN_KEYS);
        assert!(!self.eq(&other));

        let other_last = other.into_last(false).unwrap_or_else(|_| unreachable!());
        unsafe {
            let mut self_first = self
                .reborrow_mut()
                .into_first()
                .unwrap_or_else(|_| unreachable!());

            let (_, (key, val)) = other_last.remove();
            self_first.insert_fit(key, val);
        }
    }

    unsafe fn steal_from_right(&mut self, other: Self) {
        assert!(other.len() > MIN_KEYS);
        assert!(!self.eq(&other));

        let other_first = other.into_first().unwrap_or_else(|_| unreachable!());
        unsafe {
            let mut self_last = self
                .reborrow_mut()
                .into_last(true)
                .unwrap_or_else(|_| unreachable!());

            let (_, (key, val)) = other_first.remove();
            self_last.insert_fit(key, val);
        }
    }
}

// --------------------------------------------------------
// Internal nodes

impl<B, K, V> Node<B, K, V, marker::Internal> {
    fn as_ptr(&self) -> *mut InternalNode<K, V> {
        self.common_ptr.as_ptr().cast()
    }

    fn from(node: NonNull<InternalNode<K, V>>, height: usize) -> Self {
        debug_assert!(height > 0);
        let common_ptr =
            unsafe { NonNull::new_unchecked(ptr::addr_of!(node.as_ref().common) as *mut _) };
        Node {
            height,
            common_ptr,
            _marker: PhantomData,
        }
    }
}

impl<K, V> NodeOwned<K, V, marker::Internal> {
    pub fn new(child: Root<K, V>) -> Self {
        let height = unsafe { NonZeroUsize::new_unchecked(child.height + 1) };
        let mut internal = unsafe { InternalNode::<K, V>::new() };
        internal.children[0].write(child.common_ptr);
        internal.common.len = 1;
        internal.common.keys[0].write(ManuallyDrop::into_inner(child.reborrow().max_key()));

        #[allow(clippy::forget_non_drop)]
        core::mem::forget(child);

        let mut ret = Self::from_new(internal, height);
        Entry {
            node: ret.borrow_mut(),
            idx: 0,
        }
        .link_child();
        ret
    }

    fn from_new(new_internal: Box<InternalNode<K, V>>, height: NonZeroUsize) -> Self {
        let internal = Box::leak(new_internal);
        let common = &mut internal.common;
        NodeOwned {
            height: height.get(),
            common_ptr: NonNull::from(common),
            _marker: PhantomData,
        }
    }

    pub fn drop(this: Self) {
        let _ = unsafe { Box::from_raw(this.as_ptr()) };
    }

    pub unsafe fn into_first_child(this: Self) -> NodeOwned<K, V, marker::Generic> {
        let height = this.height - 1;
        let mut child = unsafe {
            let child_ptr = (*this.as_ptr()).children[0].assume_init_read();
            Self::drop(this);
            NodeOwned::from_raw(child_ptr, height)
        };
        child.clear_parent();
        child
    }
}

impl<K, V> NodeRef<'_, K, V, marker::Internal> {
    fn as_ref(&self) -> &InternalNode<K, V> {
        unsafe { &*self.as_ptr() }
    }
}

impl<K, V> NodeMut<'_, K, V, marker::Internal> {
    fn children_mut(&mut self) -> &mut [MaybeUninit<NodePtr<K, V>>] {
        let len = self.len();
        unsafe { &mut (*self.as_ptr()).children[..len] }
    }

    unsafe fn link_children<I>(&mut self, range: I)
    where
        I: Iterator<Item = usize>,
    {
        for i in range {
            let entry = unsafe {
                Entry::<NodeMut<'_, K, V, marker::Internal>>::new(self.reborrow_mut(), i)
            };
            entry.link_child();
        }
    }

    unsafe fn merge(mut self, mut other: Self) -> Self {
        assert!(self.len() + other.len() <= MAX_KEYS);
        assert!(!self.eq(&other));

        let offset = self.len();
        let new_len = offset + other.len();
        self.common_mut().len = new_len;

        move_to_slice(other.keys_mut(), &mut self.keys_mut()[offset..new_len]);
        move_to_slice(
            other.children_mut(),
            &mut self.children_mut()[offset..new_len],
        );
        unsafe { self.link_children(offset..new_len) };

        self
    }

    unsafe fn steal_from_left(&mut self, other: Self) {
        assert!(other.len() > MIN_KEYS);
        assert!(!self.eq(&other));

        let other_last = other.into_last(false).unwrap_or_else(|_| unreachable!());
        unsafe {
            let mut self_first = self
                .reborrow_mut()
                .into_first()
                .unwrap_or_else(|_| unreachable!());

            let (_, child) = other_last.remove();
            self_first.insert_fit(child);
        }
    }

    unsafe fn steal_from_right(&mut self, other: Self) {
        assert!(other.len() > MIN_KEYS);
        assert!(!self.eq(&other));

        let other_first = other.into_first().unwrap_or_else(|_| unreachable!());
        unsafe {
            let mut self_last = self
                .reborrow_mut()
                .into_last(true)
                .unwrap_or_else(|_| unreachable!());

            let (_, child) = other_first.remove();
            self_last.insert_fit(child);
        }
    }
}

// --------------------------------------------------------
// Generic nodes

impl<B, K, V> Node<B, K, V, marker::Generic> {
    pub fn into_typed(self) -> GenericTypedResult<B, K, V> {
        if self.height == 0 {
            TypedResult::Leaf(Node {
                height: 0,
                common_ptr: self.common_ptr,
                _marker: PhantomData,
            })
        } else {
            TypedResult::Internal(Node {
                height: self.height,
                common_ptr: self.common_ptr,
                _marker: PhantomData,
            })
        }
    }
}

impl<B: marker::BorrowType, K, V> Node<B, K, V, marker::Generic> {
    pub fn ascend(self) -> Result<Entry<Node<B, K, V, marker::Internal>>, Self> {
        let common = self.as_common_ptr();
        unsafe { (*common).parent }
            .map(|parent| Entry {
                node: Node::from(parent, self.height + 1),
                idx: unsafe { (*common).parent_idx.assume_init() },
            })
            .ok_or(self)
    }
}

impl<K, V> Root<K, V> {
    pub fn new() -> Self {
        NodeOwned::<K, V, marker::Leaf>::new().into_generic()
    }

    unsafe fn from_raw(common_ptr: NodePtr<K, V>, height: usize) -> Self {
        Node {
            height,
            common_ptr,
            _marker: PhantomData,
        }
    }

    pub fn drop(this: Self) {
        match this.into_typed() {
            TypedResult::Leaf(leaf) => NodeOwned::<K, V, marker::Leaf>::drop(leaf),
            TypedResult::Internal(internal) => NodeOwned::<K, V, marker::Internal>::drop(internal),
        }
    }

    unsafe fn drop_and_ascend(this: Self) -> Option<Entry<NodeOwned<K, V, marker::Generic>>> {
        unsafe {
            let parent = this.common_ptr.as_ref().parent;
            let idx = this.common_ptr.as_ref().parent_idx;
            let height = this.height;
            Self::drop(this);

            parent.map(|ptr| Entry {
                node: NodeOwned {
                    height,
                    common_ptr: NonNull::from(&ptr.as_ref().common),
                    _marker: PhantomData,
                },
                idx: idx.assume_init(),
            })
        }
    }
}

impl<'a, K: 'a, V: 'a> NodeMut<'a, K, V, marker::Generic> {
    unsafe fn into_leaf_unchecked(self) -> NodeMut<'a, K, V, marker::Leaf> {
        debug_assert!(self.height == 0);
        NodeMut {
            height: 0,
            common_ptr: self.common_ptr,
            _marker: PhantomData,
        }
    }

    unsafe fn into_internal_unchecked(self) -> NodeMut<'a, K, V, marker::Internal> {
        debug_assert!(self.height > 0);
        NodeMut {
            height: self.height,
            common_ptr: self.common_ptr,
            _marker: PhantomData,
        }
    }

    /// # Safety
    ///
    /// We here duplicate a mutable reference which is extremely dangerous. Be sure not to split
    /// them into different contexts.
    unsafe fn into_siblings(self) -> Result<Twin<(Self, Self)>, Self> {
        match unsafe { ptr::read(&self) }.ascend() {
            Ok(ent) => match ent.into_sibling() {
                Ok(Left(sib)) => Ok(Left((sib.descend(), self))),
                Ok(Right(sib)) => Ok(Right((self, sib.descend()))),
                Err(_) => unreachable!("Empty node"),
            },
            Err(root) => Err(root),
        }
    }

    unsafe fn merge(self, other: Self) -> Self {
        assert!(self.len() + other.len() <= MAX_KEYS);
        assert!(!self.eq(&other));

        unsafe {
            match self.into_typed() {
                TypedResult::Leaf(leaf) => leaf.merge(other.into_leaf_unchecked()).into_generic(),
                TypedResult::Internal(internal) => internal
                    .merge(other.into_internal_unchecked())
                    .into_generic(),
            }
        }
    }

    unsafe fn steal_from_left(&mut self, other: Self) {
        unsafe {
            match self.reborrow_mut().into_typed() {
                TypedResult::Leaf(mut leaf) => leaf.steal_from_left(other.into_leaf_unchecked()),
                TypedResult::Internal(mut internal) => {
                    internal.steal_from_left(other.into_internal_unchecked())
                }
            }
        }
    }

    unsafe fn steal_from_right(&mut self, other: Self) {
        unsafe {
            match self.reborrow_mut().into_typed() {
                TypedResult::Leaf(mut leaf) => leaf.steal_from_right(other.into_leaf_unchecked()),
                TypedResult::Internal(mut internal) => {
                    internal.steal_from_right(other.into_internal_unchecked())
                }
            }
        }
    }
}

// --------------------------------------------------------
// Auxiliary items

pub enum TypedResult<Leaf, Internal> {
    Leaf(Leaf),
    Internal(Internal),
}
pub type GenericTypedResult<B, K, V> =
    TypedResult<Node<B, K, V, marker::Leaf>, Node<B, K, V, marker::Internal>>;

enum Twin<T> {
    Left(T),
    Right(T),
}
use alloc::boxed::Box;
use Twin::*;

impl Twin<usize> {
    fn new(idx: usize) -> (usize, Self) {
        match idx {
            0..MIN_KEYS => (MIN_KEYS - 1, Left(idx)),
            MIN_KEYS..=MAX_KEYS => (MIN_KEYS, Right(idx - MIN_KEYS)),
            _ => unreachable!(),
        }
    }
}

fn into_ok_or_err<T>(res: Result<T, T>) -> T {
    match res {
        Ok(x) => x,
        Err(x) => x,
    }
}

// --------------------------------------------------------
// --------------------------------------------------------
// Entry

#[derive(Debug)]
pub struct Entry<Node> {
    node: Node,
    idx: usize,
}

impl<Node: Copy> Copy for Entry<Node> {}
// We don't need the full generality of `#[derive(Clone)]`, as the only time `Node` will be
// `Clone`able is when it is an immutable reference and therefore `Copy`.
impl<Node: Copy> Clone for Entry<Node> {
    fn clone(&self) -> Self {
        *self
    }
}

// --------------------------------------------------------
// Unspecified entries

impl<B, K, V, N> PartialEq for Entry<Node<B, K, V, N>> {
    fn eq(&self, other: &Self) -> bool {
        self.node.eq(&other.node) && self.idx == other.idx
    }
}

impl<B, K, V, N> Entry<Node<B, K, V, N>> {
    pub fn reborrow(&self) -> Entry<NodeRef<'_, K, V, N>> {
        Entry {
            node: self.node.reborrow(),
            idx: self.idx,
        }
    }

    fn into_generic(self) -> Entry<Node<B, K, V, marker::Generic>> {
        Entry {
            node: self.node.into_generic(),
            idx: self.idx,
        }
    }

    fn into_sibling(self) -> Result<Twin<Self>, Self> {
        if self.idx > 0 {
            Ok(Left(Entry {
                node: self.node,
                idx: self.idx - 1,
            }))
        } else if self.idx < self.node.len() - 1 {
            Ok(Right(Entry {
                node: self.node,
                idx: self.idx + 1,
            }))
        } else {
            Err(self)
        }
    }

    fn into_prev(self) -> Result<Self, Self> {
        if self.idx > 0 {
            Ok(Entry {
                node: self.node,
                idx: self.idx - 1,
            })
        } else {
            Err(self)
        }
    }

    fn into_next(self, additive: bool) -> Result<Self, Self> {
        let limit = if additive {
            self.node.len()
        } else {
            self.node.len() - 1
        };
        if self.idx < limit {
            Ok(Entry {
                node: self.node,
                idx: self.idx + 1,
            })
        } else {
            Err(self)
        }
    }
}

impl<K, V, N> Entry<NodeMut<'_, K, V, N>> {
    /// # Safety
    ///
    /// Because mutable pointers can roam anywhere around the tree, the returned
    /// pointer can easily be used to make the original pointer dangling, out of
    /// bounds, or invalid under stacked borrow rules.
    pub unsafe fn reborrow_mut(&mut self) -> Entry<NodeMut<'_, K, V, N>> {
        unsafe {
            Entry {
                node: self.node.reborrow_mut(),
                idx: self.idx,
            }
        }
    }

    fn update_key(&mut self) {
        let mut key = self.node.reborrow().max_key();
        let mut node = unsafe { self.reborrow_mut() }.node.into_generic();
        loop {
            (node, key) = match node.ascend() {
                Ok(mut ent) => {
                    ent.node.keys_mut()[ent.idx].write(ManuallyDrop::into_inner(key));
                    if ent.idx == ent.node.len() - 1 {
                        let key = ent.node.reborrow().max_key();
                        (ent.node.into_generic(), key)
                    } else {
                        break;
                    }
                }
                Err(_) => {
                    break;
                }
            }
        }
    }
}

// --------------------------------------------------------
// Leaf entries

impl<B, K, V> Entry<Node<B, K, V, marker::Leaf>> {
    /// # Safety
    ///
    /// The caller must ensure that `idx < node.len()`.
    pub unsafe fn new(node: Node<B, K, V, marker::Leaf>, idx: usize) -> Self {
        debug_assert!(idx <= node.len());

        Entry { node, idx }
    }

    pub fn next(self) -> Result<Self, Self> {
        self.into_next(false).or_else(|ent| {
            if let Some(next) = ent.node.reborrow().as_ref().next {
                let next = unsafe { next.as_ref() };
                Ok(Entry {
                    node: Node {
                        height: ent.node.height,
                        common_ptr: NonNull::from(&next.common),
                        _marker: PhantomData,
                    },
                    idx: 0,
                })
            } else {
                Err(ent)
            }
        })
    }

    pub fn prev(self) -> Result<Self, Self> {
        self.into_prev().or_else(|ent| {
            if let Some(prev) = ent.node.reborrow().as_ref().prev {
                let prev = unsafe { prev.as_ref() };
                Ok(Entry {
                    node: Node {
                        height: ent.node.height,
                        common_ptr: NonNull::from(&prev.common),

                        _marker: PhantomData,
                    },
                    idx: prev.common.len - 1,
                })
            } else {
                Err(ent)
            }
        })
    }

    pub fn into_kv_ptr(self) -> (*const K, *mut V) {
        unsafe {
            let key = (*self.node.as_common_ptr()).keys[self.idx].as_ptr();
            let val = (*self.node.as_ptr()).vals[self.idx].as_mut_ptr();

            (key, val)
        }
    }

    pub fn into_non_additive(self) -> Option<Self> {
        if self.idx == self.node.len() {
            if let Some(next) = self.node.reborrow().as_ref().next {
                let next = unsafe { next.as_ref() };
                Some(Entry {
                    node: Node {
                        height: self.node.height,
                        common_ptr: NonNull::from(&next.common),
                        _marker: PhantomData,
                    },
                    idx: 0,
                })
            } else {
                None
            }
        } else {
            Some(self)
        }
    }
}

impl<K, V> Entry<NodeOwned<K, V, marker::Leaf>> {
    pub unsafe fn drop_next(this: Self, back: bool) -> (Option<Self>, Option<(K, V)>) {
        unsafe {
            let kv = ptr::read(&this).into_kv();
            let next = if back {
                let ret = ptr::read(&this).prev().ok();
                Self::drop_ancestors_back(this);
                ret
            } else {
                let ret = ptr::read(&this).next().ok();
                Self::drop_ancestors(this);
                ret
            };
            (next, Some(kv))
        }
    }

    unsafe fn drop_ancestors(this: Self) {
        let mut ent = this.into_generic();
        if ent.idx == ent.node.len() - 1 {
            loop {
                ent = match unsafe { NodeOwned::drop_and_ascend(ent.node) } {
                    Some(ent) if ent.idx == ent.node.len() - 1 => ent,
                    _ => break,
                }
            }
        }
    }

    unsafe fn drop_ancestors_back(this: Self) {
        let mut ent = this.into_generic();
        if ent.idx == 0 {
            loop {
                ent = match unsafe { NodeOwned::drop_and_ascend(ent.node) } {
                    Some(ent) if ent.idx == 0 => ent,
                    _ => break,
                }
            }
        }
    }

    unsafe fn into_kv(self) -> (K, V) {
        unsafe {
            let key = (*self.node.as_common_ptr()).keys[self.idx].assume_init_read();
            let val = (*self.node.as_ptr()).vals[self.idx].assume_init_read();
            (key, val)
        }
    }
}

impl<'a, K, V> Entry<NodeRef<'a, K, V, marker::Leaf>> {
    pub fn into_kv(self) -> (&'a K, &'a V) {
        let node_ptr = self.node.as_ptr();
        unsafe {
            let key = (*node_ptr)
                .common
                .keys
                .get_unchecked(self.idx)
                .assume_init_ref();
            let val = (*node_ptr).vals.get_unchecked(self.idx).assume_init_ref();
            (key, val)
        }
    }
}

impl<'a, K, V> Entry<NodeMut<'a, K, V, marker::Leaf>> {
    pub fn val_mut(&mut self) -> &mut V {
        unsafe { self.node.vals_mut()[self.idx].assume_init_mut() }
    }

    // pub fn into_kv_mut(self) -> (&'a K, &'a mut V) {
    //       let node_ptr = self.node.as_ptr();
    //       unsafe {
    //             let key = (*node_ptr)
    //                   .common
    //                   .keys
    //                   .get_unchecked(self.idx)
    //                   .assume_init_ref();
    //             let val = (*node_ptr)
    //                   .vals
    //                   .get_unchecked_mut(self.idx)
    //                   .assume_init_mut();
    //             (key, val)
    //       }
    // }

    unsafe fn split_data(&mut self, other: &mut LeafNode<K, V>) -> ManuallyDrop<K> {
        debug_assert!(self.node.len() == MAX_KEYS);
        let self_len = self.idx;
        let other_len = MAX_KEYS - self.idx;

        let key = unsafe { self.node.keys_mut()[self.idx].assume_init_read() };

        move_to_slice(
            &self.node.keys_mut()[self_len..MAX_KEYS],
            &mut other.common.keys[..other_len],
        );
        move_to_slice(
            &self.node.vals_mut()[self_len..MAX_KEYS],
            &mut other.vals[..other_len],
        );
        self.node.common_mut().len = self_len;
        other.common.len = other_len;

        unsafe {
            let self_ptr = Some(NonNull::new_unchecked(self.node.as_ptr()));
            let other_ptr = Some(NonNull::new_unchecked(other as *mut _));
            let self_mut = self.node.as_mut();
            other.next = self_mut.next;
            other.prev = self_ptr;
            self_mut.next = other_ptr;
            if let Some(mut next) = other.next {
                next.as_mut().prev = other_ptr;
            }
        }

        ManuallyDrop::new(key)
    }

    unsafe fn split(mut self) -> SplitResult<'a, K, V, marker::Leaf> {
        debug_assert!(self.node.len() == MAX_KEYS);

        let mut other = LeafNode::new();
        let key = unsafe { self.split_data(&mut other) };

        self.update_key();

        let right = NodeOwned::<K, V, marker::Leaf>::from_new(other);
        SplitResult {
            key,
            left: self.node,
            right,
        }
    }

    unsafe fn insert_fit(&mut self, key: K, val: V) -> *mut V {
        debug_assert!(self.node.len() < MAX_KEYS);
        self.node.common_mut().len += 1;

        unsafe {
            slice_insert(self.node.keys_mut(), self.idx, key);
            slice_insert(self.node.vals_mut(), self.idx, val);
        }

        self.update_key();

        self.node.vals_mut()[self.idx].as_mut_ptr()
    }

    fn insert(self, key: K, val: V) -> (InsertResult<'a, K, V, marker::Leaf>, *mut V) {
        if self.node.len() < MAX_KEYS {
            let mut ent = self;
            let val_ptr = unsafe { ent.insert_fit(key, val) };
            (InsertResult::Fit(ent), val_ptr)
        } else {
            let (mid, ty) = Twin::new(self.idx);
            let mid_entry = Entry {
                node: self.node,
                idx: mid,
            };
            let mut res = unsafe { mid_entry.split() };
            let mut cond = match ty {
                Left(idx) => Entry {
                    node: unsafe { res.left.reborrow_mut() },
                    idx,
                },
                Right(idx) => Entry {
                    node: res.right.borrow_mut(),
                    idx,
                },
            };
            let val_ptr = unsafe { cond.insert_fit(key, val) };
            (InsertResult::Split(res), val_ptr)
        }
    }

    pub fn insert_recursive(
        self,
        key: K,
        val: V,
    ) -> (InsertResult<'a, K, V, marker::Generic>, *mut V) {
        let (mut split, val_ptr) = match self.insert(key, val) {
            (InsertResult::Fit(ent), val_ptr) => {
                return (InsertResult::Fit(ent.into_generic()), val_ptr)
            }
            (InsertResult::Split(split), val_ptr) => (split.into_generic(), val_ptr),
        };

        loop {
            split = match split.left.ascend() {
                Ok(ent) => match into_ok_or_err(ent.into_next(true)).insert(split.right.common_ptr)
                {
                    InsertResult::Fit(ent) => {
                        return (InsertResult::Fit(ent.into_generic()), val_ptr)
                    }
                    InsertResult::Split(split) => split.into_generic(),
                },
                Err(root) => {
                    return (
                        InsertResult::Split(SplitResult {
                            left: root,
                            ..split
                        }),
                        val_ptr,
                    )
                }
            }
        }
    }

    fn remove(mut self) -> (RemoveResult<'a, K, V, marker::Leaf>, (K, V)) {
        let kv = unsafe {
            let key = slice_remove(self.node.keys_mut(), self.idx);
            let val = slice_remove(self.node.vals_mut(), self.idx);
            (key, val)
        };
        self.node.common_mut().len -= 1;

        if self.node.len() >= MIN_KEYS {
            self.update_key();
            (RemoveResult::Fit, kv)
        } else {
            (RemoveResult::Attach(self), kv)
        }
    }

    pub fn into_val_mut(self) -> &'a mut V {
        let node_ptr = self.node.as_ptr();
        unsafe {
            (*node_ptr)
                .vals
                .get_unchecked_mut(self.idx)
                .assume_init_mut()
        }
    }
}

impl<'a, K: 'a, V: 'a> Entry<NodeMut<'a, K, V, marker::Leaf>> {
    pub fn remove_recursive(self) -> (RemoveResult<'a, K, V, marker::Generic>, (K, V)) {
        let (mut ent, kv) = match self.remove() {
            (RemoveResult::Fit, kv) => return (RemoveResult::Fit, kv),
            (RemoveResult::Attach(ent), kv) => (ent.into_generic(), kv),
        };

        loop {
            ent = match unsafe { ent.attach_and_ascend() } {
                Ok(None) => return (RemoveResult::Fit, kv),
                Ok(Some(parent)) => {
                    let height = parent.node.height;
                    let (res, child) = parent.remove();
                    Root::drop(unsafe { Root::from_raw(child, height - 1) });
                    match res {
                        RemoveResult::Fit => return (RemoveResult::Fit, kv),
                        RemoveResult::Attach(ent) => ent.into_generic(),
                    }
                }
                Err(ent) => return (RemoveResult::Attach(ent), kv),
            }
        }
    }
}

// --------------------------------------------------------
// Internal entries

impl<B, K, V> Entry<Node<B, K, V, marker::Internal>> {
    /// # Safety
    ///
    /// The caller must ensure that `idx < node.len()`.
    pub unsafe fn new(node: Node<B, K, V, marker::Internal>, idx: usize) -> Self {
        debug_assert!(idx < node.len());

        Entry { node, idx }
    }
}

impl<B: marker::BorrowType, K, V> Entry<Node<B, K, V, marker::Internal>> {
    pub fn descend(self) -> Node<B, K, V, marker::Generic> {
        let ptr = self.node.as_ptr();
        let child = unsafe { (*ptr).children[self.idx].assume_init_read() };
        Node {
            height: self.node.height - 1,
            common_ptr: child,
            _marker: PhantomData,
        }
    }
}

impl<'a, K, V> Entry<NodeMut<'a, K, V, marker::Internal>> {
    fn link_child(self) {
        let parent = unsafe { NonNull::new_unchecked(self.node.as_ptr()) };
        let idx = self.idx;
        self.descend().set_parent(parent, idx);
    }

    unsafe fn split_data(&mut self, other: &mut InternalNode<K, V>) -> ManuallyDrop<K> {
        debug_assert!(self.node.len() == MAX_KEYS);
        let self_len = self.idx;
        let other_len = MAX_KEYS - self.idx;

        let key = unsafe { self.node.keys_mut()[self.idx].assume_init_read() };

        move_to_slice(
            &self.node.keys_mut()[self_len..MAX_KEYS],
            &mut other.common.keys[..other_len],
        );
        move_to_slice(
            &self.node.children_mut()[self_len..MAX_KEYS],
            &mut other.children[..other_len],
        );
        self.node.common_mut().len = self_len;
        other.common.len = other_len;

        ManuallyDrop::new(key)
    }

    unsafe fn split(mut self) -> SplitResult<'a, K, V, marker::Internal> {
        debug_assert!(self.node.len() == MAX_KEYS);

        unsafe {
            let mut other = InternalNode::new();
            let key = self.split_data(&mut other);

            self.update_key();

            let mut right = NodeOwned::<K, V, marker::Internal>::from_new(
                other,
                NonZeroUsize::new_unchecked(self.node.height),
            );
            let right_len = right.len();
            right.borrow_mut().link_children(0..right_len);

            SplitResult {
                key,
                left: self.node,
                right,
            }
        }
    }

    unsafe fn insert_fit(&mut self, child: NodePtr<K, V>) {
        debug_assert!(self.node.len() < MAX_KEYS);
        let key = NodeRef::<'_, K, V, marker::Generic> {
            common_ptr: child,
            height: self.node.height - 1,
            _marker: PhantomData,
        }
        .max_key();
        self.node.common_mut().len += 1;

        unsafe {
            slice_insert(
                self.node.keys_mut(),
                self.idx,
                ManuallyDrop::into_inner(key),
            );
            slice_insert(self.node.children_mut(), self.idx, child);
            self.node.link_children(self.idx..self.node.len());
        }

        self.update_key();
    }

    fn insert(self, child: NodePtr<K, V>) -> InsertResult<'a, K, V, marker::Internal> {
        if self.node.len() < MAX_KEYS {
            let mut ent = self;
            unsafe { ent.insert_fit(child) };
            InsertResult::Fit(ent)
        } else {
            let (mid, ty) = Twin::new(self.idx);
            let mid_entry = Entry {
                node: self.node,
                idx: mid,
            };
            let mut res = unsafe { mid_entry.split() };
            let mut cond = match ty {
                Left(idx) => Entry {
                    node: unsafe { res.left.reborrow_mut() },
                    idx,
                },
                Right(idx) => Entry {
                    node: res.right.borrow_mut(),
                    idx,
                },
            };
            unsafe { cond.insert_fit(child) };
            InsertResult::Split(res)
        }
    }

    #[allow(clippy::type_complexity)]
    fn remove(mut self) -> (RemoveResult<'a, K, V, marker::Internal>, NodePtr<K, V>) {
        let child = unsafe {
            let key = slice_remove(self.node.keys_mut(), self.idx);
            core::mem::forget(key);
            let child = slice_remove(self.node.children_mut(), self.idx);

            self.node.common_mut().len -= 1;
            self.node.link_children(0..self.node.len());

            child
        };

        if self.node.len() >= MIN_KEYS {
            self.update_key();
            (RemoveResult::Fit, child)
        } else {
            (RemoveResult::Attach(self), child)
        }
    }
}

// --------------------------------------------------------
// Generic nodes

impl<'a, K: 'a, V: 'a> Entry<NodeMut<'a, K, V, marker::Generic>> {
    #[allow(clippy::type_complexity)]
    unsafe fn attach_and_ascend(
        self,
    ) -> Result<Option<Entry<NodeMut<'a, K, V, marker::Internal>>>, Self> {
        assert!(self.node.len() < MIN_KEYS);
        let Entry { node, idx } = self;
        // SAFE: One of the 2 node refs is dropped either after `update_key` or in `merge`.
        unsafe {
            match node.into_siblings() {
                Ok(Left((other, mut this))) => Ok(if other.len() + this.len() <= MAX_KEYS {
                    other
                        .merge(this.reborrow_mut())
                        .into_last(false)
                        .unwrap_or_else(|_| unreachable!())
                        .update_key();
                    this.ascend().ok()
                } else {
                    this.steal_from_left(other);
                    None
                }),
                Ok(Right((mut this, mut other))) => Ok(if other.len() + this.len() <= MAX_KEYS {
                    this.merge(other.reborrow_mut())
                        .into_last(false)
                        .unwrap_or_else(|_| unreachable!())
                        .update_key();
                    other.ascend().ok()
                } else {
                    this.steal_from_right(other);
                    None
                }),
                Err(root) => Err(Entry { node: root, idx }),
            }
        }
    }
}

// --------------------------------------------------------
// Auxiliary items

pub unsafe fn insert_root<K, V>(
    self_ptr: *mut super::BpTreeMap<K, V>,
    node: NodeOwned<K, V, marker::Generic>,
) {
    let map = unsafe { &mut *self_ptr };

    let root = map.root.as_mut().unwrap();
    crate::mem::take_mut(root, |root| {
        NodeOwned::<K, V, marker::Internal>::new(root).into_generic()
    });

    let ret = Entry {
        node: unsafe { root.borrow_mut().into_internal_unchecked() },
        idx: 1,
    }
    .insert(node.common_ptr);
    assert!(matches!(ret, InsertResult::Fit(_)));

    map.len += 1;
}

pub fn remove_with_root<K, V>(
    this: Entry<NodeMut<'_, K, V, marker::Leaf>>,
    self_ptr: *mut super::BpTreeMap<K, V>,
) -> Option<(K, V)> {
    match this.remove_recursive() {
        (RemoveResult::Fit, kv) => {
            unsafe {
                let map = &mut *self_ptr;
                map.len -= 1;
            }
            Some(kv)
        }
        (RemoveResult::Attach(_), kv) => {
            unsafe {
                let map = &mut *self_ptr;
                map.len -= 1;

                if map.len == 0 {
                    let root = map.root.take().unwrap();
                    NodeOwned::<K, V, marker::Generic>::drop(root);
                } else {
                    let root = map.root.as_mut().unwrap();
                    crate::mem::take_mut(root, |root| {
                        NodeOwned::into_first_child(match root.into_typed() {
                            TypedResult::Leaf(leaf) => return leaf.into_generic(),
                            TypedResult::Internal(internal) if internal.len() > 1 => {
                                return internal.into_generic()
                            }
                            TypedResult::Internal(internal) => internal,
                        })
                    });
                }
            }
            Some(kv)
        }
    }
}

pub struct SplitResult<'a, K, V, N> {
    pub key: ManuallyDrop<K>,
    pub left: NodeMut<'a, K, V, N>,
    pub right: NodeOwned<K, V, N>,
}

impl<'a, K, V, N> SplitResult<'a, K, V, N> {
    fn into_generic(self) -> SplitResult<'a, K, V, marker::Generic> {
        SplitResult {
            key: self.key,
            left: self.left.into_generic(),
            right: self.right.into_generic(),
        }
    }
}

pub enum InsertResult<'a, K, V, N> {
    Fit(Entry<NodeMut<'a, K, V, N>>),
    Split(SplitResult<'a, K, V, N>),
}

pub enum RemoveResult<'a, K, V, N> {
    Fit,
    Attach(Entry<NodeMut<'a, K, V, N>>),
}

pub mod marker {
    use core::marker::PhantomData;

    pub trait BorrowType {
        const PERMITS_TRAVERSAL: bool = true;
    }

    #[derive(Debug)]
    pub struct Owned;
    #[derive(Debug)]
    pub struct Ref<'a>(PhantomData<&'a ()>);
    #[derive(Debug)]
    pub struct Mut<'a>(PhantomData<&'a mut ()>);

    impl BorrowType for Owned {
        const PERMITS_TRAVERSAL: bool = false;
    }
    impl BorrowType for Ref<'_> {}
    impl BorrowType for Mut<'_> {}

    #[derive(Debug)]
    pub struct Internal {}
    #[derive(Debug)]
    pub struct Leaf {}
    #[derive(Debug)]
    pub struct Generic {}
}

/// Inserts a value into a slice of initialized elements followed by one uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
unsafe fn slice_insert<T>(slice: &mut [MaybeUninit<T>], idx: usize, val: T) {
    let len = slice.len();
    debug_assert!(len > idx);
    let slice_ptr = slice.as_mut_ptr();
    unsafe {
        if len > idx + 1 {
            ptr::copy(slice_ptr.add(idx), slice_ptr.add(idx + 1), len - idx - 1);
        }
        (*slice_ptr.add(idx)).write(val);
    }
}

/// Removes and returns a value from a slice of all initialized elements, leaving behind one
/// trailing uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
unsafe fn slice_remove<T>(slice: &mut [MaybeUninit<T>], idx: usize) -> T {
    let len = slice.len();
    debug_assert!(idx < len);
    let slice_ptr = slice.as_mut_ptr();
    unsafe {
        let ret = (*slice_ptr.add(idx)).assume_init_read();
        ptr::copy(slice_ptr.add(idx + 1), slice_ptr.add(idx), len - idx - 1);
        ret
    }
}

/// Moves all values from a slice of initialized elements to a slice
/// of uninitialized elements, leaving behind `src` as all uninitialized.
/// Works like `dst.copy_from_slice(src)` but does not require `T` to be `Copy`.
fn move_to_slice<T>(src: &[MaybeUninit<T>], dst: &mut [MaybeUninit<T>]) {
    assert!(src.len() == dst.len());
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
}
