use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ops::{Bound, RangeBounds};
use core::ptr;

use super::super::mem;
use super::node::*;

impl<B, K, V, N> Node<B, K, V, N> {
    fn get_index<Q: ?Sized>(&self, key: &Q, start_idx: usize) -> IndexResult
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        let node = self.reborrow();
        let len = self.len();
        assert!(start_idx <= len);
        let keys = node.keys();
        keys.iter()
            .enumerate()
            .skip(start_idx)
            .find_map(|(idx, k)| match key.cmp(k.borrow()) {
                Ordering::Less => Some(IndexResult::Vacant(idx)),
                Ordering::Equal => Some(IndexResult::Occupied(idx)),
                Ordering::Greater => None,
            })
            .unwrap_or(IndexResult::Vacant(len))
    }
}

impl<B, K, V> Node<B, K, V, marker::Leaf> {
    pub fn search_node<Q: ?Sized>(self, key: &Q) -> SearchResult<Node<B, K, V, marker::Leaf>>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        match self.get_index(key, 0) {
            IndexResult::Occupied(idx) => SearchResult::Occupied(unsafe {
                Entry::<Node<B, K, V, marker::Leaf>>::new(self, idx)
            }),
            IndexResult::Vacant(idx) => SearchResult::Vacant(unsafe {
                Entry::<Node<B, K, V, marker::Leaf>>::new(self, idx)
            }),
        }
    }
}

impl<B: marker::BorrowType, K, V> Node<B, K, V, marker::Internal> {
    pub fn search_node<Q: ?Sized>(self, key: &Q) -> Node<B, K, V, marker::Generic>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        let idx = self.get_index(key, 0).into_idx();
        let idx = if idx == self.len() { idx - 1 } else { idx };
        unsafe { Entry::<Node<B, K, V, marker::Internal>>::new(self, idx) }.descend()
    }
}

impl<B: marker::BorrowType, K, V> Node<B, K, V, marker::Generic> {
    pub fn search_tree<Q: ?Sized>(self, key: &Q) -> SearchResult<Node<B, K, V, marker::Leaf>>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        let mut node = self;
        loop {
            node = match node.into_typed() {
                TypedResult::Leaf(node) => break node.search_node(key),
                TypedResult::Internal(node) => node.search_node(key),
            }
        }
    }

    pub fn bound<Q: ?Sized>(
        self,
        bound: Bound<&Q>,
        lower: bool,
    ) -> Option<Entry<Node<B, K, V, marker::Leaf>>>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        let key = match bound {
            Bound::Unbounded => {
                return Some(if lower {
                    self.first_entry()
                } else {
                    self.last_entry(false)
                })
            }
            Bound::Included(key) => key,
            Bound::Excluded(key) => key,
        };

        let ent = match self.search_tree(key) {
            SearchResult::Occupied(ent) => ent,
            SearchResult::Vacant(ent) => ent,
        }
        .into_non_additive();
        match bound {
            Bound::Unbounded => unreachable!(),
            Bound::Included(_) => ent,
            Bound::Excluded(_) => {
                ent.and_then(|ent| if lower { ent.next() } else { ent.prev() }.ok())
            }
        }
    }

    pub fn first_entry(self) -> Entry<Node<B, K, V, marker::Leaf>> {
        let mut node = self;
        loop {
            node = match node.into_typed() {
                TypedResult::Leaf(node) => {
                    break node.into_first().unwrap_or_else(|_| unreachable!())
                }
                TypedResult::Internal(node) => node
                    .into_first()
                    .unwrap_or_else(|_| unreachable!())
                    .descend(),
            }
        }
    }

    pub fn last_entry(self, additive: bool) -> Entry<Node<B, K, V, marker::Leaf>> {
        let mut node = self;
        loop {
            node = match node.into_typed() {
                TypedResult::Leaf(node) => {
                    break node.into_last(additive).unwrap_or_else(|_| unreachable!())
                }
                TypedResult::Internal(node) => node
                    .into_last(false)
                    .unwrap_or_else(|_| unreachable!())
                    .descend(),
            }
        }
    }
}

#[cfg(test)]
impl<B, K: core::fmt::Debug, V: core::fmt::Debug> Node<B, K, V, marker::Leaf> {
    fn print_node(&self) {
        // println!("{:#?}", self);
    }
}

#[cfg(test)]
impl<B, K: core::fmt::Debug, V: core::fmt::Debug> Node<B, K, V, marker::Internal> {
    fn print_node(&self) {
        // println!("{:#?}", self);
        for i in 0..self.len() {
            let child =
                unsafe { Entry::<NodeRef<'_, K, V, marker::Internal>>::new(self.reborrow(), i) }
                    .descend();
            match child.into_typed() {
                TypedResult::Leaf(leaf) => leaf.print_node(),
                TypedResult::Internal(internal) => internal.print_node(),
            }
        }
    }
}

#[cfg(test)]
impl<B, K: core::fmt::Debug, V: core::fmt::Debug> Node<B, K, V, marker::Generic> {
    pub fn print_tree(&self) {
        match self.reborrow().into_typed() {
            TypedResult::Leaf(leaf) => leaf.print_node(),
            TypedResult::Internal(internal) => internal.print_node(),
        }
    }
}

pub struct IterImpl<Node> {
    front: Option<Entry<Node>>,
    back: Option<Entry<Node>>,
}

impl<Node: Copy> Copy for IterImpl<Node> {}
impl<Node: Copy> Clone for IterImpl<Node> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Node> IterImpl<Node> {
    pub fn new(front: Entry<Node>, back: Entry<Node>) -> Self {
        IterImpl {
            front: Some(front),
            back: Some(back),
        }
    }

    pub fn none() -> Self {
        IterImpl {
            front: None,
            back: None,
        }
    }
}

impl<B: marker::BorrowType, K, V> IterImpl<Node<B, K, V, marker::Leaf>> {
    pub fn range<Q: ?Sized, R>(root_node: Node<B, K, V, marker::Generic>, range: R) -> Self
    where
        R: RangeBounds<Q>,
        Q: Ord,
        K: Borrow<Q>,
    {
        let start = match unsafe { ptr::read(&root_node) }.bound(range.start_bound(), true) {
            Some(start) => start,
            None => return Self::none(),
        };
        let end = match root_node.bound(range.end_bound(), false) {
            Some(end) => end,
            None => return Self::none(),
        };
        Self::new(start, end)
    }
}

impl<B, K, V> IterImpl<Node<B, K, V, marker::Leaf>> {
    pub fn reborrow(&self) -> IterImpl<NodeRef<'_, K, V, marker::Leaf>> {
        IterImpl {
            front: self.front.as_ref().map(|front| front.reborrow()),
            back: self.back.as_ref().map(|back| back.reborrow()),
        }
    }

    pub fn next(&mut self) -> Option<(*const K, *mut V)> {
        mem::replace(&mut self.front, |front| {
            front.map_or((None, None), |front| {
                let next = Some(unsafe { ptr::read(&front) })
                    .filter(|front| Some(front) != self.back.as_ref())
                    .and_then(|front| front.next().ok());
                (next, Some(front.into_kv_ptr()))
            })
        })
    }

    pub fn prev(&mut self) -> Option<(*const K, *mut V)> {
        mem::replace(&mut self.back, |back| {
            back.map_or((None, None), |back| {
                let prev = Some(unsafe { ptr::read(&back) })
                    .filter(|back| Some(back) != self.front.as_ref())
                    .and_then(|front| front.prev().ok());
                (prev, Some(back.into_kv_ptr()))
            })
        })
    }
}

impl<K, V> IterImpl<NodeOwned<K, V, marker::Leaf>> {
    pub unsafe fn dying_next(&mut self) -> Option<(K, V)> {
        mem::replace(&mut self.front, |front| {
            front.map_or((None, None), |front| Entry::drop_next(front, false))
        })
    }

    pub unsafe fn dying_prev(&mut self) -> Option<(K, V)> {
        mem::replace(&mut self.back, |back| {
            back.map_or((None, None), |back| Entry::drop_next(back, true))
        })
    }
}

pub enum IndexResult {
    Occupied(usize),
    Vacant(usize),
}

impl IndexResult {
    pub fn into_idx(self) -> usize {
        match self {
            IndexResult::Occupied(idx) => idx,
            IndexResult::Vacant(idx) => idx,
        }
    }
}

pub enum SearchResult<Node> {
    Occupied(Entry<Node>),
    Vacant(Entry<Node>),
}
