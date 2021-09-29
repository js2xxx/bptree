mod node;
mod search;

use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter::FusedIterator;
use core::mem::{self, ManuallyDrop};
use core::ops::RangeBounds;
use core::ptr;

use node::Root;

pub struct BpTreeMap<K, V> {
    root: Option<Root<K, V>>,
    len: usize,
}

impl<K, V> Default for BpTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> BpTreeMap<K, V> {
    pub const fn new() -> Self {
        BpTreeMap { root: None, len: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn owned_root(root: &mut Option<Root<K, V>>) -> &mut Root<K, V> {
        root.get_or_insert_with(Root::new)
    }
}

impl<K, V> Clone for BpTreeMap<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    fn clone(&self) -> Self {
        // TODO: Write direct methods for cloning.
        let mut ret = Self::new();
        for (k, v) in self.iter().map(|(k, v)| (k.clone(), v.clone())) {
            ret.insert(k, v);
        }
        ret
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for BpTreeMap<K, V>
where
    K: Ord,
{
    fn from(arr: [(K, V); N]) -> Self {
        let mut ret = Self::new();
        // TOOD: Sort the array and use direct inserting methods to build the tree.
        for (k, v) in arr {
            ret.insert(k, v);
        }
        ret
    }
}

impl<K, V> BpTreeMap<K, V> {
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V>
    where
        K: Ord,
    {
        let self_ptr: *mut _ = self;
        let root_node = Self::owned_root(&mut self.root).borrow_mut();
        match root_node.search_tree(&key) {
            search::SearchResult::Occupied(inner) => Entry {
                vacant_key: None,
                inner,
                self_ptr,
            },
            search::SearchResult::Vacant(inner) => Entry {
                vacant_key: Some(key),
                inner,
                self_ptr,
            },
        }
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        self.get_key_value(key).map(|(_, value)| value)
    }

    pub fn get_key_value<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        let root_node = self.root.as_ref()?.reborrow();
        match root_node.search_tree(key) {
            search::SearchResult::Occupied(entry) => Some(entry.into_kv()),
            search::SearchResult::Vacant(_) => None,
        }
    }

    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        self.get(key).is_some()
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        let root_node = self.root.as_mut()?.borrow_mut();
        match root_node.search_tree(key) {
            search::SearchResult::Occupied(entry) => Some(entry.into_val_mut()),
            search::SearchResult::Vacant(_) => None,
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        let mut ent = self.entry(key);
        if let Some(val_mut) = ent.value_mut() {
            let mut ret = value;
            core::mem::swap(val_mut, &mut ret);
            Some(ret)
        } else {
            ent.or_insert(value);
            None
        }
    }

    pub fn append(&mut self, other: &mut Self)
    where
        K: Ord,
    {
        if other.is_empty() {
            return;
        }

        if self.is_empty() {
            mem::swap(self, other);
            return;
        }

        // TODO: Write direct methods for appending.
        for (k, v) in mem::take(other).into_iter() {
            self.insert(k, v);
        }
    }

    pub fn remove_entry<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Q: Ord,
        K: Borrow<Q>,

        Q: core::fmt::Debug,
        K: core::fmt::Debug,
        V: core::fmt::Debug,
    {
        let self_ptr: *mut _ = self;

        let root_node = self.root.as_mut()?.borrow_mut();
        match root_node.search_tree(key) {
            search::SearchResult::Vacant(_) => None,
            search::SearchResult::Occupied(entry) => node::remove_with_root(entry, self_ptr),
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        Q: Ord,
        K: Borrow<Q>,

        Q: core::fmt::Debug,
        K: core::fmt::Debug,
        V: core::fmt::Debug,
    {
        self.remove_entry(key).map(|(_, val)| val)
    }

    pub fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<K, V> BpTreeMap<K, V> {
    pub fn first(&self) -> Option<&V> {
        self.first_key_value().map(|(_, val)| val)
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        let root_node = self.root.as_ref()?.reborrow();
        Some(root_node.first_entry().into_kv())
    }

    pub fn first_entry(&mut self) -> Option<Entry<'_, K, V>> {
        let self_ptr: *mut _ = self;
        let root_node = self.root.as_mut()?.borrow_mut();
        let entry = root_node.first_entry();
        Some(Entry {
            vacant_key: None,
            inner: entry,
            self_ptr,
        })
    }

    pub fn pop_first(&mut self) -> Option<(K, V)> {
        let self_ptr: *mut _ = self;
        let root_node = self.root.as_mut()?.borrow_mut();
        let entry = root_node.first_entry();
        node::remove_with_root(entry, self_ptr)
    }

    pub fn last(&self) -> Option<&V> {
        self.last_key_value().map(|(_, val)| val)
    }

    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        let root_node = self.root.as_ref()?.reborrow();
        Some(root_node.last_entry(false).into_kv())
    }

    pub fn last_entry(&mut self) -> Option<Entry<'_, K, V>> {
        let self_ptr: *mut _ = self;
        let root_node = self.root.as_mut()?.borrow_mut();
        let entry = root_node.last_entry(false);
        Some(Entry {
            vacant_key: None,
            inner: entry,
            self_ptr,
        })
    }

    pub fn pop_last(&mut self) -> Option<(K, V)> {
        let self_ptr: *mut _ = self;
        let root_node = self.root.as_mut()?.borrow_mut();
        let entry = root_node.last_entry(false);
        node::remove_with_root(entry, self_ptr)
    }

    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            iter: self.into_iter(),
        }
    }

    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            iter: self.into_iter(),
        }
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        if let Some(root) = self.root.as_ref() {
            let first_entry = root.reborrow().first_entry();
            let last_entry = root.reborrow().last_entry(false);
            Iter {
                imp: search::IterImpl::new(first_entry, last_entry),
                rem: self.len,
            }
        } else {
            Iter {
                imp: search::IterImpl::none(),
                rem: 0,
            }
        }
    }

    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { iter: self.iter() }
    }

    pub fn values(&self) -> Values<'_, K, V> {
        Values { iter: self.iter() }
    }

    pub fn range<Q: ?Sized, R>(&self, range: R) -> Range<'_, K, V>
    where
        R: RangeBounds<Q>,
        Q: Ord,
        K: Borrow<Q>,
    {
        Range {
            imp: if let Some(root) = self.root.as_ref() {
                let root_node = root.reborrow();
                search::IterImpl::range(root_node, range)
            } else {
                search::IterImpl::none()
            },
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        if let Some(root) = self.root.as_mut() {
            let first_entry = unsafe { ptr::read(&root) }.borrow_mut().first_entry();
            let last_entry = root.borrow_mut().last_entry(false);
            IterMut {
                imp: search::IterImpl::new(first_entry, last_entry),
                rem: self.len,
            }
        } else {
            IterMut {
                imp: search::IterImpl::none(),
                rem: 0,
            }
        }
    }

    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            iter: self.iter_mut(),
        }
    }

    pub fn range_mut<Q: ?Sized, R>(&mut self, range: R) -> RangeMut<'_, K, V>
    where
        R: RangeBounds<Q>,
        Q: Ord,
        K: Borrow<Q>,
    {
        RangeMut {
            imp: if let Some(root) = self.root.as_mut() {
                let root_node = root.borrow_mut();
                search::IterImpl::range(root_node, range)
            } else {
                search::IterImpl::none()
            },
        }
    }
}

impl<K, V> IntoIterator for BpTreeMap<K, V> {
    type Item = (K, V);

    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        let mut me = ManuallyDrop::new(self);
        if let Some(root) = me.root.take() {
            let first = unsafe { ptr::read(&root) }.first_entry();
            let last = root.last_entry(false);
            IntoIter {
                imp: search::IterImpl::new(first, last),
                rem: me.len,
            }
        } else {
            IntoIter {
                imp: search::IterImpl::none(),
                rem: 0,
            }
        }
    }
}

impl<K, V> Debug for BpTreeMap<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> Drop for BpTreeMap<K, V> {
    fn drop(&mut self) {
        drop(unsafe { ptr::read(self) }.into_iter())
    }
}

pub struct Entry<'a, K, V> {
    vacant_key: Option<K>,
    inner: node::Entry<node::NodeMut<'a, K, V, node::marker::Leaf>>,
    self_ptr: *mut BpTreeMap<K, V>,
}

impl<'a, K: Ord, V> Entry<'a, K, V> {
    unsafe fn force_insert(
        inner: node::Entry<node::NodeMut<'a, K, V, node::marker::Leaf>>,
        self_ptr: *mut BpTreeMap<K, V>,
        key: K,
        value: V,
    ) -> &'a mut V {
        match inner.insert_recursive(key, value) {
            (node::InsertResult::Fit(_), val_ptr) => {
                {
                    let map = &mut *self_ptr;
                    map.len += 1;
                }
                &mut *val_ptr
            }
            (node::InsertResult::Split(split), val_ptr) => {
                let node::SplitResult { right, .. } = split;

                node::insert_root(self_ptr, right);
                &mut *val_ptr
            }
        }
    }

    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(|| default)
    }

    pub fn or_insert_with<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        self.or_insert_with_key(|_| default())
    }

    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self.vacant_key {
            None => self.inner.into_val_mut(),
            Some(key) => unsafe {
                let value = default(&key);
                Self::force_insert(self.inner, self.self_ptr, key, value)
            },
        }
    }

    pub fn key(&self) -> &K {
        match &self.vacant_key {
            None => self.inner.reborrow().into_kv().0,
            Some(key) => key,
        }
    }

    fn value_mut(&mut self) -> Option<&mut V> {
        match self.vacant_key {
            None => Some(self.inner.val_mut()),
            Some(_) => None,
        }
    }

    pub fn and_modify<F>(mut self, modify: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self.vacant_key {
            None => {
                modify(self.inner.val_mut());
                Entry {
                    vacant_key: None,
                    ..self
                }
            }
            Some(key) => Entry {
                vacant_key: Some(key),
                ..self
            },
        }
    }
}

impl<'a, K: Ord, V: Default> Entry<'a, K, V> {
    pub fn or_default(self) -> &'a mut V {
        self.or_insert_with(Default::default)
    }
}

#[cfg(test)]
impl<K: core::fmt::Debug, V: core::fmt::Debug> BpTreeMap<K, V> {
    pub fn print(&self) {
        if let Some(root) = self.root.as_ref() {
            root.reborrow().print_tree();
        }
    }
}

pub struct IntoIter<K, V> {
    imp: search::IterImpl<node::NodeOwned<K, V, node::marker::Leaf>>,
    rem: usize,
}

impl<K, V> Debug for IntoIter<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> IntoIter<K, V> {
    fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            imp: self.imp.reborrow(),
            rem: self.rem,
        }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        unsafe { self.imp.dying_next() }.map(|ret| {
            self.rem -= 1;
            ret
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.rem, Some(self.rem))
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe { self.imp.dying_prev() }.map(|ret| {
            self.rem -= 1;
            ret
        })
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.rem
    }
}

impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<K, V> Drop for IntoIter<K, V> {
    fn drop(&mut self) {
        struct Guard<'a, K, V>(&'a mut IntoIter<K, V>);
        impl<'a, K, V> Drop for Guard<'a, K, V> {
            fn drop(&mut self) {
                while let Some((k, v)) = unsafe { self.0.imp.dying_next() } {
                    drop(k);
                    drop(v);
                }
            }
        }

        while let Some((k, v)) = unsafe { self.imp.dying_next() } {
            let guard = Guard(self);
            drop(k);
            drop(v);
            mem::forget(guard);
        }
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    imp: search::IterImpl<node::NodeRef<'a, K, V, node::marker::Leaf>>,
    rem: usize,
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Self {
            imp: self.imp,
            rem: self.rem,
        }
    }
}

impl<'a, K: 'a, V: 'a> Debug for Iter<'a, K, V>
where
    Self: Clone,
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.clone()).finish()
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let (key, val) = self.imp.next()?;
        self.rem -= 1;
        Some(unsafe { (&*key, &*val) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.rem, Some(self.rem))
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (key, val) = self.imp.prev()?;
        self.rem -= 1;
        Some(unsafe { (&*key, &*val) })
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    fn len(&self) -> usize {
        self.rem
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    imp: search::IterImpl<node::NodeMut<'a, K, V, node::marker::Leaf>>,
    rem: usize,
}

impl<'a, K: 'a, V: 'a> Debug for IterMut<'a, K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a, K: 'a, V: 'a> IterMut<'a, K, V> {
    fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            imp: self.imp.reborrow(),
            rem: self.rem,
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        let (key, val) = self.imp.next()?;
        self.rem -= 1;
        Some(unsafe { (&*key, &mut *val) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.rem, Some(self.rem))
    }
}

impl<K, V> DoubleEndedIterator for IterMut<'_, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (key, val) = self.imp.prev()?;
        self.rem -= 1;
        Some(unsafe { (&*key, &mut *val) })
    }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    fn len(&self) -> usize {
        self.rem
    }
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

pub struct IntoKeys<K, V> {
    iter: IntoIter<K, V>,
}

impl<K, V> Debug for IntoKeys<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V> IntoKeys<K, V> {
    fn iter(&self) -> Keys<'_, K, V> {
        Keys {
            iter: self.iter.iter(),
        }
    }
}

impl<K, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(key, _)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for IntoKeys<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(key, _)| key)
    }
}

impl<K, V> ExactSizeIterator for IntoKeys<K, V> {}

impl<K, V> FusedIterator for IntoKeys<K, V> {}

pub struct Keys<'a, K: 'a, V: 'a> {
    iter: Iter<'a, K, V>,
}

impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, K: 'a, V: 'a> Debug for Keys<'a, K, V>
where
    Self: Clone,
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(key, _)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(key, _)| key)
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {}

impl<K, V> FusedIterator for Keys<'_, K, V> {}

pub struct IntoValues<K, V> {
    iter: IntoIter<K, V>,
}

impl<K, V> Debug for IntoValues<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V> IntoValues<K, V> {
    fn iter(&self) -> Values<'_, K, V> {
        Values {
            iter: self.iter.iter(),
        }
    }
}

impl<K, V> Iterator for IntoValues<K, V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_, val)| val)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for IntoValues<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(_, val)| val)
    }
}

impl<K, V> ExactSizeIterator for IntoValues<K, V> {}

impl<K, V> FusedIterator for IntoValues<K, V> {}

pub struct Values<'a, K: 'a, V: 'a> {
    iter: Iter<'a, K, V>,
}

impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, K: 'a, V: 'a> Debug for Values<'a, K, V>
where
    Self: Clone,
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_, val)| val)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(_, val)| val)
    }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {}

impl<K, V> FusedIterator for Values<'_, K, V> {}

pub struct ValuesMut<'a, K: 'a, V: 'a> {
    iter: IterMut<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> Debug for ValuesMut<'a, K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, K: 'a, V: 'a> ValuesMut<'a, K, V> {
    fn iter(&self) -> Values<'_, K, V> {
        Values {
            iter: Iter {
                imp: self.iter.imp.reborrow(),
                rem: self.iter.rem,
            },
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_, val)| val)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for ValuesMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(_, val)| val)
    }
}

impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

pub struct Range<'a, K: 'a, V: 'a> {
    imp: search::IterImpl<node::NodeRef<'a, K, V, node::marker::Leaf>>,
}

impl<K, V> Clone for Range<'_, K, V> {
    fn clone(&self) -> Self {
        Self { imp: self.imp }
    }
}

impl<'a, K: 'a, V: 'a> Debug for Range<'a, K, V>
where
    Self: Clone,
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.clone()).finish()
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.imp.next().map(|(k, v)| unsafe { (&*k, &*v) })
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn min(mut self) -> Option<Self::Item> {
        self.next()
    }

    fn max(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.imp.prev().map(|(k, v)| unsafe { (&*k, &*v) })
    }
}

impl<K, V> FusedIterator for Range<'_, K, V> {}

pub struct RangeMut<'a, K: 'a, V: 'a> {
    imp: search::IterImpl<node::NodeMut<'a, K, V, node::marker::Leaf>>,
}

impl<'a, K: 'a, V: 'a> Debug for RangeMut<'a, K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a, K: 'a, V: 'a> RangeMut<'a, K, V> {
    fn iter(&self) -> Range<'_, K, V> {
        Range {
            imp: self.imp.reborrow(),
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for RangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.imp.next().map(|(k, v)| unsafe { (&*k, &mut *v) })
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn min(mut self) -> Option<Self::Item> {
        self.next()
    }

    fn max(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for RangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.imp.prev().map(|(k, v)| unsafe { (&*k, &mut *v) })
    }
}

impl<K, V> FusedIterator for RangeMut<'_, K, V> {}

#[cfg(test)]
pub mod tests {

    #[test]
    pub fn construct() {
        use super::*;
        use alloc::collections::BTreeMap;
        // let init = [
        //       984, 898, 87, 541, 852, 624, 393, 54, 686, 724, 197, 119, 633, 101, 776, 127,
        //       126, 980, 432, 827,
        // ];
        // let mut init = vec![];
        let mut mirror = BTreeMap::new();
        let n = 500000;
        let max = 1000000;

        let mut t = BpTreeMap::new();

        for i in 1..=n {
            let u = {
                let mut u = rand::random::<u32>() % max;
                while mirror.try_insert(u, i).is_err() {
                    u = rand::random::<u32>() % max;
                }
                u
            };
            // init.push(u);
            // let u = init[i - 1];
            // mirror.insert(u, i);

            t.insert(u, i);
        }

        // {
        //       let mut file = core::fs::File::with_options()
        //             .create(true)
        //             .write(true)
        //             .truncate(true)
        //             .open("123.txt").unwrap();
        //       file.write_all(format!("{:#?}", init).as_bytes()).unwrap();
        // }

        for kv1 in mirror.iter() {
            let kv2 = t.get_key_value(kv1.0).unwrap();
            assert!(kv1 == kv2);
        }

        for kv2 in t.iter_mut() {
            let kv1 = mirror.get_key_value(kv2.0).unwrap();
            assert!((kv1.0, kv1.1) == (kv2.0, kv2.1));
            *kv2.1 += 20;
        }

        let mut rs = rand::random::<u32>() % max;
        let mut re = rand::random::<u32>() % max;
        if rs > re {
            core::mem::swap(&mut rs, &mut re);
        }
        for (key, _) in t.range(rs..re) {
            assert!((rs..re).contains(key));
        }

        // for (u, i0) in mirror {
        //       // println!("--------------------------{}: {} => {}", z, u, i0);
        //       // t.print();
        //       let i = t.remove(&u).unwrap();
        //       assert!(i == i0 + 20);
        // }
    }
}
