mod node;
mod search;

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Debug;
use core::iter::FusedIterator;
use core::mem::{self, ManuallyDrop};
use core::ops::{Index, IndexMut, RangeBounds};
use core::ptr;

use self::node::Root;

/// A map based on a B+ tree.
///
/// # Examples
///
/// ```
/// use bptree::BpTreeMap;
///
/// let mut students = BpTreeMap::new();
///
/// // Input some students' information.
/// students.insert("S01", "John");
/// students.insert("S02", "Jack");
/// students.insert("S03", "Reo");
///
/// // Find a student's information by direct indexing.
/// let jack = students["S02"];
/// assert_eq!(jack, "Jack");
///
/// // A student has graduated from the college.
/// let john = students.remove("S01").unwrap();
/// assert_eq!(john, "John");
///
/// // Iterates the information so as to deal with senior's inspection.
/// for (id, name) in students.iter() {
///     println!("{}: {}", id, name);
/// }
/// ```
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
    /// Creates an empty `BpTreeMap`.
    ///
    /// This function doesn't allocate anything from the heap, so it can be used in constant
    /// initalizations.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// // Doesn't allocate anything.
    /// let mut map = BpTreeMap::new();
    ///
    /// // Inserts key-value pairs into the empty map.
    /// // Now allocates.
    /// map.insert(1, "Sample");
    /// ```
    pub const fn new() -> Self {
        BpTreeMap { root: None, len: 0 }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.len(), 2);
    ///
    /// map.remove(&2);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert(1, "One");
    /// assert!(!map.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
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
    /// Returns the entry of the map at the given key for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut count = BpTreeMap::new();
    /// let sample = "Hello world!";
    /// for c in sample.bytes() {
    ///     *count.entry(c).or_insert(0) += 1;
    /// }
    /// assert_eq!(count[&b'l'], 3);
    /// ```
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

    /// Returns the reference to the value at the given key.
    ///
    /// The key can be any borrowing form of the map's key type, but the ordering on the borrowed
    /// form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.get(&1), Some(&"One"));
    /// assert_eq!(map.get(&10), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        self.get_key_value(key).map(|(_, value)| value)
    }

    /// Returns the reference to the key-value pair at the given key.
    ///
    /// The key can be any borrowing form of the map's key type, but the ordering on the borrowed
    /// form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"One")));
    /// assert_eq!(map.get_key_value(&10), None);
    /// ```
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

    /// Returns `true` if the map contains the specified key.
    ///
    /// The key can be any borrowing form of the map's key type, but the ordering on the borrowed
    /// form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&10), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        self.get(key).is_some()
    }

    /// Returns the mutable reference to the value at the given key.
    ///
    /// The key can be any borrowing form of the map's key type, but the ordering on the borrowed
    /// form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.get_mut(&1), Some(&mut "One"));
    /// assert_eq!(map.get_mut(&10), None);
    /// ```
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

    /// Inserts a key-value pair into the map.
    ///
    /// If the map didn't have this key present, `None` is returned.
    ///
    /// If it did, the key is not updated, and the old value is replaced with the new one and
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// assert_eq!(map.insert(1, "One"), None);
    /// assert_eq!(map.len(), 1);
    ///
    /// assert_eq!(map.insert(1, "Another"), Some("One"));
    /// assert_eq!(map.get(&1), Some(&"Another"));
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        let mut ent = self.entry(key);
        if let Some(val_mut) = ent.get_mut() {
            let mut ret = value;
            core::mem::swap(val_mut, &mut ret);
            Some(ret)
        } else {
            ent.or_insert(value);
            None
        }
    }

    /// Moves all elements from `other` to `Self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut a = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// let mut b = BpTreeMap::from([(2, "AnotherTwo"), (3, "Three"), (4, "Four")]);
    ///
    /// a.append(&mut b);
    /// assert_eq!(a.len(), 4);
    /// assert_eq!(a[&2], "AnotherTwo");
    /// assert!(b.is_empty());
    /// ```
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

    /// Removes and returns the key-value pair from the map according to the given key.
    ///
    /// The key can be any borrowing form of the map's key type, but the ordering on the borrowed
    /// form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.remove_entry(&2), Some((2, "Two")));
    /// assert_eq!(map.remove_entry(&2), None);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn remove_entry<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        let self_ptr: *mut _ = self;

        let root_node = self.root.as_mut()?.borrow_mut();
        match root_node.search_tree(key) {
            search::SearchResult::Vacant(_) => None,
            search::SearchResult::Occupied(entry) => node::remove_with_root(entry, self_ptr),
        }
    }

    /// Removes the key-value pair from the map according to the given key. Only the value is
    /// returned.
    ///
    /// The key can be any borrowing form of the map's key type, but the ordering on the borrowed
    /// form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.remove(&2), Some("Two"));
    /// assert_eq!(map.remove(&2), None);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        self.remove_entry(key).map(|(_, val)| val)
    }

    /// Clears the map, dropping all of its elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert!(!map.is_empty());
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<Q: ?Sized + Ord, K: Borrow<Q>, V> Index<&Q> for BpTreeMap<K, V> {
    type Output = V;

    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<Q: ?Sized + Ord, K: Borrow<Q>, V> IndexMut<&Q> for BpTreeMap<K, V> {
    fn index_mut(&mut self, index: &Q) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

impl<K, V> BpTreeMap<K, V> {
    /// Returns the first key-value pair in the map.
    ///
    /// The first key is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// assert_eq!(map.first_key_value(), None);
    ///
    /// map.insert(1, "One");
    /// map.insert(2, "Two");
    /// assert_eq!(map.first_key_value(), Some((&1, &"One")));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        let root_node = self.root.as_ref()?.reborrow();
        Some(root_node.first_entry().into_kv())
    }

    /// Returns the first entry in the map for in-place manipulation..
    ///
    /// The key of the entry is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// assert!(map.first_entry().is_none());
    ///
    /// map.insert(1, "One");
    /// map.insert(2, "Two");
    /// map.first_entry().unwrap().and_modify(|val| *val = "Another");
    ///
    /// assert_eq!(map.first_key_value(), Some((&1, &"Another")));
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

    /// Removes and returns the first key-value pair from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.pop_first(), Some((1, "One")));
    /// assert_eq!(map.pop_first(), Some((2, "Two")));
    /// assert_eq!(map.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        self.first_entry().and_then(|ent| ent.remove_entry())
    }

    /// Returns the last key-value pair in the map.
    ///
    /// The last key is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// assert_eq!(map.last_key_value(), None);
    ///
    /// map.insert(1, "One");
    /// map.insert(2, "Two");
    /// assert_eq!(map.last_key_value(), Some((&2, &"Two")));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        let root_node = self.root.as_ref()?.reborrow();
        Some(root_node.last_entry(false).into_kv())
    }

    /// Returns the last entry in the map for in-place manipulation..
    ///
    /// The key of the entry is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// assert!(map.last_entry().is_none());
    ///
    /// map.insert(1, "One");
    /// map.insert(2, "Two");
    /// map.last_entry().unwrap().and_modify(|val| *val = "Another");
    ///
    /// assert_eq!(map.last_key_value(), Some((&2, &"Another")));
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

    /// Removes and returns the last key-value pair from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.pop_last(), Some((2, "Two")));
    /// assert_eq!(map.pop_last(), Some((1, "One")));
    /// assert_eq!(map.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        self.last_entry().and_then(|ent| ent.remove_entry())
    }

    /// Converts the map into an iterator over the keys of the map, while the values are dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// let vec = map.into_keys().collect::<Vec<_>>();
    /// assert_eq!(vec, vec![1, 2]);
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            iter: self.into_iter(),
        }
    }

    /// Converts the map into an iterator over the values of the map, while the keys are dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// let vec = map.into_values().collect::<Vec<_>>();
    /// assert_eq!(vec, vec!["One", "Two"]);
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            iter: self.into_iter(),
        }
    }

    /// Returns an iterator over the elements of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(3, "Three"), (1, "One"), (4, "Four"), (2, "Two")]);
    /// for (key, value) in map.iter() {
    ///     println!("{}: {}", key, value);
    /// }
    ///
    /// let first_kv = map.iter().next().unwrap();
    /// assert_eq!(first_kv, (&1, &"One"));
    /// ```
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

    /// Returns an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(3, "Three"), (1, "One"), (4, "Four"), (2, "Two")]);
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    ///
    /// let first_key = map.keys().next().unwrap();
    /// assert_eq!(first_key, &1);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { iter: self.iter() }
    }

    /// Returns an iterator over the values of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(3, "Three"), (1, "One"), (4, "Four"), (2, "Two")]);
    /// for value in map.values() {
    ///     println!("{}", value);
    /// }
    ///
    /// let first_value = map.values().next().unwrap();
    /// assert_eq!(first_value, &"One");
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values { iter: self.iter() }
    }

    /// Returns an iterator over a sub-range of entries in the map.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let map = BpTreeMap::from([(2, "Two"), (6, "Six"), (11, "Eleven")]);
    /// assert_eq!(map.range(2..).next(), Some((&2, &"Two")));
    /// assert_eq!(map.range(..6).next(), Some((&2, &"Two")));
    /// ```
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

    /// Returns a mutable iterator over the elements of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(3, "Three"), (1, "One"), (4, "Four"), (2, "Two")]);
    ///
    /// let first_kv = map.iter_mut().next().unwrap();
    /// assert_eq!(first_kv, (&1, &mut "One"));
    /// *first_kv.1 = "Another";
    /// drop(first_kv);
    ///
    /// for (key, value) in map.iter_mut() {
    ///     println!("{}: {}", key, value);
    /// }
    /// ```
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

    /// Returns a mutable iterator over the elements of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(3, "Three"), (1, "One"), (4, "Four"), (2, "Two")]);
    ///
    /// let first_value = map.values_mut().next().unwrap();
    /// assert_eq!(first_value, &mut "One");
    /// *first_value = "Another";
    /// drop(first_value);
    ///
    /// for value in map.values_mut() {
    ///     println!("{}", value);
    /// }
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            iter: self.iter_mut(),
        }
    }

    /// Returns a mutable iterator over a sub-range of entries in the map.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(2, "Two"), (6, "Six"), (11, "Eleven")]);
    /// assert_eq!(map.range_mut(2..).next(), Some((&2, &mut "Two")));
    /// assert_eq!(map.range_mut(..6).next(), Some((&2, &mut "Two")));
    /// ```
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
            if root.is_empty() {
                Root::drop(root);
                IntoIter {
                    imp: search::IterImpl::none(),
                    rem: 0,
                }
            } else {
                let first = unsafe { ptr::read(&root) }.first_entry();
                let last = root.last_entry(false);
                IntoIter {
                    imp: search::IterImpl::new(first, last),
                    rem: me.len,
                }
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

impl<'a, K: Debug, V: Debug> Debug for Entry<'a, K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut d = f.debug_struct("Entry");
        match self.vacant_key.as_ref() {
            Some(key) => d.field("vacant", &true).field("key", key),
            None => {
                let (k, v) = self.inner.reborrow().into_kv();
                d.field("vacant", &false).field("key", k).field("value", v)
            }
        }
        .finish()
    }
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

    /// Ensures a value is present in the entry by inserting a default value if not, and returns
    /// a mutable reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// map.entry(1).or_insert("One");
    /// assert_eq!(map[&1], "One");
    /// ```
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(|| default)
    }

    /// Ensures a value is present in the entry by inserting the result of the default function
    /// if not, and returns a mutable reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// map.entry(1).or_insert_with(|| "One".to_string());
    /// assert_eq!(&*map[&1], "One");
    /// ```
    pub fn or_insert_with<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        self.or_insert_with_key(|_| default())
    }

    /// Ensures a value is present in the entry by inserting the result of the default function
    /// if not, and returns a mutable reference to the value.
    ///
    /// The function is parameterized by a reference to the key of the entry and thus allows
    /// key-derived value generation.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    /// map.entry("Hello").or_insert_with_key(|key| key.chars().count());
    /// assert_eq!(map["Hello"], 5);
    /// ```
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

    /// Returns the key of the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::<&str, ()>::new();
    /// let entry = map.entry("Hello");
    /// assert_eq!(entry.key(), &"Hello");
    /// ```
    pub fn key(&self) -> &K {
        match &self.vacant_key {
            None => self.inner.reborrow().into_kv().0,
            Some(key) => key,
        }
    }

    /// Returns a reference to the value of the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One")]);
    ///
    /// let one = map.entry(1);
    /// assert_eq!(one.get(), Some(&"One"));
    /// drop(one);
    ///
    /// let another = map.entry(5);
    /// assert_eq!(another.get(), None);
    /// assert_eq!(another.or_insert("Five"), &mut "Five");
    /// ```
    pub fn get(&self) -> Option<&V> {
        match self.vacant_key {
            None => Some(self.inner.reborrow().into_kv().1),
            Some(_) => None,
        }
    }

    /// Returns a mutable reference to the value of the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One")]);
    ///
    /// let mut one = map.entry(1);
    /// assert_eq!(one.get_mut(), Some(&mut "One"));
    /// drop(one);
    ///
    /// let mut another = map.entry(5);
    /// assert_eq!(another.get_mut(), None);
    /// assert_eq!(another.or_insert("Five"), &mut "Five");
    /// ```
    pub fn get_mut(&mut self) -> Option<&mut V> {
        match self.vacant_key {
            None => Some(self.inner.val_mut()),
            Some(_) => None,
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into
    /// the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::new();
    ///
    /// map.entry("Value").and_modify(|v| *v += 1).or_insert(0);
    /// assert_eq!(map["Value"], 0);
    ///
    /// map.entry("Value").and_modify(|v| *v += 1).or_insert(0);
    /// assert_eq!(map["Value"], 1);
    /// ```
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

impl<'a, K, V> Entry<'a, K, V> {
    /// Removes the entry from the map if present, returning the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.entry(2).remove(), Some("Two"));
    /// assert_eq!(map.entry(2).remove(), None);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn remove(self) -> Option<V> {
        self.remove_entry().map(|(_, val)| val)
    }

    /// Removes the entry from the map if present, returning the key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::from([(1, "One"), (2, "Two")]);
    /// assert_eq!(map.entry(2).remove_entry(), Some((2, "Two")));
    /// assert_eq!(map.entry(2).remove_entry(), None);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn remove_entry(self) -> Option<(K, V)> {
        match self.vacant_key {
            Some(_) => None,
            None => node::remove_with_root(self.inner, self.self_ptr),
        }
    }
}

impl<'a, K: Ord, V: Default> Entry<'a, K, V> {
    /// Ensures a value is present in the entry by inserting the result of the default value
    /// if not, and returns a mutable reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bptree::BpTreeMap;
    ///
    /// let mut map = BpTreeMap::<&str, u32>::new();
    /// map.entry("Zero").or_default();
    /// assert_eq!(map["Zero"], 0);
    /// ```
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

/// An owning iterator over the entries of a `BpTreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`BpTreeMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
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
    /// Returns an iterator of references over the remaining items.
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

/// An iterator over the entries of a `BpTreeMap`.
///
/// This `struct` is created by the [`iter`] method on [`BpTreeMap`]. See its
/// documentation for more.
///
/// [`iter`]: BpTreeMap::iter
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

/// A mutable iterator over the entries of a `BpTreeMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`BpTreeMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: BpTreeMap::iter_mut
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
    /// Returns an iterator of references over the remaining items.
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

/// An owning iterator over the keys of a `BpTreeMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`BpTreeMap`].
/// See its documentation for more.
///
/// [`into_keys`]: BpTreeMap::into_keys
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
    /// Returns an iterator of references over the remaining items.
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

/// An iterator over the keys of a `BpTreeMap`.
///
/// This `struct` is created by the [`keys`] method on [`BpTreeMap`]. See its
/// documentation for more.
///
/// [`keys`]: BpTreeMap::keys
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

/// An owning iterator over the values of a `BpTreeMap`.
///
/// This `struct` is created by the [`into_values`] method on [`BpTreeMap`].
/// See its documentation for more.
///
/// [`into_values`]: BpTreeMap::into_values
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
    /// Returns an iterator of references over the remaining items.
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

/// An iterator over the values of a `BpTreeMap`.
///
/// This `struct` is created by the [`values`] method on [`BpTreeMap`]. See its
/// documentation for more.
///
/// [`values`]: BpTreeMap::values
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

/// A mutable iterator over the values of a `BpTreeMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`BpTreeMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: BpTreeMap::values_mut
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
    /// Returns an iterator of references over the remaining items.
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

/// An iterator over a sub-range of entries in a `BpTreeMap`.
///
/// This `struct` is created by the [`range`] method on [`BpTreeMap`]. See its
/// documentation for more.
///
/// [`range`]: BpTreeMap::range
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

/// A mutable iterator over a sub-range of entries in a `BpTreeMap`.
///
/// This `struct` is created by the [`range_mut`] method on [`BpTreeMap`]. See its
/// documentation for more.
///
/// [`range_mut`]: BpTreeMap::range_mut
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
    /// Returns an iterator of references over the remaining items.
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

impl<K: Ord, V> FromIterator<(K, V)> for BpTreeMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut ret = Self::new();
        for (k, v) in iter {
            ret.insert(k, v);
        }
        ret
    }
}

impl<K: PartialEq, V: PartialEq> PartialEq for BpTreeMap<K, V> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().zip(other.iter()).all(|(x, y)| x == y)
    }
}
impl<K: Eq, V: Eq> Eq for BpTreeMap<K, V> {}

impl<K: PartialOrd, V: PartialOrd> PartialOrd for BpTreeMap<K, V> {
    #[inline]
    fn partial_cmp(&self, other: &BpTreeMap<K, V>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}
impl<K: Ord, V: Ord> Ord for BpTreeMap<K, V> {
    #[inline]
    fn cmp(&self, other: &BpTreeMap<K, V>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

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
