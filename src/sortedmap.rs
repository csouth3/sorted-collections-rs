use std::collections::btree_map::{BTreeMap, self};
use std::collections::hash_map::{HashMap, self};
use std::collections::hash_state::HashState;
use std::default::Default;
use std::hash::{Hash, Hasher};
use std::iter::Peekable;

/// An extension trait for a `Map` whose keys have a defined total ordering.
/// This trait provides convenience methods which take advantage of the map's ordering.
/// The provided methods may be overriden if desired to provide more efficient
/// implementations.
#[experimental]
pub trait SortedMap<K, V> : Sized
    where K: Clone + Ord,
          V: Clone {
          type Range;
          type RangeMut;
          type RangeRemove;

    /// Returns an immutable reference to the first (least) key currently in this map.
    /// Returns `None` if this map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.first().unwrap(), &1u32);
    /// }
    /// ```
    #[experimental]
    fn first(&self) -> Option<&K>;

    /// Removes and returns the first (least) key currently in this map and its associated value.
    /// Returns `None` if this map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.first_remove().unwrap(), (1u32, 1u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(2u32, 2u32), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn first_remove(&mut self) -> Option<(K, V)>;

    /// Returns an immutable reference to the last (greatest) key currently in this map.
    /// Returns `None` if this map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.last().unwrap(), &5u32);
    /// }
    /// ```
    #[experimental]
    fn last(&self) -> Option<&K>;

    /// Removes and returns the last (greatest) key currently in this map and its associated value.
    /// Returns `None` if this map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.last_remove().unwrap(), (5u32, 5u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4)]);
    /// }
    /// ```
    #[experimental]
    fn last_remove(&mut self) -> Option<(K, V)>;

    /// Returns an immutable reference to the least key in this map greater than or equal to `key`.
    /// Returns `None` if there is no such key.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.ceiling(&3).unwrap(), &3u32);
    /// }
    /// ```
    #[experimental]
    fn ceiling(&self, key: &K) -> Option<&K>;

    /// Removes and returns the least key in this map greater than or equal to `key` and its
    /// associated value.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.ceiling_remove(&3).unwrap(), (3u32, 3u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn ceiling_remove(&mut self, key: &K) -> Option<(K, V)>;

    /// Returns an immutable reference to the greatest key in this map less than or equal to `key`.
    /// Returns `None` if there is no such key.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.floor(&3).unwrap(), &3u32);
    /// }
    /// ```
    #[experimental]
    fn floor(&self, key: &K) -> Option<&K>;

    /// Removes and returns the greatest key in this map less than or equal to `key` and its
    /// associated value.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.floor_remove(&3).unwrap(), (3u32, 3u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn floor_remove(&mut self, key: &K) -> Option<(K, V)>;

    /// Returns an immutable reference to the least key in this map strictly greater than `key`.
    /// Returns `None` if there is no such key.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.higher(&3).unwrap(), &4u32);
    /// }
    /// ```
    #[experimental]
    fn higher(&self, key: &K) -> Option<&K>;

    /// Removes and returns the least key in this map strictly greater than `key` and its
    /// associated value.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.higher_remove(&3).unwrap(), (4u32, 4u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn higher_remove(&mut self, key: &K) -> Option<(K, V)>;


    /// Returns an immutable reference to the greatest key in this map strictly less than `key`.
    /// Returns `None` if there is no such key.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.lower(&3).unwrap(), &2u32);
    /// }
    /// ```
    #[experimental]
    fn lower(&self, key: &K) -> Option<&K>;

    /// Removes and returns the greatest key in this map strictly less than `key` and its
    /// associated value.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.lower_remove(&3).unwrap(), (2u32, 2u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn lower_remove(&mut self, key: &K) -> Option<(K, V)>;

    /// Returns an iterator over pairs of immutable key-value references into this map,
    /// with the pairs being iterated being those whose keys are in the range [from_key, to_key).
    /// Note that this iterator need not necessarily yield the pairs in ascending order by key!
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.range(&2, &4).map(|(&k, &v)| (k, v)).collect::<Vec<(u32, u32)>>(),
    ///         vec![(2u32, 2u32), (3, 3)]);
    /// }
    /// ```
    #[experimental]
    fn range(&self, from_key: &K, to_key: &K) -> Self::Range;

    /// Returns an iterator over pairs of immutable-key/mutable-value references into this map,
    /// with the pairs being iterated being those whose keys are in the range [from_key, to_key).
    /// Note that this iterator need not necessarily yield the pairs in ascending order by key!
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     for (_, v) in map.range_mut(&2, &4) {
    ///         *v += 1;
    ///     }
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 3), (3, 4), (4, 4), (5, 5)]);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if `from_elem > to_elem`.
    #[experimental]
    fn range_mut(&mut self, from_key: &K, to_key: &K) -> Self::RangeMut;

    /// Removes the key-value pairs of this map whose keys lie in the range [from_key, to_key),
    /// and returns a by-value iterator over the removed pairs.  Note that this iterator need
    /// not necessarily yield the values in ascending order by key!
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMap;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.range_remove(&2, &4).collect::<Vec<(u32, u32)>>(),
    ///         vec![(2u32, 2u32), (3, 3)]);
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn range_remove(&mut self, from_key: &K, to_key: &K) -> Self::RangeRemove;
}

// A generic reusable impl of SortedMap.
macro_rules! sortedmap_impl {
    ($typ:ty, $range:ident, $rangeret:ty, $rangemut:ident, $rangemutret:ty, $rangeremove:ident, $rangeremoveret:ty) => (
        fn first(&self) -> Option<&K> {
            if self.is_empty() { return None }

            Some(self.keys().min().unwrap())
        }

        fn first_remove(&mut self) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.first().cloned().unwrap();
            let val = self.remove(&key);
            assert!(val.is_some());

            Some((key, val.unwrap()))
        }

        fn last(&self) -> Option<&K> {
            if self.is_empty() { return None }

            Some(self.keys().max().unwrap())
        }

        fn last_remove(&mut self) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.last().cloned().unwrap();
            let val = self.remove(&key);
            assert!(val.is_some());

            Some((key, val.unwrap()))
        }

        fn ceiling(&self, key: &K) -> Option<&K> {
            if self.is_empty() { return None }

            Some(self.keys().filter(|&k| k >= key).min().unwrap())
        }

        fn ceiling_remove(&mut self, key: &K) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let ceiling = self.ceiling(key).cloned().unwrap();
            let val = self.remove(&ceiling).unwrap();
            Some((ceiling, val))
        }

        fn floor(&self, key: &K) -> Option<&K> {
            if self.is_empty() { return None }

            Some(self.keys().filter(|&k| k <= key).max().unwrap())
        }

        fn floor_remove(&mut self, key: &K) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let floor = self.floor(key).cloned().unwrap();
            let val = self.remove(&floor).unwrap();
            Some((floor, val))
        }

        fn higher(&self, key: &K) -> Option<&K> {
            if self.is_empty() { return None }

            Some(self.keys().filter(|&k| k > key).min().unwrap())
        }

        fn higher_remove(&mut self, key: &K) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let higher = self.higher(key).cloned().unwrap();
            let val = self.remove(&higher).unwrap();
            Some((higher, val))
        }

        fn lower(&self, key: &K) -> Option<&K> {
            if self.is_empty() { return None }

            Some(self.keys().filter(|&k| k < key).max().unwrap())
        }

        fn lower_remove(&mut self, key: &K) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let lower = self.lower(key).cloned().unwrap();
            let val = self.remove(&lower).unwrap();
            Some((lower, val))
        }

        fn range(&self, from_key: &K, to_key: &K) -> $rangeret {
            $range {
                iter: self.iter().peekable(),
                lower: from_key.clone(),
                upper: to_key.clone(),
            }
        }

        fn range_mut(&mut self, from_key: &K, to_key: &K) -> $rangemutret {
            $rangemut {
                iter: self.iter_mut().peekable(),
                lower: from_key.clone(),
                upper: to_key.clone(),
            }
        }

        fn range_remove(&mut self, from_key: &K, to_key: &K) -> $rangeremoveret {
            let remove: $typ = self.keys().cloned().zip(self.values().cloned())
                .filter_map(|(k, v)| if k >= *from_key && k < *to_key { Some((k, v)) } else { None }).collect();
            for key in remove.keys() {
                self.remove(key);
            }
            $rangeremove { iter: remove.into_iter() }
        }
    );
}

// An impl of SortedMap for the standard library BTreeMap
#[experimental]
impl<'a, K, V> SortedMap<K, V> for BTreeMap<K, V>
    where K: Clone + Ord,
          V: Clone {
    type Range = BTreeMapRange<'a, K, V>;
    type RangeMut = BTreeMapRangeMut<'a, K, V>;
    type RangeRemove = BTreeMapRangeRemove<K, V>;

    sortedmap_impl!(BTreeMap<K, V>, BTreeMapRange, BTreeMapRange<K, V>, BTreeMapRangeMut, BTreeMapRangeMut<K, V>, BTreeMapRangeRemove, BTreeMapRangeRemove<K, V>);
}
// An impl of SortedMap for the standard library HashMap.
#[experimental]
impl<'a, K, V, S, H> SortedMap<K, V> for HashMap<K, V, S>
    where K: Clone + Eq + Hash<H> + Ord,
          V: Clone,
          S: HashState<Hasher=H> + Default,
          H: Hasher<Output=u64> {
    type Range = HashMapRange<'a, K, V>;
    type RangeMut = HashMapRangeMut<'a, K, V>;
    type RangeRemove = HashMapRangeRemove<K, V>;

    sortedmap_impl!(HashMap<K, V, S>, HashMapRange, HashMapRange<K, V>, HashMapRangeMut, HashMapRangeMut<K, V>, HashMapRangeRemove, HashMapRangeRemove<K, V>);
}

#[experimental]
pub struct BTreeMapRange<'a, K: 'a, V: 'a> {
    iter: Peekable<(&'a K, &'a V), btree_map::Iter<'a, K, V>>,
    lower: K,
    upper: K,
}

#[experimental]
impl<'a, K: Ord, V> Iterator for BTreeMapRange<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            if self.iter.is_empty() { return None; }

            if (*self.iter.peek().unwrap()).0 >= &self.lower
                && (*self.iter.peek().unwrap()).0 < &self.upper { return self.iter.next(); }
            else { self.iter.next(); }
        }
    }
}

#[experimental]
pub struct BTreeMapRangeMut<'a, K: 'a, V: 'a> {
    iter: Peekable<(&'a K, &'a mut V), btree_map::IterMut<'a, K, V>>,
    lower: K,
    upper: K,
}

#[experimental]
impl<'a, K: Ord, V> Iterator for BTreeMapRangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        loop {
            if self.iter.is_empty() { return None; }

            if (*self.iter.peek().unwrap()).0 >= &self.lower
                && (*self.iter.peek().unwrap()).0 < &self.upper { return self.iter.next(); }
            else { self.iter.next(); }
        }
    }
}

#[experimental]
pub struct BTreeMapRangeRemove<K, V> {
    iter: btree_map::IntoIter<K, V>
}

#[experimental]
impl<K, V> Iterator for BTreeMapRangeRemove<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
#[experimental]
impl<K, V> DoubleEndedIterator for BTreeMapRangeRemove<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> { self.iter.next_back() }
}
#[experimental]
impl<K, V> ExactSizeIterator for BTreeMapRangeRemove<K, V> {
    fn len(&self) -> usize { self.iter.len() }
}

#[experimental]
pub struct HashMapRange<'a, K: 'a, V: 'a> {
    iter: Peekable<(&'a K, &'a V), hash_map::Iter<'a, K, V>>,
    lower: K,
    upper: K,
}

#[experimental]
impl<'a, K: Ord, V> Iterator for HashMapRange<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            if self.iter.is_empty() { return None; }

            if (*self.iter.peek().unwrap()).0 >= &self.lower
                && (*self.iter.peek().unwrap()).0 < &self.upper { return self.iter.next(); }
            else { self.iter.next(); }
        }
    }
}

#[experimental]
pub struct HashMapRangeMut<'a, K: 'a, V: 'a> {
    iter: Peekable<(&'a K, &'a mut V), hash_map::IterMut<'a, K, V>>,
    lower: K,
    upper: K,
}

#[experimental]
impl<'a, K: Ord, V> Iterator for HashMapRangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        loop {
            if self.iter.is_empty() { return None; }

            if (*self.iter.peek().unwrap()).0 >= &self.lower
                && (*self.iter.peek().unwrap()).0 < &self.upper { return self.iter.next(); }
            else { self.iter.next(); }
        }
    }
}

#[experimental]
pub struct HashMapRangeRemove<K, V> {
    iter: hash_map::IntoIter<K, V>
}

#[experimental]
impl<K, V> Iterator for HashMapRangeRemove<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
#[experimental]
impl<K, V> ExactSizeIterator for HashMapRangeRemove<K, V> {
    fn len(&self) -> usize { self.iter.len() }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::SortedMap;

    #[test]
    fn test_first() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.first().unwrap(), &1u32);
    }

    #[test]
    fn test_first_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.first_remove().unwrap(), (1u32, 1u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(2u32, 2u32), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_last() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.last().unwrap(), &5u32);
    }

    #[test]
    fn test_last_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.last_remove().unwrap(), (5u32, 5u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4)]);
    }

    #[test]
    fn test_ceiling() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.ceiling(&3).unwrap(), &3u32);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_ceiling_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.ceiling_remove(&3).unwrap(), (3u32, 3u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_floor() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.floor(&3).unwrap(), &3u32);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_floor_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.floor_remove(&3).unwrap(), (3u32, 3u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_higher() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.higher(&3).unwrap(), &4u32);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_higher_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.higher_remove(&3).unwrap(), (4u32, 4u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (5, 5)]);
    }

    #[test]
    fn test_lower() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.lower(&3).unwrap(), &2u32);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_lower_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.lower_remove(&3).unwrap(), (2u32, 2u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_range() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.range(&2, &4).map(|(&k, &v)| (k, v)).collect::<Vec<(u32, u32)>>(),
            vec![(2u32, 2u32), (3, 3)]);
    }

    #[test]
    fn test_range_mut() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        for (_, v) in map.range_mut(&2, &4) {
            *v += 1;
        }
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
            vec![(1u32, 1u32), (2, 3), (3, 4), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_range_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.range_remove(&2, &4).collect::<Vec<(u32, u32)>>(), vec![(2u32, 2u32), (3, 3)]);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
            vec![(1u32, 1u32), (4, 4), (5, 5)]);
    }
}
