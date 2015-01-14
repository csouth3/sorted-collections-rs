use std::collections::{BTreeMap, HashMap};
use std::collections::hash_state::HashState;
use std::default::Default;
use std::hash::{Hash, Hasher};

/// An extension trait for a `Map` whose keys have a defined total ordering.
/// This trait provides convenience methods which take advantage of the map's ordering.
/// The provided methods may be overriden if desired to provide more efficient
/// implementations.
#[experimental]
pub trait SortedMap<K, V> : Sized
    where K: Clone + Ord,
          V: Clone {
    /// Returns the first (least) key currently in this map, and its corresponding value.
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
    ///     assert_eq!(map.first().unwrap(), (1u32, 1u32));
    /// }
    /// ```
    // FIXME: Return reference here?
    #[experimental]
    fn first(&self) -> Option<(K, V)>;

    /// Removes and returns the first (least) key currently in this map, and its corresponding
    /// value.
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

    /// Returns the last (greatest) key currently in this map, and its corresponding value.
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
    ///     assert_eq!(map.last().unwrap(), (5u32, 5u32));
    /// }
    /// ```
    // FIXME: Return reference here?
    #[experimental]
    fn last(&self) -> Option<(K, V)>;

    /// Removes and returns the last (greatest) key currently in this map, and its
    /// corresponding value.
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

    /// Returns the key-value pairs of this map whose keys are less than (or equal to,
    /// if `inclusive` is true) `key`, as a new instance of the same type of map.
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
    ///
    ///     let head_map = map.head_map(&3, true);
    ///     // The original map shouldn't have changed.
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    ///
    ///     assert_eq!(head_map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3)]);
    /// }
    /// ```
    #[experimental]
    fn head_map(&self, key: &K, inclusive: bool) -> Self;

    /// Returns the key-value pairs of this map whose keys range from `from_key` to
    /// `to_key`, as a new instance of the same type of map.
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
    ///
    ///     let sub_map = map.sub_map(&2, false, &4, true);
    ///     // The original map shouldn't have changed.
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    ///
    ///     assert_eq!(sub_map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(3u32, 3u32), (4, 4)]);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if `from_key < to_key`.
    #[experimental]
    fn sub_map(&self, from_key: &K, from_inclusive: bool, to_key: &K, to_inclusive: bool) -> Self;

    /// Returns the key-value pairs of this map whose keys are greater than (or equal to,
    /// if `inclusive` is true) `key`, as a new instance of the same type of map.
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
    ///
    ///     let tail_map = map.tail_map(&3, true);
    ///     // The original map shouldn't have changed.
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    ///
    ///     assert_eq!(tail_map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(3u32, 3u32), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn tail_map(&self, key: &K, inclusive: bool) -> Self;

    /// Returns the least key greater than or equal to `key`, and its corresponding value.
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
    ///
    ///     assert_eq!(map.ceiling(&3).unwrap(), (3u32, 3u32));
    ///     // The original map shouldn't have changed.
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn ceiling(&self, key: &K) -> Option<(K, V)> {
        let tail = self.tail_map(key, true);
        tail.first()
    }

    /// Returns the greatest key less than or equal to `key`, and its corresponding value.
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
    ///
    ///     assert_eq!(map.floor(&3).unwrap(), (3u32, 3u32));
    ///     // The original map shouldn't have changed.
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn floor(&self, key: &K) -> Option<(K, V)> {
        let head = self.head_map(key, true);
        head.last()
    }

    /// Returns the least key strictly greater than the given key, and its corresponding value.
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
    ///
    ///     assert_eq!(map.higher(&3).unwrap(), (4u32, 4u32));
    ///     // The original map shouldn't have changed.
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn higher(&self, key: &K) -> Option<(K, V)> {
        let tail = self.tail_map(key, false);
        tail.first()
    }

    /// Returns the greatest key strictly less than the given key, and its corresponding value.
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
    ///
    ///     assert_eq!(map.lower(&3).unwrap(), (2u32, 2u32));
    ///     // The original map shouldn't have changed.
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
    #[experimental]
    fn lower(&self, key: &K) -> Option<(K, V)> {
        let head = self.head_map(key, false);
        head.last()
    }
}

// A generic reusable impl of SortedMap.
macro_rules! sortedmap_impl {
    ($typ:ty) => (
        fn first(&self) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.keys().min().cloned().unwrap();
            let val = self.get(&key).cloned().unwrap();

            Some((key, val))
        }

        fn first_remove(&mut self) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.keys().min().cloned().unwrap();
            let val = self.remove(&key);
            assert!(val.is_some());

            Some((key, val.unwrap()))
        }

        fn last(&self) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.keys().max().cloned().unwrap();
            let val = self.get(&key).cloned().unwrap();

            Some((key, val))
        }

        fn last_remove(&mut self) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.keys().max().cloned().unwrap();
            let val = self.remove(&key);
            assert!(val.is_some());

            Some((key, val.unwrap()))
        }

        fn head_map(&self, key: &K, inclusive: bool) -> $typ {
            let it = self.keys().cloned().zip(self.values().cloned());
            if inclusive {
                return it.filter_map(|(k, v)| if k <= *key { Some((k, v)) } else { None }).collect();
            } else {
                return it.filter_map(|(k, v)| if k < *key { Some((k, v)) } else { None }).collect();
            }
        }

        fn sub_map(&self, from_key: &K, from_inclusive: bool, to_key: &K, to_inclusive: bool) -> $typ {
            assert!(from_key <= to_key);

            let it = self.keys().cloned().zip(self.values().cloned());
            if from_inclusive && to_inclusive {
                return it.filter_map(|(k, v)| if k >= *from_key && k <= *to_key { Some((k, v)) } else { None }).collect();
            } else if from_inclusive && !to_inclusive {
                return it.filter_map(|(k, v)| if k >= *from_key && k < *to_key { Some((k, v)) } else { None }).collect();
            } else if !from_inclusive && to_inclusive {
                return it.filter_map(|(k, v)| if k > *from_key && k <= *to_key { Some((k, v)) } else { None }).collect();
            } else {
                return it.filter_map(|(k, v)| if k > *from_key && k < *to_key { Some((k, v)) } else { None }).collect();
            }
        }

        fn tail_map(&self, key: &K, inclusive: bool) -> $typ {
            let it = self.keys().cloned().zip(self.values().cloned());
            if inclusive {
                return it.filter_map(|(k, v)| if k >= *key { Some((k, v)) } else { None }).collect();
            } else {
                return it.filter_map(|(k, v)| if k > *key { Some((k, v)) } else { None }).collect();
            }
        }
    );
}

// An impl of SortedMap for the standard library BTreeMap
#[experimental]
impl<K, V> SortedMap<K, V> for BTreeMap<K, V>
    where K: Clone + Ord,
          V: Clone {
    sortedmap_impl!(BTreeMap<K, V>);
}
// An impl of SortedMap for the standard library HashMap.
#[experimental]
impl<K, V, S, H> SortedMap<K, V> for HashMap<K, V, S>
    where K: Clone + Eq + Hash<H> + Ord,
          V: Clone,
          S: HashState<Hasher=H> + Default,
          H: Hasher<Output=u64> {
    sortedmap_impl!(HashMap<K, V, S>);
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::SortedMap;

    #[test]
    fn test_first() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.first().unwrap(), (1u32, 1u32));
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
        assert_eq!(map.last().unwrap(), (5u32, 5u32));
    }

    #[test]
    fn test_last_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.last_remove().unwrap(), (5u32, 5u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4)]);
    }

    #[test]
    fn test_head_map_noinclusive() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let head_map = map.head_map(&3, false);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(head_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2)]);
    }

    #[test]
    fn test_head_map_inclusive() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let head_map = map.head_map(&3, true);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(head_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3)]);
    }

    #[test]
    fn test_sub_map_noinclusive() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let sub_map = map.sub_map(&2, false, &4, false);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(sub_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(3u32, 3u32)]);
    }

    #[test]
    fn test_sub_map_nofrom_to() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let sub_map = map.sub_map(&2, false, &4, true);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(sub_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(3u32, 3u32), (4, 4)]);
    }

    #[test]
    fn test_sub_from_noto() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let sub_map = map.sub_map(&2, true, &4, false);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(sub_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(2u32, 2u32), (3, 3)]);
    }

    #[test]
    fn test_sub_map_inclusive() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let sub_map = map.sub_map(&2, true, &4, true);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(sub_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(2u32, 2u32), (3, 3), (4, 4)]);
    }

    #[test]
    fn test_tail_map_noinclusive() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let tail_map = map.tail_map(&3, false);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(tail_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(4u32, 4u32), (5, 5)]);
    }

    #[test]
    fn test_tail_map_inclusive() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let tail_map = map.tail_map(&3, true);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(tail_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(3u32, 3u32), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_ceiling() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.ceiling(&3).unwrap(), (3u32, 3u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_floor() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.floor(&3).unwrap(), (3u32, 3u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);

    }

    #[test]
    fn test_higher() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.higher(&3).unwrap(), (4u32, 4u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_lower() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.lower(&3).unwrap(), (2u32, 2u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);

    }
}
