// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::Bound;
use std::collections::btree_map::{BTreeMap, self};

/// An extension trait for a `Map` whose keys have a defined total ordering.
/// This trait defines convenience methods which take advantage of the map's ordering.
pub trait SortedMapExt<K, V>
    where K: Clone + Ord,
          V: Clone 
{
    /// A by-value iterator yielding key-value pairs whose keys fall within a given range and
    /// which have just been removed from this map.
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.first().unwrap(), &1u32);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.first_remove().unwrap(), (1u32, 1u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(2u32, 2u32), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.last().unwrap(), &5u32);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.last_remove().unwrap(), (5u32, 5u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4)]);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.ceiling(&3).unwrap(), &3u32);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.ceiling_remove(&3).unwrap(), (3u32, 3u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (4, 4), (5, 5)]);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.floor(&3).unwrap(), &3u32);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.floor_remove(&3).unwrap(), (3u32, 3u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (4, 4), (5, 5)]);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.higher(&3).unwrap(), &4u32);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.higher_remove(&3).unwrap(), (4u32, 4u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (5, 5)]);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.lower(&3).unwrap(), &2u32);
    /// }
    /// ```
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
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.lower_remove(&3).unwrap(), (2u32, 2u32));
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (3, 3), (4, 4), (5, 5)]);
    /// }
    /// ```
    fn lower_remove(&mut self, key: &K) -> Option<(K, V)>;

    /// Removes the key-value pairs of this map whose keys lie in the range starting at `from_key`
    /// and ending at `to_key`, and returns a double-ended by-value iterator over the removed pairs.
    ///
    /// If `from_key` is `Unbounded`, then it will be treated as "negative infinity", and
    /// if `to_key` is `Unbounded`, then it will be treated as "positive infinity".  Thus,
    /// `range_remove(Unbounded, Unbounded)` will clear the map and return a by-value
    /// iterator over all of the pairs which were in it.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::Bound::{Excluded, Included};
    /// use std::collections::BTreeMap;
    /// use sorted_collections::SortedMapExt;
    ///
    /// fn main() {
    ///     let mut map: BTreeMap<u32, u32> =
    ///         vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
    ///     assert_eq!(map.range_remove(Included(&2), Excluded(&4)).collect::<Vec<(u32, u32)>>(),
    ///         vec![(2u32, 2u32), (3, 3)]);
    ///     assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
    ///         vec![(1u32, 1u32), (4, 4), (5, 5)]);
    /// }
    /// ```
    fn range_remove(&mut self, from_key: Bound<&K>, to_key: Bound<&K>) -> Self::RangeRemove;
}

// A generic reusable impl of SortedMapExt.
macro_rules! sortedmap_impl {
    ($typ:ty, $rangeremove:ident, $rangeremoveret:ty) => (
        fn first(&self) -> Option<&K> {
            self.keys().min()
        }

        fn first_remove(&mut self) -> Option<(K, V)> {
            if let Some(key) = self.first().cloned() {
                let val = self.remove(&key);
                assert!(val.is_some());
                Some((key, val.unwrap()))
            } else {
                None
            }
        }

        fn last(&self) -> Option<&K> {
            self.keys().max()
        }

        fn last_remove(&mut self) -> Option<(K, V)> {
            if let Some(key) = self.last().cloned() {
                let val = self.remove(&key);
                assert!(val.is_some());
                Some((key, val.unwrap()))
            } else {
                None
            }
        }

        fn ceiling(&self, key: &K) -> Option<&K> {
            self.keys().filter(|&k| k >= key).min()
        }

        fn ceiling_remove(&mut self, key: &K) -> Option<(K, V)> {
            if let Some(ceiling) = self.ceiling(key).cloned() {
                let val = self.remove(&ceiling);
                assert!(val.is_some());
                Some((ceiling, val.unwrap()))
            } else {
                None
            }
        }

        fn floor(&self, key: &K) -> Option<&K> {
            self.keys().filter(|&k| k <= key).max()
        }

        fn floor_remove(&mut self, key: &K) -> Option<(K, V)> {
            if let Some(floor) = self.floor(key).cloned() {
                let val = self.remove(&floor);
                assert!(val.is_some());
                Some((floor, val.unwrap()))
            } else {
                None
            }
        }

        fn higher(&self, key: &K) -> Option<&K> {
            self.keys().filter(|&k| k > key).min()
        }

        fn higher_remove(&mut self, key: &K) -> Option<(K, V)> {
            if let Some(higher) = self.higher(key).cloned() {
                let val = self.remove(&higher);
                assert!(val.is_some());
                Some((higher, val.unwrap()))
            } else {
                None
            }
        }

        fn lower(&self, key: &K) -> Option<&K> {
            self.keys().filter(|&k| k < key).max()
        }

        fn lower_remove(&mut self, key: &K) -> Option<(K, V)> {
            if let Some(lower) = self.lower(key).cloned() {
                let val = self.remove(&lower);
                assert!(val.is_some());
                Some((lower, val.unwrap()))
            } else {
                None
            }
        }

        fn range_remove(&mut self, from_key: Bound<&K>, to_key: Bound<&K>) -> $rangeremoveret {
            let ret: $typ = self.range(from_key, to_key)
                                .map(|(ref k, ref v)| ((**k).clone(), (**v).clone()))
                                .collect();

            for key in ret.keys() {
                assert!(self.remove(key).is_some())
            }
            $rangeremove { iter: ret.into_iter() }
        }
    );
}

// An impl of SortedMapExt for the standard library BTreeMap
impl<'a, K, V> SortedMapExt<K, V> for BTreeMap<K, V>
    where K: Clone + Ord,
          V: Clone
{
    type RangeRemove = BTreeMapRangeRemove<K, V>;

    sortedmap_impl!(BTreeMap<K, V>, BTreeMapRangeRemove, BTreeMapRangeRemove<K, V>);
}

pub struct BTreeMapRangeRemove<K, V> {
    iter: btree_map::IntoIter<K, V>
}

impl<K, V> Iterator for BTreeMapRangeRemove<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
impl<K, V> DoubleEndedIterator for BTreeMapRangeRemove<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> { self.iter.next_back() }
}
impl<K, V> ExactSizeIterator for BTreeMapRangeRemove<K, V> {
    fn len(&self) -> usize { self.iter.len() }
}

#[cfg(test)]
mod tests {
    use std::collections::Bound::{Excluded, Included};
    use std::collections::BTreeMap;

    use super::SortedMapExt;

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
    fn test_range_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.range_remove(Included(&2), Excluded(&4)).collect::<Vec<(u32, u32)>>(),
            vec![(2u32, 2u32), (3, 3)]);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(),
            vec![(1u32, 1u32), (4, 4), (5, 5)]);
    }
}
