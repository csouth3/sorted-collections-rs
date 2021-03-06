// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A trait extending ordered maps, along with associated impls and iterators.

use std::collections::Bound::{self, Excluded, Included, Unbounded};
use std::collections::btree_map::{self, BTreeMap};

/// An extension trait for a `Map` whose keys have a defined total ordering.
/// This trait defines convenience methods which take advantage of the map's ordering.
pub trait SortedMapExt<K, V>
    where K: Clone + Ord
{
    /// A by-value iterator yielding key-value pairs whose keys fall within a given range and
    /// which have just been removed from this map.
    type RangeRemove;

    /// Returns an immutable reference to the first (least) key currently in this map.
    /// Returns `None` if this map is empty.
    ///
    /// # Examples
    ///
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
    /// ```ignore
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
            match self.first().cloned() {
                Some(first) => {
                    let val = self.remove(&first);
                    debug_assert!(val.is_some());
                    Some((first, val.unwrap()))
                },
                _ => {
                    None
                },
            }
        }

        fn last(&self) -> Option<&K> {
            self.keys().max()
        }

        fn last_remove(&mut self) -> Option<(K, V)> {
            match self.last().cloned() {
                Some(last) => {
                    let val = self.remove(&last);
                    debug_assert!(val.is_some());
                    Some((last, val.unwrap()))
                },
                _ => {
                    None
                },
            }
        }

        fn ceiling(&self, key: &K) -> Option<&K> {
            self.range(Included(key), Unbounded).map(|(k, _)| k).min()
        }

        fn ceiling_remove(&mut self, key: &K) -> Option<(K, V)> {
            match self.ceiling(key).cloned() {
                Some(ceiling) => {
                    let val = self.remove(&ceiling);
                    debug_assert!(val.is_some());
                    Some((ceiling, val.unwrap()))
                },
                _ => {
                    None
                },
            }
        }

        fn floor(&self, key: &K) -> Option<&K> {
            self.range(Unbounded, Included(key)).map(|(k, _)| k).max()
        }

        fn floor_remove(&mut self, key: &K) -> Option<(K, V)> {
            match self.floor(key).cloned() {
                Some(floor) => {
                    let val = self.remove(&floor);
                    debug_assert!(val.is_some());
                    Some((floor, val.unwrap()))
                },
                _ => {
                    None
                },
            }
        }

        fn higher(&self, key: &K) -> Option<&K> {
            self.range(Excluded(key), Unbounded).map(|(k, _)| k).min()
        }

        fn higher_remove(&mut self, key: &K) -> Option<(K, V)> {
            match self.higher(key).cloned() {
                Some(higher) => {
                    let val = self.remove(&higher);
                    debug_assert!(val.is_some());
                    Some((higher, val.unwrap()))
                },
                _ => {
                    None
                },
            }
        }

        fn lower(&self, key: &K) -> Option<&K> {
            self.range(Unbounded, Excluded(key)).map(|(k, _)| k).max()
        }

        fn lower_remove(&mut self, key: &K) -> Option<(K, V)> {
            match self.lower(key).cloned() {
                Some(lower) => {
                    let val = self.remove(&lower);
                    debug_assert!(val.is_some());
                    Some((lower, val.unwrap()))
                },
                _ => {
                    None
                },
            }
        }

        fn range_remove(&mut self, from_key: Bound<&K>, to_key: Bound<&K>) -> $rangeremoveret {
            let keys: Vec<K> = self.range(from_key, to_key).map(|(k, _)| k.clone()).collect();
            let values: Vec<V> = keys.iter().map(|k| self.remove(k).unwrap()).collect();
            let ret: $typ = keys.into_iter().zip(values.into_iter()).collect();

            $rangeremove(ret.into_iter())
        }
    );
}

// An impl of SortedMapExt for the standard library BTreeMap
impl<'a, K, V> SortedMapExt<K, V> for BTreeMap<K, V>
    where K: Clone + Ord
{
    type RangeRemove = BTreeMapRangeRemove<K, V>;

    sortedmap_impl!(BTreeMap<K, V>, BTreeMapRangeRemove, BTreeMapRangeRemove<K, V>);
}

/// A double-ended by-value iterator for removing pairs from a BTreeMap.
pub struct BTreeMapRangeRemove<K, V>(btree_map::IntoIter<K, V>);

impl<K, V> Iterator for BTreeMapRangeRemove<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}
impl<K, V> DoubleEndedIterator for BTreeMapRangeRemove<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> { self.0.next_back() }
}
impl<K, V> ExactSizeIterator for BTreeMapRangeRemove<K, V> {
    fn len(&self) -> usize { self.0.len() }
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
