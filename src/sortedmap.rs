use std::collections::{BTreeMap, HashMap};
use std::collections::hash_state::HashState;
use std::default::Default;
use std::hash::{Hash, Hasher};

/// An extension trait for a `Map` whose keys have a defined total ordering.
/// This trait provides convenience methods which take advantage of the map's ordering.
pub trait SortedMap<K, V> : Sized
    where K: Clone + Ord,
          V: Clone {
    /// Returns the first (lowest) key currently in this map, and its corresponding value,
    /// and optionally removes it from the map.
    /// Returns `None` if this map is empty.
    fn first(&mut self, remove: bool) -> Option<(K, V)>;

    /// Returns the last (highest) key currently in this map, and its corresponding value,
    /// and optionally removes it from the map.
    /// Returns `None` if this map is empty.
    fn last(&mut self, remove: bool) -> Option<(K, V)>;

    /// Returns the key-value pairs of this map whose keys are less than (or equal to,
    /// if `inclusive` is true) `key`, as a new instance of the same type of map.
    fn head_map(&self, key: &K, inclusive: bool) -> Self;

    /// Returns the key-value pairs of this map whose keys range from `from_key` to
    /// `to_key`, as a new instance of the same type of map.
    fn sub_map(&self, from_key: &K, from_inclusive: bool, to_key: &K, to_inclusive: bool) -> Self;

    /// Returns the key-value pairs of this map whose keys are greater than (or equal to,
    /// if `inclusive` is true) `key`, as a new instance of the same type of map.
    fn tail_map(&self, key: &K, inclusive: bool) -> Self;

    /// Returns the least key greater than or equal to `key`, and its corresponding value.
    /// Returns `None` if there is no such key.
    fn ceiling(&self, key: &K) -> Option<(K, V)> {
        let mut tail = self.tail_map(key, true);
        tail.first(false)
    }

    /// Returns the greatest key less than or equal to `key`, and its corresponding value.
    /// Returns `None` if there is no such key.
    fn floor(&self, key: &K) -> Option<(K, V)> {
        let mut head = self.head_map(key, true);
        head.last(false)
    }

    /// Returns the least key strictly greater than the given key, and its corresponding value.
    /// Returns `None` if there is no such key.
    fn higher(&self, key: &K) -> Option<(K, V)> {
        let mut tail = self.tail_map(key, false);
        tail.first(false)
    }

    /// Returns the greatest key strictly less than the given key, and its corresponding value.
    /// Returns `None` if there is no such key.
    fn lower(&self, key: &K) -> Option<(K, V)> {
        let mut head = self.head_map(key, false);
        head.last(false)
    }
}

macro_rules! sortedmap_impl {
    ($typ:ty) => (
        fn first(&mut self, remove: bool) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.keys().min().unwrap().clone();
            let val: V;

            if remove {
                val = self.remove(&key).unwrap();
            } else {
                val = self.get(&key).unwrap().clone();
            }

            Some((key, val))
        }

        fn last(&mut self, remove: bool) -> Option<(K, V)> {
            if self.is_empty() { return None }

            let key = self.keys().max().unwrap().clone();
            let val: V;

            if remove {
                val = self.remove(&key).unwrap();
            } else {
                val = self.get(&key).unwrap().clone();
            }

            Some((key, val))
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

impl<K, V> SortedMap<K, V> for BTreeMap<K, V>
    where K: Clone + Ord,
          V: Clone {
    sortedmap_impl!(BTreeMap<K, V>);
}
impl<K, V, S, H> SortedMap<K, V> for HashMap<K, V, S>
    where K: Clone + Eq + Hash<H> + Ord,
          V: Clone,
          S: HashState<Hasher=H> + Default,
          H: Hasher<Output=u64> {
    sortedmap_impl!(HashMap<K, V, S>);
}

#[cfg(test)]
mod tests {
    use super::SortedMap;

    use std::collections::BTreeMap;

    #[test]
    fn test_first_noremove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.first(false).unwrap(), (1u32, 1u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_first_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.first(true).unwrap(), (1u32, 1u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(2u32, 2u32), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_last_noremove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.last(false).unwrap(), (5u32, 5u32));
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
    }

    #[test]
    fn test_last_remove() {
        let mut map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        assert_eq!(map.last(true).unwrap(), (5u32, 5u32));
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
    fn test_tail_set_noinclusive() {
        let map: BTreeMap<u32, u32> = vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)].into_iter().collect();
        let tail_map = map.tail_map(&3, false);
        assert_eq!(map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(1u32, 1u32), (2, 2), (3, 3), (4, 4), (5, 5)]);
        assert_eq!(tail_map.into_iter().collect::<Vec<(u32, u32)>>(), vec![(4u32, 4u32), (5, 5)]);
    }

    #[test]
    fn test_tail_set_inclusive() {
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
