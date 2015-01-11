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
    fn first_key(&mut self, remove: bool) -> Option<(K, V)>;

    /// Returns the last (highest) key currently in this map, and its corresponding value,
    /// and optionally removes it from the map.
    /// Returns `None` if this map is empty.
    fn last_key(&mut self, remove: bool) -> Option<(K, V)>;

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
    fn ceiling_key(&self, key: &K) -> Option<(K, V)> {
        let mut tail = self.tail_map(key, true);
        tail.first_key(false)
    }

    /// Returns the greatest key less than or equal to `key`, and its corresponding value.
    /// Returns `None` if there is no such key.
    fn floor_key(&self, key: &K) -> Option<(K, V)> {
        let mut head = self.head_map(key, true);
        head.last_key(false)
    }

    /// Returns the least key strictly greater than the given key, and its corresponding value.
    /// Returns `None` if there is no such key.
    fn higher_key(&self, key: &K) -> Option<(K, V)> {
        let mut tail = self.tail_map(key, false);
        tail.first_key(false)
    }

    /// Returns the greatest key strictly less than the given key, and its corresponding value.
    /// Returns `None` if there is no such key.
    fn lower_key(&self, key: &K) -> Option<(K, V)> {
        let mut head = self.head_map(key, false);
        head.first_key(false)
    }
}

macro_rules! sortedmap_impl {
    ($typ:ty) => (
        fn first_key(&mut self, remove: bool) -> Option<(K, V)> {
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

        fn last_key(&mut self, remove: bool) -> Option<(K, V)> {
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
