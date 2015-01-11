use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::collections::hash_state::HashState;
use std::default::Default;
use std::hash::{Hash, Hasher};

use super::traits::{SortedMap, SortedSet};

macro_rules! sortedset_impl {
    ($typ:ty) => (
        fn first(&mut self, remove: bool) -> Option<T> {
            if self.is_empty() { return None }

            let ret = self.iter().min().unwrap().clone();
            if remove {
                self.remove(&ret);
            }
            Some(ret)
        }

        fn last(&mut self, remove: bool) -> Option<T> {
            if self.is_empty() { return None }

            let ret = self.iter().max().unwrap().clone();
            if remove {
                self.remove(&ret);
            }
            Some(ret)
        }

        fn head_set(&self, elem: &T, inclusive: bool) -> $typ {
            if inclusive {
                return self.iter().cloned().filter(|x| x <= elem).collect();
            } else {
                return self.iter().cloned().filter(|x| x < elem).collect();
            }
        }

        fn sub_set(&self, from_elem: &T, from_inclusive: bool, to_elem: &T, to_inclusive:bool) -> $typ {
            assert!(from_elem <= to_elem);

            if from_inclusive && to_inclusive {
                return self.iter().cloned().filter(|x| x >= from_elem && x <= to_elem).collect();
            } else if from_inclusive && !to_inclusive {
                return self.iter().cloned().filter(|x| x >= from_elem && x < to_elem).collect();
            } else if !from_inclusive && to_inclusive {
                return self.iter().cloned().filter(|x| x > from_elem && x <= to_elem).collect();
            } else {
                return self.iter().cloned().filter(|x| x > from_elem && x < to_elem).collect();
            }
        }

        fn tail_set(&self, elem: &T, inclusive: bool) -> $typ {
            if inclusive {
                return self.iter().cloned().filter(|x| x >= elem).collect();
            } else {
                return self.iter().cloned().filter(|x| x > elem).collect();
            }
        }
    );
}

impl<T> SortedSet<T> for BTreeSet<T>
    where T: Clone + Ord {
    sortedset_impl!(BTreeSet<T>);
}
impl<T, S, H> SortedSet<T> for HashSet<T, S>
    where T: Clone + Eq + Hash<H> + Ord,
          S: HashState<Hasher=H> + Default,
          H: Hasher<Output=u64> {
    sortedset_impl!(HashSet<T, S>);
}

macro_rules! sortedmap_impl {
    ($typ:ty) => (
        fn first_key(&mut self, remove: bool) -> Option<K> {
            if self.is_empty() { return None }

            let ret = self.keys().min().unwrap().clone();
            if remove {
                self.remove(&ret);
            }
            Some(ret)
        }

        fn last_key(&mut self, remove: bool) -> Option<K> {
            if self.is_empty() { return None }

            let ret = self.keys().max().unwrap().clone();
            if remove {
                self.remove(&ret);
            }
            Some(ret)
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
    use super::super::traits::SortedSet;

    use std::collections::BTreeSet;

    #[test]
    fn test_first_noremove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.first(false).unwrap(), 1u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_first_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.first(true).unwrap(), 1u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![2u32, 3, 4, 5]);
    }

    #[test]
    fn test_last_noremove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.last(false).unwrap(), 5u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_last_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.last(true).unwrap(), 5u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4]);
    }

    #[test]
    fn test_head_set_noinclusive() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let head_set = set.head_set(&3, false);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(head_set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2]);
    }

    #[test]
    fn test_head_set_inclusive() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let head_set = set.head_set(&3, true);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(head_set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3]);

    }

    // FIXME: Add subset tests!

    #[test]
    fn test_tail_set_noinclusive() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let tail_set = set.tail_set(&3, false);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(tail_set.into_iter().collect::<Vec<u32>>(), vec![4u32, 5]);
    }

    #[test]
    fn test_tail_set_inclusive() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let tail_set = set.tail_set(&3, true);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(tail_set.into_iter().collect::<Vec<u32>>(), vec![3u32, 4, 5]);
    }

    // FIXME: Add provided fn tests!

    // FIXME: Add map tests!
}
