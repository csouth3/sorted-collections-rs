use std::collections::{BTreeSet, HashSet};
use std::collections::hash_state::HashState;
use std::default::Default;
use std::hash::{Hash, Hasher};

/// An extension trait for a `Set` whose elements have a defined total ordering.
/// This trait provides convenience methods which take advantage of the set's ordering.
/// The provided methods may be overridden if desired to provide more efficient
/// implementations.
#[experimental]
pub trait SortedSet<T> : Sized
    where T: Clone + Ord {
    /// Returns the first (least) element currently in this set and optionally removes it
    /// from the set.
    /// Returns `None` if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.first(false).unwrap(), 1u32);
    ///     // The original set should remain unchanged since we opted not to remove.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn first(&mut self, remove: bool) -> Option<T>;

    /// Returns the last (greatest) element currently in this set and optionally removes it
    /// from the set.
    /// Returns `None` if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.last(false).unwrap(), 5u32);
    ///     // The original set should remain unchanged since we opted not to remove.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn last(&mut self, remove: bool) -> Option<T>;

    /// Returns the elements of this set which are less than (or equal to, if `inclusive`
    /// is true) `elem`, as a new instance of the same type of set.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     let head_set = set.head_set(&3, true);
    ///     // The original set shouldn't change.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    ///     assert_eq!(head_set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3]);
    /// }
    /// ```
    #[experimental]
    fn head_set(&self, elem: &T, inclusive: bool) -> Self;

    /// Returns the elements of this set ranging from `from_elem` to `to_elem`, as
    /// a new instance of the same type of set.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     let sub_set = set.sub_set(&2, false, &4, true);
    ///     // The original set shouldn't change.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    ///     // 2 isn't in the resulting set, while 4 is, just as we expected.
    ///     assert_eq!(sub_set.into_iter().collect::<Vec<u32>>(), vec![3u32, 4]);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if `from_elem > to_elem`.
    #[experimental]
    fn sub_set(&self, from_elem: &T, from_inclusive: bool, to_elem: &T, to_inclusive: bool) -> Self;

    /// Returns the elements of this set which are greater than (or equal to, if
    /// `inclusive` is true) `elem`, as a new instance of the same type of set.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     let tail_set = set.tail_set(&3, true);
    ///     // The original set shouldn't change.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    ///     assert_eq!(tail_set.into_iter().collect::<Vec<u32>>(), vec![3u32, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn tail_set(&self, elem: &T, inclusive: bool) -> Self;

    /// Returns the least element in this set greater than or equal to `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.ceiling(&3).unwrap(), 3u32);
    ///     // The original set shouldn't change.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn ceiling(&self, elem: &T) -> Option<T> {
        let mut tail = self.tail_set(elem, true);
        tail.first(false)
    }

    /// Returns the greatest element in this set less than or equal to `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.floor(&3).unwrap(), 3u32);
    ///     // The original set shouldn't change.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn floor(&self, elem: &T) -> Option<T> {
        let mut head = self.head_set(elem, true);
        head.last(false)
    }

    /// Returns the least element in this set strictly greater than `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.higher(&3).unwrap(), 4u32);
    ///     // The original set shouldn't change.
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn higher(&self, elem: &T) -> Option<T> {
        let mut tail = self.tail_set(elem, false);
        tail.first(false)
    }

    /// Returns the greatest element in this set strictly less than `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSet;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.lower(&3).unwrap(), 2u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn lower(&self, elem: &T) -> Option<T> {
        let mut head = self.head_set(elem, false);
        head.last(false)
    }
}

// A generic reusable impl of SortedSet.
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

        fn sub_set(&self, from_elem: &T, from_inclusive: bool, to_elem: &T, to_inclusive: bool) -> $typ {
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

// An impl of SortedSet for the standard library BTreeSet
#[experimental]
impl<T> SortedSet<T> for BTreeSet<T>
    where T: Clone + Ord {
    sortedset_impl!(BTreeSet<T>);
}
// An impl of SortedSet for the standard library HashSet
#[experimental]
impl<T, S, H> SortedSet<T> for HashSet<T, S>
    where T: Clone + Eq + Hash<H> + Ord,
          S: HashState<Hasher=H> + Default,
          H: Hasher<Output=u64> {
    sortedset_impl!(HashSet<T, S>);
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::SortedSet;

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

    #[test]
    fn test_sub_set_noinclusive() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let sub_set = set.sub_set(&2, false, &4, false);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(sub_set.into_iter().collect::<Vec<u32>>(), vec![3u32]);
    }

    #[test]
    fn test_sub_set_nofrom_to() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let sub_set = set.sub_set(&2, false, &4, true);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(sub_set.into_iter().collect::<Vec<u32>>(), vec![3u32, 4]);
    }

    #[test]
    fn test_sub_set_from_noto() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let sub_set = set.sub_set(&2, true, &4, false);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(sub_set.into_iter().collect::<Vec<u32>>(), vec![2u32, 3]);
    }

    #[test]
    fn test_sub_set_inclusive() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let sub_set = set.sub_set(&2, true, &4, true);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
        assert_eq!(sub_set.into_iter().collect::<Vec<u32>>(), vec![2u32, 3, 4]);
    }

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

    #[test]
    fn test_ceiling() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.ceiling(&3).unwrap(), 3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_floor() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.floor(&3).unwrap(), 3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_higher() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.higher(&3).unwrap(), 4u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_lower() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.lower(&3).unwrap(), 2u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }
}
