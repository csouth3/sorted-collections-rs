use std::collections::btree_set::{BTreeSet, self};
use std::collections::hash_set::{HashSet, self};
use std::collections::hash_state::HashState;
use std::default::Default;
use std::hash::{Hash, Hasher};
use std::iter::Peekable;

/// An extension trait for a `Set` whose elements have a defined total ordering.
/// This trait provides convenience methods which take advantage of the set's ordering.
/// The provided methods may be overridden if desired to provide more efficient
/// implementations.
#[experimental]
pub trait SortedSet<T> : Sized
    where T: Clone + Ord {

    /// An iterator over immutable references to this set's elements within a given range.
    #[experimental]
    type Range;

    /// A by-value iterator yielding elements within a given range which have just been removed
    /// from this set.
    #[experimental]
    type RangeRemove;

    /// Returns an immutable reference to the first (least) element currently in this set.
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
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.first().unwrap(), &1u32);
    /// }
    /// ```
    #[experimental]
    fn first(&self) -> Option<&T>;

    /// Removes and returns the first (least) element currently in this set.
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
    ///     assert_eq!(set.first_remove().unwrap(), 1u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![2u32, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn first_remove(&mut self) -> Option<T>;

    /// Returns an immutable reference to the last (greatest) element currently in this set.
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
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.last().unwrap(), &5u32);
    /// }
    /// ```
    #[experimental]
    fn last(&self) -> Option<&T>;

    /// Removes and returns the last (greatest) element currently in this set.
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
    ///     assert_eq!(set.last_remove().unwrap(), 5u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4]);
    /// }
    /// ```
    #[experimental]
    fn last_remove(&mut self) -> Option<T>;

    /// Returns an immutable reference to the least element in this set greater than or equal to `elem`.
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
    ///     assert_eq!(set.ceiling(&3).unwrap(), &3u32);
    /// }
    /// ```
    #[experimental]
    fn ceiling(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the least element in this set greater than or equal to `elem`.
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
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.ceiling_remove(&3).unwrap(), 3u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn ceiling_remove(&mut self, elem: &T) -> Option<T>;

    /// Returns an immutable reference to the greatest element in this set less than or equal to `elem`.
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
    ///     assert_eq!(set.floor(&3).unwrap(), &3u32);
    /// }
    /// ```
    #[experimental]
    fn floor(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the greatest element in this set less than or equal to `elem`.
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
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.floor_remove(&3).unwrap(), 3u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn floor_remove(&mut self, elem: &T) -> Option<T>;

    /// Returns an immutable reference to the least element in this set strictly greater than `elem`.
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
    ///     assert_eq!(set.higher(&3).unwrap(), &4u32);
    /// }
    /// ```
    #[experimental]
    fn higher(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the least element in this set strictly greater than `elem`.
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
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.higher_remove(&3).unwrap(), 4u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 5]);
    /// }
    /// ```
    #[experimental]
    fn higher_remove(&mut self, elem: &T) -> Option<T>;

    /// Returns an immutable reference to the greatest element in this set strictly less than `elem`.
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
    ///     assert_eq!(set.lower(&3).unwrap(), &2u32);
    /// }
    /// ```
    #[experimental]
    fn lower(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the greatest element in this set strictly less than `elem`.
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
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.lower_remove(&3).unwrap(), 2u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 3, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn lower_remove(&mut self, elem: &T) -> Option<T>;

    /// Returns an iterator over immutable references to the elements
    /// of this set in the range [from_elem, to_elem).  Note that this iterator
    /// need not necessarily yield the values in ascending order!
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
    ///     assert_eq!(set.range(&2, &4).map(|&x| x).collect::<Vec<u32>>(), vec![2u32, 3]);
    /// }
    /// ```
    #[experimental]
    fn range(&self, from_elem: &T, to_elem: &T) -> Self::Range;

    /// Removes the elements of this set in the range [from_elem, to_elem), and returns
    /// a by-value iterator over the removed elements.  Note that this iterator need not
    /// necessarily yield the values in ascending order!
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
    ///     assert_eq!(set.range_remove(&2, &4).collect::<Vec<u32>>(), vec![2u32, 3]);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 4, 5]);
    /// }
    /// ```
    #[experimental]
    fn range_remove(&mut self, from_elem: &T, to_elem: &T) -> Self::RangeRemove;

}

// A generic reusable impl of SortedSet.
macro_rules! sortedset_impl {
    ($typ:ty, $range:ident, $rangeret:ty, $rangeremove: ident, $rangeremoveret:ty)=> (
        fn first(&self) -> Option<&T> {
            self.iter().min()
        }

        fn first_remove(&mut self) -> Option<T> {
            if let Some(ret) = self.first().cloned() {
                assert!(self.remove(&ret));
                Some(ret)
            } else {
                None
            }
        }

        fn last(&self) -> Option<&T> {
            self.iter().max()
        }

        fn last_remove(&mut self) -> Option<T> {
            if let Some(ret) = self.iter().last().cloned() {
                assert!(self.remove(&ret));
                Some(ret)
            } else {
                None
            }
        }

        fn ceiling(&self, elem: &T) -> Option<&T> {
            self.range(elem, self.last().unwrap()).min()
        }

        fn ceiling_remove(&mut self, elem: &T) -> Option<T> {
            if let Some(ceiling) = self.ceiling(elem).cloned() {
                assert!(self.remove(&ceiling));
                Some(ceiling)
            } else {
                None
            }
        }

        fn floor(&self, elem: &T) -> Option<&T> {
            self.iter().filter(|&x| x <= elem).max()
        }

        fn floor_remove(&mut self, elem: &T) -> Option<T> {
            if let Some(floor) = self.floor(elem).cloned() {
                assert!(self.remove(&floor));
                Some(floor)
            } else {
                None
            }
        }

        fn higher(&self, elem: &T) -> Option<&T> {
            self.iter().filter(|&x| x > elem).min()
        }

        fn higher_remove(&mut self, elem: &T) -> Option<T> {
            if let Some(higher) = self.higher(elem).cloned() {
                assert!(self.remove(&higher));
                Some(higher)
            } else {
                None
            }
        }

        fn lower(&self, elem: &T) -> Option<&T> {
            self.range(self.first().unwrap(), elem).max()
        }

        fn lower_remove(&mut self, elem: &T) -> Option<T> {
            if let Some(lower) = self.lower(elem).cloned() {
                assert!(self.remove(&lower));
                Some(lower)
            } else {
                None
            }
        }

        fn range(&self, from_elem: &T, to_elem: &T) -> $rangeret {
            $range {
                iter: self.iter().peekable(),
                lower: from_elem.clone(),
                upper: to_elem.clone(),
            }
        }

        fn range_remove(&mut self, from_elem: &T, to_elem: &T) -> $rangeremoveret {
            let remove: $typ = self.iter().cloned().filter(|x| x >= from_elem && x < to_elem).collect();
            for elem in remove.iter() {
                self.remove(elem);
            }
            $rangeremove { iter: remove.into_iter() }
        }
    );
}

// An impl of SortedSet for the standard library BTreeSet
#[experimental]
impl<'a, T> SortedSet<T> for BTreeSet<T>
    where T: Clone + Ord {
    type Range = BTreeSetRange<'a, T>;
    type RangeRemove = BTreeSetRangeRemove<T>;

    sortedset_impl!(BTreeSet<T>, BTreeSetRange, BTreeSetRange<T>, BTreeSetRangeRemove, BTreeSetRangeRemove<T>);
}
// An impl of SortedSet for the standard library HashSet
#[experimental]
impl<'a, T, S, H> SortedSet<T> for HashSet<T, S>
    where T: Clone + Eq + Hash<H> + Ord,
          S: HashState<Hasher=H> + Default,
          H: Hasher<Output=u64> {
    type Range = HashSetRange<'a, T>;
    type RangeRemove = HashSetRangeRemove<T>;

    sortedset_impl!(HashSet<T, S>, HashSetRange, HashSetRange<T>, HashSetRangeRemove, HashSetRangeRemove<T>);
}

#[experimental]
pub struct BTreeSetRange<'a, T: 'a> {
    iter: Peekable<&'a T, btree_set::Iter<'a, T>>,
    lower: T,
    upper: T,
}

#[experimental]
impl<'a, T: Ord> Iterator for BTreeSetRange<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            // If iterator is empty, return None.
            if self.iter.is_empty() { return None; }

            // If the next item is in range, yield it.
            if (*self.iter.peek().unwrap() >= &self.lower)
                && (*self.iter.peek().unwrap() < &self.upper) { return self.iter.next(); }

            // Otherwise, advance the iterator.
            else { self.iter.next(); }
        }
    }
}

#[experimental]
pub struct BTreeSetRangeRemove<T> {
    iter: btree_set::IntoIter<T>
}

#[experimental]
impl<T> Iterator for BTreeSetRangeRemove<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
#[experimental]
impl<T> DoubleEndedIterator for BTreeSetRangeRemove<T> {
    fn next_back(&mut self) -> Option<T> { self.iter.next_back() }
}
#[experimental]
impl<T> ExactSizeIterator for BTreeSetRangeRemove<T> {
    fn len(&self) -> usize { self.iter.len() }
}

#[experimental]
pub struct HashSetRange<'a, T: 'a> {
    iter: Peekable<&'a T, hash_set::Iter<'a, T>>,
    lower: T, 
    upper: T,
}

#[experimental]
impl<'a, T: Ord> Iterator for HashSetRange<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            // If the iterator is empty, return None.
            if self.iter.is_empty() { return None; }

            // If the next item is in range, yield it.
            if (*self.iter.peek().unwrap() >= &self.lower)
                && (*self.iter.peek().unwrap() < &self.upper) { return self.iter.next(); }

            // Otherwise, advance the iterator.
            else { self.iter.next(); }
        }
    }
}

#[experimental]
pub struct HashSetRangeRemove<T> {
    iter: hash_set::IntoIter<T>
}

#[experimental]
impl<T> Iterator for HashSetRangeRemove<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}
#[experimental]
impl<T> ExactSizeIterator for HashSetRangeRemove<T> {
    fn len(&self) -> usize { self.iter.len() }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::SortedSet;

    #[test]
    fn test_first() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.first().unwrap(), &1u32);
    }

    #[test]
    fn test_first_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.first_remove().unwrap(), 1u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![2u32, 3, 4, 5]);
    }

    #[test]
    fn test_last() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.last().unwrap(), &5u32);
    }

    #[test]
    fn test_last_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.last_remove().unwrap(), 5u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4]);
    }

    #[test]
    fn test_ceiling() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.ceiling(&3).unwrap(), &3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_ceiling_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.ceiling_remove(&3).unwrap(), 3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    }

    #[test]
    fn test_floor() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.floor(&3).unwrap(), &3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_floor_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.floor_remove(&3).unwrap(), 3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    }

    #[test]
    fn test_higher() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.higher(&3).unwrap(), &4u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_higher_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.higher_remove(&3).unwrap(), 4u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 5]);
    }

    #[test]
    fn test_lower() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.lower(&3).unwrap(), &2u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_lower_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.lower_remove(&3).unwrap(), 2u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 3, 4, 5]);
    }

    #[test]
    fn test_range() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.range(&2, &4).map(|&x| x).collect::<Vec<u32>>(), vec![2u32, 3]);
    }

    #[test]
    fn test_range_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.range_remove(&2, &4).collect::<Vec<u32>>(), vec![2u32, 3]);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 4, 5]);
    }
}
