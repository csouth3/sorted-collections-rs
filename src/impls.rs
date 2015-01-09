use std::collections::BTreeSet;

use super::traits::SortedSet;

macro_rules! sortedset_impl {
    ($typ:ty) => (
        impl<T: Ord + Clone> SortedSet<T> for $typ {
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
                    return self.iter().cloned().filter(|x|  x < elem).collect();
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
        }
    );
}
sortedset_impl!(BTreeSet<T>);

#[cfg(test)]
mod tests {
    use test;

    use super::super::traits::{SortedMap, SortedSet};

    #[test]
    fn test_sub_set() {
        use std::collections::BTreeSet;

        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        let sub_set = set.sub_set(&2, true, &4, true);
        let v: Vec<u32> = sub_set.into_iter().collect();
        assert_eq!(v, vec![2u32, 3, 4]);
    }
}
