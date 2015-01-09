use std::collections::{HashMap, BTreeMap, VecMap, HashSet, BTreeSet};

use super::traits::{SortedMap, SortedSet};

impl<T: Ord + Clone> SortedSet<T> for BTreeSet<T> {
    fn first(&mut self, remove: bool) -> Option<T> {
        if self.is_empty() { return None }

        let mut vec: Vec<T> = self.iter().cloned().collect();
        let ret = vec.remove(0);
        if remove {
            self.remove(&ret);
        }
        Some(ret)
    }

    fn last(&mut self, remove: bool) -> Option<T> {
        if self.is_empty() { return None }

        let mut vec: Vec<T> = self.iter().rev().cloned().collect();
        let ret = vec.remove(0);
        if remove {
            self.remove(&ret);
        }
        Some(ret)
    }

    fn head_set(&self, elem: &T, inclusive: bool) -> BTreeSet<T> {
        let mut vec: Vec<T>;
        if inclusive {
            vec = self.iter().cloned().filter(|x| x <= elem).collect();
        } else {
            vec = self.iter().cloned().filter(|x|  x < elem).collect();
        }
        vec.into_iter().collect::<BTreeSet<T>>()
    }

    fn sub_set(&self, from_elem: &T, from_inclusive: bool, to_elem: &T, to_inclusive:bool) -> BTreeSet<T> {
        assert!(from_elem <= to_elem);

        let mut vec: Vec<T>;
        if from_inclusive && to_inclusive {
            vec = self.iter().cloned().filter(|x| x >= from_elem && x <= to_elem).collect();
        } else if from_inclusive && !to_inclusive {
            vec = self.iter().cloned().filter(|x| x >= from_elem && x < to_elem).collect();
        } else if !from_inclusive && to_inclusive {
            vec = self.iter().cloned().filter(|x| x > from_elem && x <= to_elem).collect();
        } else {
            vec = self.iter().cloned().filter(|x| x > from_elem && x < to_elem).collect();
        }
        vec.into_iter().collect::<BTreeSet<T>>()
    }

    fn tail_set(&self, elem: &T, inclusive: bool) -> BTreeSet<T> {
        let mut vec: Vec<T>;
        if inclusive {
            vec = self.iter().cloned().filter(|x| x >= elem).collect();
        } else {
            vec = self.iter().cloned().filter(|x| x > elem).collect();
        }
        vec.into_iter().collect::<BTreeSet<T>>()
    }
}

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
