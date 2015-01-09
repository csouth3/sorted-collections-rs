/// An extension trait for a `Set` whose elements have a defined total ordering.
/// This trait provides convenience methods which take advantage of the set's ordering.
pub trait SortedSet<T: Ord + Clone> : Sized {
    /// Returns the first (lowest) element currently in this set and optionally removes it
    /// from the set.
    /// Returns `None` if this set is empty.
    fn first(&mut self, remove: bool) -> Option<T>;

    /// Returns the last (highest) element current in this set and optionally removes it
    /// from the set.
    /// Returns `None` if this set is empty.
    fn last(&mut self, remove: bool) -> Option<T>;

    /// Returns the elements of this set which are less than (or equal to, if `inclusive`
    /// is true) `elem`, as a new instance of the same type of set.
    fn head_set(&self, elem: &T, inclusive: bool) -> Self;

    /// Returns the elements of this set ranging from `from_elem` to `to_elem`, as
    /// a new instance of the same type of set.
    fn sub_set(&self, from_elem: &T, from_inclusive: bool, to_elem: &T, to_inclusive: bool) -> Self;

    /// Returns the elements of this set which are greater than (or equal to, if
    /// `inclusive` is true) `elem`, as a new instance of the same type of set.
    fn tail_set(&self, elem: &T, inclusive: bool) -> Self;
    
    /// Returns the least element in this set greater than or equal to `elem`.
    /// Returns `None` if there is no such element.
    fn ceiling(&self, elem: &T) -> Option<T> {
        let mut tail = self.tail_set(elem, true);
        tail.first(false)
    }

    /// Returns the greatest element in this set less than or equal to `elem`.
    /// Returns `None` if there is no such element.
    fn floor(&self, elem: &T) -> Option<T> {
        let mut head = self.head_set(elem, true);
        head.last(false)
    }

    /// Returns the least element in this set strictly greater than `elem`.
    /// Returns `None` if there is no such element.
    fn higher(&self, elem: &T) -> Option<T> {
        let mut tail = self.tail_set(elem, false);
        tail.first(false)
    }

    /// Returns the greatest element in this set strictly less than `elem`.
    /// Returns `None` if there is no such element.
    fn lower(&self, elem: &T) -> Option<T> {
        let mut head = self.head_set(elem, false);
        head.first(false)
    }
}

/// An extension trait for a `Map` whose keys have a defined total ordering.
/// This trait provides convenience methods which take advantage of the map's ordering.
pub trait SortedMap<K: Ord + Clone, V: Clone> : Sized {
    /// Returns the first (lowest) key currently in this map and optionally removes it
    /// from the map.
    /// Returns `None` if this map is empty.
    fn first_key(&mut self, remove: bool) -> Option<K>;

    /// Returns the last (highest) key currently in this map and optionally removes it
    /// from the map.
    /// Returns `None` if this map is empty.
    fn last_key(&mut self, remove: bool) -> Option<K>;

    /// Returns the key-value pairs of this map whose keys are less than (or equal to,
    /// if `inclusive` is true) `key`, as a new instance of the same type of map.
    fn head_map(&self, key: &K, inclusive: bool) -> Self;

    /// Returns the key-value pairs of this map whose keys range from `from_key` to
    /// `to_key`, as a new instance of the same type of map.
    fn sub_map(&self, from_key: &K, from_inclusive: bool, to_key: &K, to_inclusive: bool) -> Self;

    /// Returns the key-value pairs of this map whose keys are greater than (or equal to,
    /// if `inclusive` is true) `key`, as a new instance of the same type of map.
    fn tail_map(&self, key: &K, inclusive: bool) -> Self;

    /// Returns the least key greater than or equal to `key`.
    /// Returns `None` if there is no such key.
    fn ceiling_key(&self, key: &K) -> Option<K> {
        let mut tail = self.tail_map(key, true);
        tail.first_key(false)
    }

    /// Returns the greatest key less than or equal to `key`.
    /// Returns `None` if there is no such key.
    fn floor_key(&self, key: &K) -> Option<K> {
        let mut head = self.head_map(key, true);
        head.last_key(false)
    }

    /// Returns the least key strictly greater than the given key.
    /// Returns `None` if there is no such key.
    fn higher_key(&self, key: &K) -> Option<K> {
        let mut tail = self.tail_map(key, false);
        tail.first_key(false)
    }

    /// Returns the greatest key strictly less than the given key.
    /// Returns `None` if there is no such key.
    fn lower_key(&self, key: &K) -> Option<K> {
        let mut head = self.head_map(key, false);
        head.first_key(false)
    }
}
