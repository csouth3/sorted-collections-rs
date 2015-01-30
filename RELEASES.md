Version 0.0.1 (January 12, 2015)
-------------------------------
* Supported libcollections sets: BTreeSet and HashSet.
* Supported libcollections maps: BTreeMap and HashMap.

Version 0.0.2 (January 13, 2015)
--------------------------------
* Split `first()` and `last()` into `first()/first_remove()` and `last()/last_remove()`

Version 0.0.3 (January 16, 2015)
--------------------------------
* Entire API overhauled to be more consistent with those found in libcollections,
though things are not in final form yet.

Version 0.0.4 (January 22, 2015)
--------------------------------
BTreeSet and Map just got bounded iterators in libcollections, so just as a stopgap
until I decide more clearly what to do, rename some of my stuff to avoid the
naming conflict.

Version 0.0.5 (January 24, 2015)
--------------------------------
Various cleanups, removed support for Hash{Set, Map}, traits renamed.

Version 0.0.6 (January 30, 2015)
--------------------------------
Removed some redundant features in favor of libcollections bounded iterators.
