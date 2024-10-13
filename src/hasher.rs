//! This implementation uses a lot of hash maps. This is a faster (but worse) hasher.
//! We make some effort to make the HashMap and HashSet act the same as the standard
//! types, so that we can easily replace them again.

use std::{
    collections,
    hash::{BuildHasher, Hash, Hasher},
    ops::{Deref, DerefMut},
};

type InnerHashMap<K, V> = collections::HashMap<K, V, FastHasherBuilder>;
type InnerHashSet<K> = collections::HashSet<K, FastHasherBuilder>;

/// HashMap wrapper that uses the faster hasher. This is a wrapper and not
/// a type alias so I can implement `new` for the type.
#[derive(Clone)]
pub struct HashMap<K: Eq + Hash, V>(InnerHashMap<K, V>);

/// HashSet wrapper that uses the faster hasher. This is a wrapper and not
/// a type alias so I can implement `new` for the type.
#[derive(Clone)]
pub struct HashSet<K: Eq + Hash>(InnerHashSet<K>);

/// This is a faster hasher.
#[derive(Clone, Copy)]
pub struct FastHasher(u64);

/// This is a builder for the faster hasher.
#[derive(Clone, Copy)]
pub struct FastHasherBuilder;

// These have *not* been carefully chosen.
const DEFAULT_SEED: u64 = 0x35ef47c8a29c2134;
const MULTIPLIER0: u64 = 0x5851f42d4c957f2d;
const MULTIPLIER1: u64 = 0x14057b7ef767814f;

impl FastHasher {
    /// Create a new hasher initialized with the default seed.
    fn new() -> Self {
        Self(DEFAULT_SEED)
    }
}

impl Default for FastHasherBuilder {
    fn default() -> Self {
        FastHasherBuilder
    }
}

impl BuildHasher for FastHasherBuilder {
    type Hasher = FastHasher;

    fn build_hasher(&self) -> Self::Hasher {
        Self::Hasher::new()
    }
}

impl Hasher for FastHasher {
    fn finish(&self) -> u64 {
        let mul = (self.0 as u128) * (MULTIPLIER1 as u128);
        (mul >> 64) as u64 ^ mul as u64
    }

    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut val = 0;
            for &b in chunk {
                val = (val << 8) + b as u64;
            }
            self.write_u64(val);
        }
    }

    fn write_u8(&mut self, i: u8) {
        self.write_u64(i as u64);
    }

    fn write_u16(&mut self, i: u16) {
        self.write_u64(i as u64);
    }

    fn write_u32(&mut self, i: u32) {
        self.write_u64(i as u64);
    }

    fn write_u64(&mut self, i: u64) {
        let mul = ((self.0 ^ i) as u128) * (MULTIPLIER0 as u128);
        self.0 = (mul >> 64) as u64 ^ mul as u64;
    }

    fn write_u128(&mut self, i: u128) {
        self.write_u64(i as u64);
        self.write_u64((i >> 64) as u64);
    }

    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64)
    }
}

impl<K: Eq + Hash, V> HashMap<K, V> {
    /// Create a new (empty) instance.
    pub fn new() -> Self {
        Self(InnerHashMap::<K, V>::with_hasher(FastHasherBuilder))
    }

    /// Create a new (empty) instance with the given capacity.
    pub fn with_capacity(cap: usize) -> Self {
        Self(InnerHashMap::<K, V>::with_capacity_and_hasher(
            cap,
            FastHasherBuilder,
        ))
    }
}

impl<K: Eq + Hash> HashSet<K> {
    /// Create a new (empty) instance.
    pub fn new() -> Self {
        Self(InnerHashSet::<K>::with_hasher(FastHasherBuilder))
    }

    /// Create a new (empty) instance with the given capacity.
    pub fn with_capacity(cap: usize) -> Self {
        Self(InnerHashSet::<K>::with_capacity_and_hasher(
            cap,
            FastHasherBuilder,
        ))
    }
}

impl<K: Eq + Hash, V> Default for HashMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Eq + Hash, V> Deref for HashMap<K, V> {
    type Target = InnerHashMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K: Eq + Hash, V> DerefMut for HashMap<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K: Eq + Hash> Default for HashSet<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Eq + Hash> Deref for HashSet<K> {
    type Target = InnerHashSet<K>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K: Eq + Hash> DerefMut for HashSet<K> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K: Eq + Hash> FromIterator<K> for HashSet<K> {
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        Self(InnerHashSet::<K>::from_iter(iter))
    }
}

impl<'a, K: Eq + Hash, V> IntoIterator for &'a HashMap<K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = <&'a InnerHashMap<K, V> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, K: Eq + Hash> IntoIterator for &'a HashSet<K> {
    type Item = &'a K;

    type IntoIter = <&'a InnerHashSet<K> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<K: Eq + Hash, V> IntoIterator for HashMap<K, V> {
    type Item = (K, V);

    type IntoIter = <InnerHashMap<K, V> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<K: Eq + Hash> IntoIterator for HashSet<K> {
    type Item = K;

    type IntoIter = <InnerHashSet<K> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{BuildHasher, Hasher};

    use super::FastHasherBuilder;

    #[test]
    fn same_values_hash_equal() {
        let mut hasher0 = FastHasherBuilder.build_hasher();
        hasher0.write_u64(32);
        hasher0.write_u32(42);
        hasher0.write_u16(52);
        hasher0.write_u8(64);
        let mut hasher1 = FastHasherBuilder.build_hasher();
        hasher1.write_u64(32);
        hasher1.write_u32(42);
        hasher1.write_u16(52);
        hasher1.write_u8(64);
        assert_eq!(hasher0.finish(), hasher1.finish());
    }

    #[test]
    fn different_values_likely_hash_different() {
        let mut hasher0 = FastHasherBuilder.build_hasher();
        hasher0.write_u64(32);
        hasher0.write_u32(42);
        hasher0.write_u16(52);
        hasher0.write_u8(64);
        let mut hasher1 = FastHasherBuilder.build_hasher();
        hasher1.write_u64(32);
        hasher1.write_u32(43);
        hasher1.write_u16(52);
        hasher1.write_u8(64);
        assert_ne!(hasher0.finish(), hasher1.finish());
    }

    #[test]
    fn hasher_can_be_finalized_again() {
        let mut hasher = FastHasherBuilder.build_hasher();
        hasher.write_u64(32);
        hasher.write_u32(42);
        hasher.write_u16(52);
        hasher.write_u8(64);
        assert_eq!(hasher.finish(), hasher.finish());
        hasher.write_u8(64);
        assert_eq!(hasher.finish(), hasher.finish());
    }
}
