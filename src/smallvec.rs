//! A small vector that holds a small number of element directly. There are a
//! number of places in the optimizers where vectors are expected to have mostly
//! only one or two elements, but where theoretically it could be unbounded.
//! This type tries to optimize for that.

use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    mem::{self, ManuallyDrop, MaybeUninit},
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr, usize,
};

/// Internal data of the small vector. Represents either a small array or a standard
/// heap-allocated vector. This is not an enum to use the size as the discriminant.
union SmallVecData<T, const N: usize> {
    vec: ManuallyDrop<Vec<T>>,
    arr: ManuallyDrop<[MaybeUninit<T>; N]>,
}

/// A small vector that can hold some elements directly.
pub struct SmallVec<T, const N: usize> {
    size: u8,
    data: SmallVecData<T, N>,
}

/// An owning iterator for the small vector.
pub enum SmallVecIntoIter<T, const N: usize> {
    Small([MaybeUninit<T>; N], u8, u8),
    Large(<Vec<T> as IntoIterator>::IntoIter),
}

impl<T, const N: usize> SmallVec<T, N> {
    /// Create a new (empty) small vector without allocating.
    pub fn new() -> Self {
        assert!(N <= 128, "`N` must be at most 128");
        Self {
            size: 0,
            data: SmallVecData {
                // SAFETY: The array elements are still uninitialized.
                arr: unsafe { MaybeUninit::uninit().assume_init() },
            },
        }
    }

    /// Use the given vector to build an instance of `SmallVec`.
    pub fn from_vec(vec: Vec<T>) -> Self {
        assert!(N <= 128, "`N` must be at most 128");
        Self {
            size: N as u8 + 1,
            data: SmallVecData {
                vec: ManuallyDrop::new(vec),
            },
        }
    }

    /// Create an (empty) vector. If `size` is bigger that `N`, this will perform
    /// a heap allocation using the standard vector type.
    pub fn with_capacity(size: usize) -> Self {
        if size <= N {
            Self::new()
        } else {
            Self::from_vec(Vec::with_capacity(size))
        }
    }

    /// Create a vector containing only the element `elem`.
    pub fn with(elem: T) -> Self {
        let mut me = Self::with_capacity(1);
        me.push(elem);
        me
    }

    /// Create a vector from an array of elements.
    pub fn with_all<const M: usize>(elems: [T; M]) -> Self {
        let mut me = Self::with_capacity(M);
        for elem in elems {
            me.push(elem);
        }
        me
    }

    /// Promote this vector from the small representation to the large one.
    /// This is not inlined, so it can be marked cold, since we expect the overwhelming
    /// majority of vectors to remain smaller than `N`.
    ///
    /// # Safety
    /// The `arr` pointer must belong to `me` and the size of `me` must be `N`.
    #[cold]
    unsafe fn push_promote(me: &mut Self, elem: T) {
        let mut vs = Vec::with_capacity(N + 1);
        for elem in &mut *me.data.arr {
            // SAFETY: All elements have been initialized.
            vs.push(elem.assume_init_read());
        }
        vs.push(elem);
        // SAFETY: We use write only to prevent the drop of self.
        ptr::from_mut(me).write(SmallVec {
            size: N as u8 + 1,
            data: SmallVecData {
                vec: ManuallyDrop::new(vs),
            },
        });
    }

    /// This is not inlined, so it can be marked cold, since we expect the overwhelming
    /// majority of vectors to remain smaller than `N`.
    #[cold]
    fn push_to_vec(vec: &mut Vec<T>, elem: T) {
        vec.push(elem);
    }

    /// Insert the given element `elem` at the end of the vector.
    pub fn push(&mut self, elem: T) {
        if (self.size as usize) < N {
            // SAFETY: If `size` <= `N` we have a small representation.
            unsafe {
                (*self.data.arr)[self.size as usize].write(elem);
            }
            self.size += 1;
        } else if self.size as usize == N {
            // SAFETY: If `size` <= `N` we have a small representation.
            unsafe {
                Self::push_promote(self, elem);
            }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe {
                Self::push_to_vec(&mut self.data.vec, elem);
            }
        }
    }

    /// Insert all elements yielded by the iterator to the end of the vector.
    pub fn extend(&mut self, iter: impl Iterator<Item = T>) {
        for v in iter {
            self.push(v);
        }
    }

    /// Empty the vector and drop all contained elements. In case this vector
    /// already contains contains some allocation, it may be reused.
    pub fn clear(&mut self) {
        if (self.size as usize) <= N {
            if mem::needs_drop::<T>() {
                // SAFETY: If `size` <= `N` we have a small representation.
                // The first `size` elements are initialized.
                unsafe {
                    for i in 0..self.size as usize {
                        (*self.data.arr)[i].assume_init_drop();
                    }
                }
            }
            self.size = 0;
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe { (*self.data.vec).clear() }
        }
    }

    /// Get a shared reference to the contained slice.
    pub fn as_slice(&self) -> &[T] {
        if (self.size as usize) <= N {
            // SAFETY: If `size` <= `N` we have a small representation.
            // The first `size` elements are initialized.
            unsafe { mem::transmute(&(*self.data.arr)[..self.size as usize]) }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe { &self.data.vec }
        }
    }

    /// Get a mutable reference to the contained slice.
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        if (self.size as usize) <= N {
            // SAFETY: If `size` <= `N` we have a small representation.
            // The first `size` elements are initialized.
            unsafe { mem::transmute(&mut (*self.data.arr)[..self.size as usize]) }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe { &mut self.data.vec }
        }
    }

    /// Remove all elements from this vector for which the predicate return false.
    pub fn retain<F>(&mut self, pred: F)
    where
        F: Fn(&T) -> bool,
    {
        if (self.size as usize) <= N {
            // SAFETY: If `size` <= `N` we have a small representation.
            // The first `size` elements are initialized.
            unsafe {
                let mut j = 0;
                for i in 0..self.size as usize {
                    if pred((*self.data.arr)[i].assume_init_ref()) {
                        if i != j {
                            let val = self.data.arr[i].assume_init_read();
                            (*self.data.arr)[j].write(val);
                        }
                        j += 1;
                    }
                }
                self.size = j as u8;
            }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe { (*self.data.vec).retain(pred) }
        }
    }

    /// Remove all elements from this vector for which the predicate return false.
    pub fn retain_mut<F>(&mut self, pred: F)
    where
        F: Fn(&mut T) -> bool,
    {
        if (self.size as usize) <= N {
            // SAFETY: If `size` <= `N` we have a small representation.
            // The first `size` elements are initialized.
            unsafe {
                let mut j = 0;
                for i in 0..self.size as usize {
                    if pred((*self.data.arr)[i].assume_init_mut()) {
                        if i != j {
                            let val = self.data.arr[i].assume_init_read();
                            (*self.data.arr)[j].write(val);
                        }
                        j += 1;
                    }
                }
                self.size = j as u8;
            }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe { (*self.data.vec).retain_mut(pred) }
        }
    }

    /// Remove all but the first consecutive elements that compare equal.
    pub fn dedup(&mut self)
    where
        T: PartialEq,
    {
        if (self.size as usize) <= N {
            // SAFETY: If `size` <= `N` we have a small representation.
            // The first `size` elements are initialized.
            unsafe {
                let mut j = 1;
                for i in 1..self.size as usize {
                    if self.data.arr[i].assume_init_ref() != self.data.arr[j - 1].assume_init_ref()
                    {
                        if i != j {
                            let val = self.data.arr[i].assume_init_read();
                            (*self.data.arr)[j].write(val);
                        }
                        j += 1;
                    }
                }
                self.size = j as u8;
            }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe { (*self.data.vec).dedup() }
        }
    }
}

impl<T, const N: usize> Drop for SmallVec<T, N> {
    fn drop(&mut self) {
        if (self.size as usize) <= N {
            if mem::needs_drop::<T>() {
                // SAFETY: If `size` <= `N` we have a small representation.
                // The first `size` elements are initialized.
                unsafe {
                    for i in 0..self.size as usize {
                        (*self.data.arr)[i].assume_init_drop();
                    }
                }
            }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe { ManuallyDrop::drop(&mut self.data.vec) }
        }
    }
}

impl<T: Clone, const N: usize> Clone for SmallVec<T, N> {
    fn clone(&self) -> Self {
        let slice = self.as_slice();
        if slice.len() <= N {
            let mut new = Self::new();
            for elem in slice {
                new.push(elem.clone());
            }
            new
        } else {
            Self::from_vec(Vec::from(slice))
        }
    }
}

impl<T: Hash, const N: usize> Hash for SmallVec<T, N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T: PartialEq, const N: usize> PartialEq for SmallVec<T, N> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}

impl<T: Eq, const N: usize> Eq for SmallVec<T, N> {}

impl<T: Ord, const N: usize> PartialOrd for SmallVec<T, N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T: Ord, const N: usize> Ord for SmallVec<T, N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T, const N: usize> Deref for SmallVec<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const N: usize> DerefMut for SmallVec<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}

impl<T, const N: usize> Iterator for SmallVecIntoIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            SmallVecIntoIter::Small(arr, i, size) => {
                if i < size {
                    // SAFETY: The first `size` values are initialized.
                    let result = Some(unsafe { arr[*i as usize].assume_init_read() });
                    *i += 1;
                    result
                } else {
                    None
                }
            }
            SmallVecIntoIter::Large(vs) => vs.next(),
        }
    }
}

impl<T, const N: usize> Drop for SmallVecIntoIter<T, N> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            match self {
                SmallVecIntoIter::Small(arr, i, size) => {
                    for j in *i as usize..*size as usize {
                        // SAFETY: The first `size` values are initialized, and the
                        // values from `i` onward have not yet been given out.
                        unsafe { arr[j].assume_init_drop() };
                    }
                }
                SmallVecIntoIter::Large(_) => { /* Will be dropped automatically. */ }
            }
        }
    }
}

impl<T, const N: usize> IntoIterator for SmallVec<T, N> {
    type Item = T;

    type IntoIter = SmallVecIntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        let mut me = ManuallyDrop::new(self);
        if (me.size as usize) <= N {
            // SAFETY: If `size` <= `N` we have a small representation.
            // The first `size` elements are initialized.
            unsafe {
                let arr = ptr::from_mut(&mut *me.data.arr);
                SmallVecIntoIter::Small(arr.read(), 0, me.size)
            }
        } else {
            // SAFETY: If `size` > `N` we have a large representation.
            unsafe {
                let vec = ptr::from_mut(&mut *me.data.vec);
                SmallVecIntoIter::Large(vec.read().into_iter())
            }
        }
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a SmallVec<T, N> {
    type Item = &'a T;

    type IntoIter = <&'a [T] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut SmallVec<T, N> {
    type Item = &'a mut T;

    type IntoIter = <&'a mut [T] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, const N: usize> Index<usize> for SmallVec<T, N> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T, const N: usize> IndexMut<usize> for SmallVec<T, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::SmallVec;

    #[test]
    fn small_vector() {
        let vec: SmallVec<i32, 1> = SmallVec::with(5);
        assert_eq!(vec.as_slice(), &[5]);
    }

    #[test]
    fn large_vector() {
        let mut vec: SmallVec<i32, 1> = SmallVec::with_capacity(10);
        vec.extend([0, 1, 2, 3, 4].into_iter());
        assert_eq!(vec.as_slice(), &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn growing_from_small_to_large() {
        let mut vec: SmallVec<i32, 1> = SmallVec::new();
        for i in 0..10 {
            vec.push(i);
        }
        assert_eq!(vec.as_slice(), &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn clear_small_vector() {
        let mut vec: SmallVec<i32, 1> = SmallVec::with(5);
        vec.clear();
        assert_eq!(vec.as_slice(), &[]);
    }

    #[test]
    fn clear_large_vector() {
        let mut vec: SmallVec<i32, 1> = SmallVec::with_capacity(10);
        vec.extend([0, 1, 2, 3, 4].into_iter());
        vec.clear();
        assert_eq!(vec.as_slice(), &[]);
    }

    #[test]
    fn clone_small_vector() {
        let vec: SmallVec<i32, 1> = SmallVec::with(5);
        assert_eq!(vec.clone().as_slice(), &[5]);
    }

    #[test]
    fn clone_large_vector() {
        let mut vec: SmallVec<i32, 1> = SmallVec::with_capacity(10);
        vec.extend([0, 1, 2, 3, 4].into_iter());
        assert_eq!(vec.clone().as_slice(), &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn clone_small_vector_with_large_capacity() {
        let mut vec: SmallVec<i32, 1> = SmallVec::with_capacity(10);
        vec.push(5);
        assert_eq!(vec.clone().as_slice(), &[5]);
    }

    #[test]
    fn iterate_small_vector() {
        let vec: SmallVec<i32, 1> = SmallVec::with(5);
        let mut es = Vec::new();
        for e in vec {
            es.push(e);
        }
        assert_eq!(&es, &[5]);
    }

    #[test]
    fn iterate_large_vector() {
        let mut vec: SmallVec<i32, 1> = SmallVec::with_capacity(10);
        vec.extend([0, 1, 2, 3, 4].into_iter());
        let mut es = Vec::new();
        for e in vec {
            es.push(e);
        }
        assert_eq!(&es, &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn fake_smallvec() {
        let mut vec: SmallVec<i32, 0> = SmallVec::new();
        for i in 0..10 {
            vec.push(i);
        }
        assert_eq!(vec.as_slice(), &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn large_smallvec() {
        let mut vec: SmallVec<i32, 32> = SmallVec::new();
        for i in 0..10 {
            vec.push(i);
        }
        assert_eq!(vec.as_slice(), &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }
}
