use std::fmt;

use la_arena::{Arena, ArenaMap, Idx};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

impl Position {
    pub fn new(line: u32, character: u32) -> Self {
        Self { line, character }
    }
    pub fn to_byte_offset(self, src: &str) -> Option<usize> {
        let mut lines = self.line;
        let mut columns = self.character;
        src.char_indices()
            .find(|&(_, c)| {
                if lines == 0 {
                    if columns == 0 {
                        return true;
                    } else {
                        columns -= 1
                    }
                } else if c == '\n' {
                    lines -= 1;
                }
                false
            })
            .map(|(idx, _)| idx)
    }
    pub fn from_byte_offset(src: &str, byte_offset: usize) -> Self {
        if src.get(0..byte_offset).is_none() {
            // TODO: Should the this perhaps return the final position instead
            // of first?
            return Position::new(0, 0);
        }
        if src[0..byte_offset].is_empty() {
            return Position::new(0, 0);
        }

        if src[0..byte_offset].ends_with('\n') {
            let l = src[0..byte_offset].lines().count();
            Position::new(l as _, 0)
        } else {
            let l = src[0..byte_offset].lines().count() - 1;
            let c = src[0..byte_offset].lines().last().unwrap().len();
            Position::new(l as _, c as _)
        }
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.character)
    }
}

pub trait IdxWrap: Clone + Copy + fmt::Debug {
    type Inner: fmt::Debug + Clone + PartialEq + Eq + std::hash::Hash;
    fn into_idx(self) -> Idx<Self::Inner>;
    fn from_idx(idx: Idx<Self::Inner>) -> Self;
    fn into_raw(self) -> la_arena::RawIdx {
        self.into_idx().into_raw()
    }
    fn from_raw(raw: la_arena::RawIdx) -> Self {
        Self::from_idx(Idx::from_raw(raw))
    }
}

#[macro_export]
macro_rules! impl_idx_ {
    ($name:ident, $inner:ty) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(::la_arena::Idx<$inner>);
        impl $crate::util::IdxWrap for $name {
            type Inner = $inner;

            fn into_idx(self) -> ::la_arena::Idx<Self::Inner> {
                self.0
            }

            fn from_idx(idx: ::la_arena::Idx<Self::Inner>) -> Self {
                Self(idx)
            }
        }
    };
    ($name:ident, $inner:ty, default_debug) => {
        $crate::util::impl_idx!($name, $inner);
        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                f.debug_tuple(stringify!($inner))
                    .field(&self.0.into_raw())
                    .finish()
            }
        }
    };
}
pub use impl_idx_ as impl_idx;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct IdxArena<IDX: IdxWrap>(Arena<IDX::Inner>);

impl<IDX: IdxWrap> Default for IdxArena<IDX> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<IDX: IdxWrap> fmt::Debug for IdxArena<IDX>
where
    IDX::Inner: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<IDX: IdxWrap> IdxArena<IDX> {
    pub fn alloc(&mut self, v: IDX::Inner) -> IDX {
        IDX::from_idx(self.0.alloc(v))
    }
    pub fn iter(&self) -> impl Iterator<Item = (IDX, &IDX::Inner)> {
        self.0.iter().map(|(idx, v)| (IDX::from_idx(idx), v))
    }
}

impl<IDX: IdxWrap> std::ops::Index<IDX> for IdxArena<IDX> {
    type Output = IDX::Inner;

    fn index(&self, index: IDX) -> &Self::Output {
        &self.0[index.into_idx()]
    }
}
impl<IDX: IdxWrap> std::ops::IndexMut<IDX> for IdxArena<IDX> {
    fn index_mut(&mut self, index: IDX) -> &mut Self::Output {
        &mut self.0[index.into_idx()]
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct IdxMap<IDX: IdxWrap, V>(ArenaMap<Idx<IDX::Inner>, V>);

impl<IDX: IdxWrap, V> Default for IdxMap<IDX, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<IDX: IdxWrap, V: fmt::Debug> fmt::Debug for IdxMap<IDX, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<IDX: IdxWrap, V> IdxMap<IDX, V> {
    pub fn new() -> Self {
        Default::default()
    }
    pub fn with_capacity(capacity: usize) -> Self {
        IdxMap(ArenaMap::with_capacity(capacity))
    }
    pub fn get(&self, idx: IDX) -> Option<&V> {
        self.0.get(idx.into_idx())
    }
    pub fn get_mut(&mut self, idx: IDX) -> Option<&mut V> {
        self.0.get_mut(idx.into_idx())
    }
    pub fn insert(&mut self, idx: IDX, value: V) -> Option<V> {
        self.0.insert(idx.into_idx(), value)
    }
    pub fn remove(&mut self, idx: IDX) -> Option<V> {
        self.0.remove(idx.into_idx())
    }
    pub fn contains_idx(&self, idx: IDX) -> bool {
        self.0.contains_idx(idx.into_idx())
    }
    pub fn iter(&self) -> impl Iterator<Item = (IDX, &V)> {
        self.0.iter().map(|(idx, v)| (IDX::from_idx(idx), v))
    }
    pub fn entry(&mut self, idx: IDX) -> la_arena::Entry<Idx<IDX::Inner>, V> {
        self.0.entry(idx.into_idx())
    }
}

impl<IDX: IdxWrap, V> std::ops::Index<IDX> for IdxMap<IDX, V> {
    type Output = V;

    fn index(&self, index: IDX) -> &Self::Output {
        &self.0[index.into_idx()]
    }
}
impl<IDX: IdxWrap, V> std::ops::IndexMut<IDX> for IdxMap<IDX, V> {
    fn index_mut(&mut self, index: IDX) -> &mut Self::Output {
        &mut self.0[index.into_idx()]
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct IdxSet<IDX: IdxWrap>(IdxMap<IDX, ()>);

impl<V: IdxWrap> Default for IdxSet<V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<V: IdxWrap + fmt::Debug> fmt::Debug for IdxSet<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set()
            .entries(self.0.iter().map(|(k, ())| k))
            .finish()
    }
}

impl<V: IdxWrap> IdxSet<V> {
    pub fn insert(&mut self, idx: V) -> bool {
        self.0.insert(idx, ()).is_some()
    }
    pub fn remove(&mut self, idx: V) -> bool {
        self.0.remove(idx).is_some()
    }
    pub fn contains_idx(&self, idx: V) -> bool {
        self.0.contains_idx(idx)
    }
    pub fn iter(&self) -> impl Iterator<Item = V> + '_ {
        self.0.iter().map(|(idx, _)| idx)
    }
}
