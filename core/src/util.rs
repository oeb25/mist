use std::fmt;

use la_arena::{ArenaMap, Idx};

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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArenaSet<IDX>(ArenaMap<IDX, ()>);

impl<V> Default for ArenaSet<Idx<V>> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<V> fmt::Debug for ArenaSet<Idx<V>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set()
            .entries(self.0.iter().map(|(k, ())| k))
            .finish()
    }
}

impl<V> ArenaSet<Idx<V>> {
    pub fn insert(&mut self, idx: Idx<V>) -> bool {
        self.0.insert(idx, ()).is_some()
    }
    pub fn remove(&mut self, idx: Idx<V>) -> bool {
        self.0.remove(idx).is_some()
    }
    pub fn contains_idx(&self, idx: Idx<V>) -> bool {
        self.0.contains_idx(idx)
    }
    pub fn iter(&self) -> impl Iterator<Item = Idx<V>> + '_ {
        self.0.iter().map(|(idx, _)| idx)
    }
}
