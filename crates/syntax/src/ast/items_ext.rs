use itertools::Itertools;

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct AttrFlags: u8 {
        const PURE = 0b01;
        const GHOST = 0b10;
    }
}

impl Default for AttrFlags {
    fn default() -> Self {
        Self::empty()
    }
}

impl AttrFlags {
    pub fn is_ghost(self) -> bool {
        self.contains(Self::GHOST)
    }
    pub fn is_pure(self) -> bool {
        self.contains(Self::PURE)
    }
}

impl std::fmt::Display for AttrFlags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        [self.contains(Self::PURE).then_some("pure"), self.contains(Self::GHOST).then_some("ghost")]
            .into_iter()
            .flatten()
            .format(" ")
            .fmt(f)
    }
}
