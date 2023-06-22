use std::fmt;

use crate::{
    mono::{
        exprs::{Field, VariablePtr},
        types::Type,
    },
    util::impl_idx,
};

impl_idx!(SlotId, Slot);
impl fmt::Debug for SlotId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0.into_raw())
    }
}
impl fmt::Display for SlotId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0.into_raw())
    }
}
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub enum Slot {
    #[default]
    Temp,
    Self_,
    Param(VariablePtr),
    Local(VariablePtr),
    Quantified(VariablePtr),
    Result,
}
impl Slot {
    #[must_use]
    pub fn is_result(&self) -> bool {
        matches!(self, Self::Result)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Place {
    slot: SlotId,
    projection: Option<ProjectionList>,
}
impl Place {
    pub fn new(slot: SlotId, projection: Option<ProjectionList>) -> Place {
        Place { slot, projection }
    }

    pub fn slot(self) -> SlotId {
        self.slot
    }

    pub fn has_projection(self, db: &dyn crate::Db) -> bool {
        !self.projection(db).is_empty(db)
    }

    pub fn projection(self, db: &dyn crate::Db) -> ProjectionList {
        self.projection.unwrap_or_else(|| ProjectionList::new(db, Vec::new()))
    }

    pub fn projections(self, db: &dyn crate::Db) -> &[Projection] {
        self.projection(db).elements(db)
    }

    pub fn without_projection(&self, db: &dyn crate::Db) -> Place {
        self.replace_projection(Projection::empty(db))
    }

    pub fn replace_projection(&self, projection: ProjectionList) -> Place {
        Place::new(self.slot, Some(projection))
    }

    pub fn parent(&self, db: &dyn crate::Db) -> Option<Place> {
        Some(self.replace_projection(self.projection(db).parent(db)?))
    }

    pub fn project_deeper(self, db: &dyn crate::Db, projection: &[Projection]) -> Place {
        let mut new_projection = self.projection(db).elements(db).to_vec();
        new_projection.extend_from_slice(projection);
        self.replace_projection(ProjectionList::new(db, new_projection))
    }

    pub fn projection_iter(self, db: &dyn crate::Db) -> impl Iterator<Item = Projection> + '_ {
        self.projection(db).iter(db)
    }

    pub fn projection_path_iter(
        self,
        db: &dyn crate::Db,
    ) -> impl Iterator<Item = ProjectionList> + '_ {
        self.projection(db).path_iter(db)
    }

    pub(super) fn nested_places(self, db: &dyn crate::Db) -> impl Iterator<Item = Place> + '_ {
        self.projection_iter(db).filter_map(|pj| match pj {
            Projection::Field(_, _) => None,
            Projection::Index(s, _) => Some(s.into()),
        })
    }
}

impl From<SlotId> for Place {
    fn from(slot: SlotId) -> Place {
        Place { slot, projection: None }
    }
}

#[salsa::interned]
pub struct ProjectionList {
    #[return_ref]
    pub elements: Vec<Projection>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Projection {
    Field(Field, Type),
    Index(SlotId, Type),
}
impl Projection {
    /// Construct an empty [`ProjectionList`]
    pub fn empty(db: &dyn crate::Db) -> ProjectionList {
        ProjectionList::new(db, Vec::new())
    }
}
impl ProjectionList {
    pub fn is_empty(self, db: &dyn crate::Db) -> bool {
        self.elements(db).is_empty()
    }
    pub fn len(self, db: &dyn crate::Db) -> usize {
        self.elements(db).len()
    }
    pub fn last(self, db: &dyn crate::Db) -> Option<Projection> {
        self.elements(db).last().copied()
    }
    pub fn iter(self, db: &dyn crate::Db) -> impl Iterator<Item = Projection> + '_ {
        self.elements(db).iter().copied()
    }
    pub fn parent(self, db: &dyn crate::Db) -> Option<ProjectionList> {
        let list = self.elements(db);
        let search_for = if list.is_empty() {
            return None;
        } else {
            &list[0..list.len() - 1]
        };
        Some(ProjectionList::new(db, search_for.to_vec()))
    }
    /// Returns a iterator over all [`ProjectionList`]'s leading to this projection.
    ///
    /// For `a.b.c` the iterator will produce `[a, a.b, a.b.c]` in that order.
    pub fn path_iter(self, db: &dyn crate::Db) -> impl Iterator<Item = ProjectionList> + '_ {
        let mut entries = vec![self];
        let mut current = self;

        loop {
            match current.parent(db) {
                Some(next) => {
                    entries.push(next);
                    current = next;
                }
                None => {
                    return entries.into_iter().rev();
                }
            }
        }
    }
}
