use super::ItemBody;

mod isorecursive;
mod mention;

pub use isorecursive::IsorecursivePass;
pub use mention::MentionPass;

pub trait Pass {
    fn run(db: &dyn crate::Db, ib: &mut ItemBody);
}

pub struct FullDefaultPass;

impl Pass for FullDefaultPass {
    fn run(db: &dyn crate::Db, ib: &mut ItemBody) {
        MentionPass::run(db, ib);
        IsorecursivePass::run(db, ib);
    }
}
