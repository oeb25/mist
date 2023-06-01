use super::Body;

mod isorecursive;
mod mention;

pub use isorecursive::IsorecursivePass;
pub use mention::MentionPass;

pub trait Pass {
    fn run(db: &dyn crate::Db, body: &mut Body);
}

pub struct FullDefaultPass;

impl Pass for FullDefaultPass {
    fn run(db: &dyn crate::Db, body: &mut Body) {
        MentionPass::run(db, body);
        IsorecursivePass::run(db, body);
    }
}
