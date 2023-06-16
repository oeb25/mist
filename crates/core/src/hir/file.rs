use std::marker::PhantomData;

use mist_syntax::{
    ast,
    ptr::{AstPtr, SyntaxNodePtr},
    AstNode, Parse,
};

use crate::{
    def::Def,
    util::{impl_idx, IdxArena},
};

use super::SourceFile;

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct AstIdMap {
    arena: IdxArena<SyntaxNodePtrId>,
}

impl_idx!(SyntaxNodePtrId, SyntaxNodePtr, default_debug);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InFile<T> {
    pub file: SourceFile,
    pub value: T,
}

#[salsa::tracked]
pub fn parse_file(db: &dyn crate::Db, file: SourceFile) -> Parse<ast::SourceFile> {
    mist_syntax::parse(file.text(db))
}

#[salsa::tracked]
pub fn ast_map(db: &dyn crate::Db, file: SourceFile) -> AstIdMap {
    AstIdMap::from_source(file.root(db))
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct FileAstId<N> {
    raw: SyntaxNodePtrId,
    _marker: PhantomData<fn() -> N>,
}

impl<N> Clone for FileAstId<N> {
    fn clone(&self) -> Self {
        Self { raw: self.raw, _marker: PhantomData }
    }
}
impl<N> Copy for FileAstId<N> {}

pub type AstId<N> = InFile<FileAstId<N>>;

impl SourceFile {
    pub fn root(&self, db: &dyn crate::Db) -> ast::SourceFile {
        parse_file(db, *self).tree()
    }
    pub fn ast_map(&self, db: &dyn crate::Db) -> AstIdMap {
        ast_map(db, *self)
    }
    pub fn definitions(&self, db: &dyn crate::Db) -> Vec<Def> {
        super::file_definitions(db, *self)
    }
}

impl AstIdMap {
    fn alloc(&mut self, ptr: SyntaxNodePtr) -> SyntaxNodePtrId {
        self.arena.alloc(ptr)
    }
    pub fn ast_id<N: AstNode>(&self, file: SourceFile, node: &N) -> AstId<N> {
        let ptr = SyntaxNodePtr::new(node.syntax());
        let raw = self.arena.iter().find_map(|(idx, p)| (p == &ptr).then_some(idx)).unwrap();

        let value = FileAstId { raw, _marker: PhantomData };

        InFile { file, value }
    }
    pub fn get<N: AstNode>(&self, id: FileAstId<N>) -> AstPtr<N> {
        AstPtr::try_from_raw(self.arena[id.raw].clone()).unwrap()
    }

    fn from_source(source: ast::SourceFile) -> AstIdMap {
        let mut field_queue = vec![];
        let mut res = AstIdMap::default();
        for item in source.items() {
            res.alloc(SyntaxNodePtr::new(item.syntax()));
            match item {
                ast::Item::Struct(s) => field_queue.extend(s.struct_fields()),
                ast::Item::Const(_)
                | ast::Item::Fn(_)
                | ast::Item::TypeInvariant(_)
                | ast::Item::Macro(_) => {}
            }
        }
        for field in field_queue {
            res.alloc(SyntaxNodePtr::new(field.syntax()));
        }
        res
    }
}

impl<N: AstNode> AstId<N> {
    pub fn to_node(&self, db: &dyn crate::Db) -> N {
        let root = self.file.root(db);
        self.file.ast_map(db).get(self.value).to_node(root.syntax())
    }
}
