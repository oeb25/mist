use mist_syntax::{
    ast::{self, HasAttrs, HasName},
    AstNode,
};

use crate::{
    file::SourceFile,
    hir::{self, Param},
};

use super::{Def, DefKind, Function, Name, Struct, StructField, TypeInvariant};

impl Def {
    pub fn file(&self, db: &dyn crate::Db) -> SourceFile {
        match self.kind(db) {
            DefKind::Function(it) => it.id(db).file,
            DefKind::Struct(it) => it.id(db).file,
            DefKind::StructField(it) => it.id(db).file,
            DefKind::TypeInvariant(it) => it.id(db).file,
        }
    }
    pub fn syntax(&self, db: &dyn crate::Db) -> mist_syntax::SyntaxNode {
        match self.kind(db) {
            DefKind::Function(it) => it.ast_node(db).syntax().clone(),
            DefKind::Struct(it) => it.ast_node(db).syntax().clone(),
            DefKind::StructField(it) => it.ast_node(db).syntax().clone(),
            DefKind::TypeInvariant(it) => it.ast_node(db).syntax().clone(),
        }
    }
    pub fn display(&self, db: &dyn crate::Db) -> String {
        match self.kind(db) {
            DefKind::Function(it) => format!(
                "fn {}",
                it.ast_node(db)
                    .name()
                    .and_then(|s| Some(s.ident_token()?.text().to_string()))
                    .unwrap_or_else(|| "?missing".to_string())
            ),
            DefKind::Struct(it) => format!(
                "struct {}",
                it.ast_node(db)
                    .name()
                    .and_then(|s| Some(s.ident_token()?.text().to_string()))
                    .unwrap_or_else(|| "?missing".to_string())
            ),
            DefKind::StructField(it) => format!(
                "field {}.{}",
                it.parent_struct(db)
                    .ast_node(db)
                    .name()
                    .and_then(|s| Some(s.ident_token()?.text().to_string()))
                    .unwrap_or_else(|| "?missing".to_string()),
                it.ast_node(db)
                    .name()
                    .and_then(|s| Some(s.ident_token()?.text().to_string()))
                    .unwrap_or_else(|| "?missing".to_string())
            ),
            DefKind::TypeInvariant(it) => format!(
                "invariant {}",
                it.ast_node(db)
                    .ty()
                    .map(|ty| ty.syntax().text().to_string())
                    .unwrap_or_else(|| "?missing".to_string())
            ),
        }
    }

    pub fn hir(&self, db: &dyn crate::Db) -> Option<hir::DefinitionHir> {
        hir::lower_def(db, *self)
    }
}

impl Function {
    pub fn ast_node(&self, db: &dyn crate::Db) -> ast::Fn {
        self.id(db).to_node(db)
    }
    pub fn attrs(&self, db: &dyn crate::Db) -> ast::AttrFlags {
        self.id(db).to_node(db).attr_flags()
    }
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self.ast_node(db).name() {
            Some(n) => n.into(),
            None => Name::new("<?missing>"),
        }
    }
    pub fn param_list(
        &self,
        db: &dyn crate::Db,
    ) -> impl Iterator<Item = Param<ast::Name, Option<ast::Type>>> + '_ {
        self.ast_node(db).param_list().into_iter().flat_map(|param_list| {
            param_list.params().map(|param| -> Param<ast::Name, Option<ast::Type>> {
                Param {
                    is_ghost: param.is_ghost(),
                    name: param.name().expect("param did not have a name"),
                    ty: param.ty(),
                }
            })
        })
    }
}

impl Struct {
    pub fn ast_node(&self, db: &dyn crate::Db) -> ast::Struct {
        self.id(db).to_node(db)
    }
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.ast_node(db).name().unwrap().into()
    }
    pub fn fields<'db>(&self, db: &'db dyn crate::Db) -> impl Iterator<Item = StructField> + 'db {
        let s = *self;
        let file = self.id(db).file;
        let ast_map = file.ast_map(db);
        self.ast_node(db)
            .struct_fields()
            .map(move |f| StructField::new(db, ast_map.ast_id(file, &f), s))
    }
}

impl StructField {
    pub fn ast_node(&self, db: &dyn crate::Db) -> ast::StructField {
        self.id(db).to_node(db)
    }
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.ast_node(db).name().unwrap().into()
    }
    pub fn is_ghost(&self, db: &dyn crate::Db) -> bool {
        self.ast_node(db).attr_flags().is_ghost()
    }
}

impl TypeInvariant {
    pub fn ast_node(&self, db: &dyn crate::Db) -> ast::TypeInvariant {
        self.id(db).to_node(db)
    }
    pub fn ty(&self, db: &dyn crate::Db) -> Option<ast::Type> {
        self.id(db).to_node(db).ty()
    }
}
