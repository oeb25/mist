mod name;

use derive_more::{Display, From};
use derive_new::new;
use mist_syntax::{
    ast::{
        self,
        operators::{BinaryOp, UnaryOp},
        AttrFlags, HasAttrs, HasName, Spanned,
    },
    ptr::AstPtr,
    AstNode, SourceSpan,
};
use tracing::error;

use crate::util::impl_idx;

pub use super::typecheck::TypeId;
use super::ItemContext;

pub use name::Name;

#[salsa::interned]
pub struct ItemId {
    pub data: ItemData,
}

impl ItemId {
    pub fn syntax(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> mist_syntax::SyntaxNode {
        self.data(db).syntax(root)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, From)]
pub enum ItemData {
    Const { ast: AstPtr<ast::Const> },
    Fn { ast: AstPtr<ast::Fn> },
    Struct { ast: AstPtr<ast::Struct> },
    TypeInvariant { ast: AstPtr<ast::TypeInvariant> },
    Macro { ast: AstPtr<ast::Macro> },
}
impl ItemData {
    fn syntax(&self, root: &ast::SourceFile) -> mist_syntax::SyntaxNode {
        match self {
            ItemData::Const { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::Fn { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::Struct { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::TypeInvariant { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::Macro { ast } => ast.to_node(root.syntax()).syntax().clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum Item {
    Type(TypeDecl),
    TypeInvariant(TypeInvariant),
    Function(Function),
}

impl Item {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self {
            Item::Type(t) => t.name(db),
            Item::TypeInvariant(t) => t.name(db),
            Item::Function(f) => f.name(db),
        }
    }
}

#[salsa::tracked]
pub struct TypeDecl {
    pub name: Name,
    pub data: TypeDeclData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeDeclData {
    Struct(Struct),
}

#[salsa::interned]
pub struct Function {
    #[return_ref]
    syntax: AstPtr<ast::Fn>,
    pub name: Name,
    pub attrs: AttrFlags,
}

impl Function {
    pub fn ast_node(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> ast::Fn {
        self.syntax(db).to_node(root.syntax())
    }
    pub fn param_list(
        &self,
        db: &dyn crate::Db,
        root: &ast::SourceFile,
    ) -> impl Iterator<Item = Param<ast::Name, Option<ast::Type>>> + '_ {
        self.syntax(db)
            .to_node(root.syntax())
            .param_list()
            .into_iter()
            .flat_map(|param_list| {
                param_list
                    .params()
                    .map(|param| -> Param<ast::Name, Option<ast::Type>> {
                        Param {
                            is_ghost: param.is_ghost(),
                            name: param.name().expect("param did not have a name"),
                            ty: param.ty(),
                        }
                    })
            })
    }
}

#[salsa::interned]
pub struct VariableId {
    #[return_ref]
    pub text: Name,
}

#[salsa::tracked]
pub struct Variable {
    #[id]
    pub name: VariableId,
}
impl_idx!(VariableIdx, Variable, default_debug);
#[derive(new, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VariableRef {
    idx: VariableIdx,
    span: SourceSpan,
}

impl VariableRef {
    pub fn idx(&self) -> VariableIdx {
        self.idx
    }
}
impl Spanned for VariableRef {
    fn span(self) -> SourceSpan {
        self.span
    }
}
impl Spanned for &'_ VariableRef {
    fn span(self) -> SourceSpan {
        self.span
    }
}
impl From<VariableRef> for VariableIdx {
    fn from(value: VariableRef) -> Self {
        value.idx
    }
}
impl From<&'_ VariableRef> for VariableIdx {
    fn from(value: &VariableRef) -> Self {
        value.idx
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param<I, T = TypeSrcId> {
    pub is_ghost: bool,
    pub name: I,
    pub ty: T,
}

impl<I, T> Param<I, T> {
    pub fn map_var<J>(&self, f: impl FnOnce(&I) -> J) -> Param<J, T>
    where
        T: Clone,
    {
        Param {
            is_ghost: self.is_ghost,
            name: f(&self.name),
            ty: self.ty.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Condition {
    Requires(Vec<ExprIdx>),
    Ensures(Vec<ExprIdx>),
}

impl Condition {
    pub fn exprs(&self) -> &[ExprIdx] {
        match self {
            Self::Requires(it) | Self::Ensures(it) => it,
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Decreases {
    #[default]
    Unspecified,
    Expr(ExprIdx),
    Inferred,
}

impl_idx!(ExprIdx, Expr, default_debug);
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    pub ty: TypeId,
    pub data: ExprData,
}
impl Expr {
    pub(super) fn new_block(block: Block) -> Expr {
        Expr {
            ty: block.return_ty,
            data: ExprData::Block(block),
        }
    }
    pub(super) fn new_if(if_expr: IfExpr) -> Expr {
        Expr {
            ty: if_expr.return_ty,
            data: ExprData::If(if_expr),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    Literal(Literal),
    Self_,
    Ident(VariableRef),
    Block(Block),
    Field {
        expr: ExprIdx,
        field_name: Name,
        field: Option<Field>,
    },
    Struct {
        struct_declaration: Struct,
        struct_span: SourceSpan,
        fields: Vec<StructExprField>,
    },
    Missing,
    If(IfExpr),
    Call {
        expr: ExprIdx,
        args: Vec<ExprIdx>,
    },
    Unary {
        op: UnaryOp,
        inner: ExprIdx,
    },
    Bin {
        lhs: ExprIdx,
        op: BinaryOp,
        rhs: ExprIdx,
    },
    Ref {
        is_mut: bool,
        expr: ExprIdx,
    },
    Index {
        base: ExprIdx,
        index: ExprIdx,
    },
    List {
        elems: Vec<ExprIdx>,
    },
    Quantifier {
        quantifier: Quantifier,
        params: Vec<Param<VariableIdx>>,
        expr: ExprIdx,
    },
    Result,
    Range {
        lhs: Option<ExprIdx>,
        rhs: Option<ExprIdx>,
    },
    Return(Option<ExprIdx>),
    NotNull(ExprIdx),
}
impl ExprData {
    pub(super) fn typed(self, ty: TypeId) -> Expr {
        Expr { ty, data: self }
    }
}
#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    #[display(fmt = "null")]
    Null,
    #[display(fmt = "{_0}")]
    Int(i64),
    #[display(fmt = "{_0}")]
    Bool(bool),
}

impl Literal {
    pub fn as_bool(&self) -> Option<&bool> {
        if let Self::Bool(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<&i64> {
        if let Self::Int(v) = self {
            Some(v)
        } else {
            None
        }
    }
}
#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    #[display(fmt = "forall")]
    Forall,
    #[display(fmt = "exists")]
    Exists,
}
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructExprField {
    pub decl: Field,
    pub name: AstPtr<ast::NameRef>,
    pub value: ExprIdx,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfExpr {
    pub if_span: SourceSpan,
    pub is_ghost: bool,
    pub return_ty: TypeId,
    pub condition: ExprIdx,
    pub then_branch: ExprIdx,
    pub else_branch: Option<ExprIdx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub tail_expr: Option<ExprIdx>,
    pub return_ty: TypeId,
}

#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Statement {
    pub span: SourceSpan,
    pub data: StatementData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StatementData {
    Expr(ExprIdx),
    Let {
        variable: VariableRef,
        explicit_ty: Option<TypeSrcId>,
        initializer: ExprIdx,
    },
    While {
        expr: ExprIdx,
        invariants: Vec<Vec<ExprIdx>>,
        decreases: Decreases,
        body: Block,
    },
    Assertion {
        kind: AssertionKind,
        exprs: Vec<ExprIdx>,
    },
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssertionKind {
    #[display(fmt = "assert")]
    Assert,
    #[display(fmt = "assume")]
    Assume,
    #[display(fmt = "inhale")]
    Inhale,
    #[display(fmt = "exhale")]
    Exhale,
}

impl_idx!(TypeSrcId, TypeSrc, default_debug);
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeSrc {
    pub data: Option<TypeData<TypeSrcId>>,
    pub ty: TypeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeData<T = TypeId> {
    Error,
    Void,
    Ghost(T),
    Ref {
        is_mut: bool,
        inner: T,
    },
    List(T),
    Optional(T),
    Primitive(Primitive),
    Struct(Struct),
    Null,
    Function {
        attrs: AttrFlags,
        name: Option<Name>,
        params: Vec<Param<Name>>,
        return_ty: T,
    },
    Range(T),
    Free,
}
impl_idx!(TypeDataIdx, TypeData, default_debug);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Primitive {
    Int,
    Bool,
}

impl ena::unify::UnifyValue for TypeData {
    type Error = ();

    fn unify_values(ty1: &Self, ty2: &Self) -> Result<Self, ()> {
        match (ty1, ty2) {
            (TypeData::Free, other) | (other, TypeData::Free) => Ok(other.clone()),
            _ => {
                error!("could not unify {ty1:?} with {ty2:?}");
                Err(())
            }
        }
    }
}

impl<T> TypeData<T> {
    pub fn map<S>(&self, mut f: impl FnMut(&T) -> S) -> TypeData<S> {
        match self {
            TypeData::Error => TypeData::Error,
            TypeData::Void => TypeData::Void,
            TypeData::Ghost(it) => TypeData::Ghost(f(it)),
            TypeData::Ref { is_mut, inner } => TypeData::Ref {
                is_mut: *is_mut,
                inner: f(inner),
            },
            TypeData::List(it) => TypeData::List(f(it)),
            TypeData::Optional(it) => TypeData::Optional(f(it)),
            TypeData::Primitive(it) => TypeData::Primitive(it.clone()),
            TypeData::Struct(it) => TypeData::Struct(*it),
            TypeData::Null => TypeData::Null,
            TypeData::Function {
                attrs,
                name,
                params,
                return_ty,
            } => TypeData::Function {
                attrs: *attrs,
                name: name.clone(),
                params: params.clone(),
                return_ty: f(return_ty),
            },
            TypeData::Range(it) => TypeData::Range(f(it)),
            TypeData::Free => TypeData::Free,
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self, TypeData::Void)
    }
    pub fn is_ghost(&self) -> bool {
        matches!(self, TypeData::Ghost(_))
    }
    pub fn is_error(&self) -> bool {
        matches!(self, TypeData::Error)
    }
}
impl TypeData<TypeSrcId> {
    pub fn canonical(&self, cx: &ItemContext) -> TypeData {
        self.map(|&id| cx[id].ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructFieldInner {
    // TODO: remove the visibility modifier
    pub(super) node: AstPtr<ast::StructField>,
    pub(super) name: Name,
    pub(super) is_ghost: bool,
}

#[salsa::interned]
pub struct Struct {
    #[return_ref]
    node: AstPtr<ast::Struct>,
    pub name: Name,
    #[return_ref]
    fields_inner: Vec<StructFieldInner>,
}

impl Struct {
    pub fn ast_node(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> ast::Struct {
        self.node(db).to_node(root.syntax())
    }
    pub fn fields<'db>(
        &self,
        db: &'db dyn crate::Db,
    ) -> impl Iterator<Item = StructFieldRef> + 'db {
        let s = *self;
        self.fields_inner(db).iter().map(move |f| StructFieldRef {
            inner: Field::new(
                db,
                Some(f.node.clone()),
                FieldParent::Struct(s),
                f.name.clone(),
                f.is_ghost,
            ),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructFieldRef {
    inner: Field,
}

impl StructFieldRef {
    pub fn field(&self) -> Field {
        self.inner
    }
    pub fn ast_node(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> ast::StructField {
        self.inner
            .ast_node(db, root)
            .expect("this is aways okay, since it's been constructed by the parent")
    }
    pub fn parent(&self, db: &dyn crate::Db) -> FieldParent {
        self.inner.parent(db)
    }
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.inner.name(db)
    }
    pub fn is_ghost(&self, db: &dyn crate::Db) -> bool {
        self.inner.is_ghost(db)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldParent {
    Struct(Struct),
    List(TypeId),
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[salsa::interned]
pub struct Field {
    node: Option<AstPtr<ast::StructField>>,
    pub parent: FieldParent,
    pub name: Name,
    pub is_ghost: bool,
    // ast_ty: Option<AstPtr<ast::Type>>,
}

impl Field {
    pub fn ast_node(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> Option<ast::StructField> {
        self.node(db).map(|node| node.to_node(root.syntax()))
    }
    // pub fn ty(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> Option<ast::Type> {
    //     self.ast_ty(db).as_ref().map(|ty| ty.to_node(root.syntax()))
    // }
}

#[salsa::interned]
pub struct TypeInvariant {
    #[return_ref]
    node: AstPtr<ast::TypeInvariant>,
    pub name: Name,
}

impl TypeInvariant {
    pub fn ast_node(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> ast::TypeInvariant {
        self.node(db).to_node(root.syntax())
    }
}
