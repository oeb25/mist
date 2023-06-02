use std::fmt::Write;

use derive_new::new;
use owo_colors::{colors::*, OwoColorize};

use crate::{
    hir::ItemContext,
    mir::{BlockLocation, Projection, Terminator},
};

use super::{
    BlockId, Body, BodyLocation, BorrowKind, Folding, FunctionData, FunctionId, Instruction,
    InstructionId, MExpr, Operand, Place, Slot, SlotId,
};

#[derive(new)]
struct Serializer<'a> {
    color: Color,
    body: &'a Body,
    #[new(default)]
    output: String,
    #[new(default)]
    start_of_line: bool,
    #[new(default)]
    indentation: usize,
    #[new(default)]
    annotator: Option<Box<dyn Fn(BodyLocation) -> Option<String>>>,
}

impl Body {
    pub fn serialize_with_annotation(
        &self,
        db: &dyn crate::Db,
        cx: Option<&ItemContext>,
        color: Color,
        f: Box<dyn Fn(BodyLocation) -> Option<String>>,
    ) -> String {
        Serializer::new(color, self).with_annotator(f).finish(db, cx)
    }
    pub fn serialize(&self, db: &dyn crate::Db, cx: Option<&ItemContext>, color: Color) -> String {
        Serializer::new(color, self).finish(db, cx)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Color {
    No,
    Yes,
}

impl MExpr {
    pub fn serialize(
        &self,
        color: Color,
        db: &dyn crate::Db,
        cx: Option<&ItemContext>,
        body: &Body,
    ) -> String {
        let mut s = Serializer::new(color, body);
        s.expr(db, cx, self);
        s.output
    }
}
pub fn serialize_terminator(
    color: Color,
    db: Option<&dyn crate::Db>,
    cx: Option<&ItemContext>,
    body: &Body,
    term: &Terminator,
) -> String {
    let mut s = Serializer::new(color, body).with_color(color);
    s.terminator(db, cx, term);
    s.output
}
pub fn serialize_block(
    color: Color,
    db: &dyn crate::Db,
    cx: Option<&ItemContext>,
    body: &Body,
    bid: BlockId,
) -> String {
    let mut s = Serializer::new(color, body).with_color(color);
    s.block(db, cx, bid);
    s.output
}
pub fn serialize_slot(color: Color, cx: Option<&ItemContext>, body: &Body, slot: SlotId) -> String {
    let mut s = Serializer::new(color, body).with_color(color);
    s.slot(cx, slot);
    s.output
}
pub fn serialize_place(
    color: Color,
    db: Option<&dyn crate::Db>,
    cx: Option<&ItemContext>,
    body: &Body,
    place: Place,
) -> String {
    let mut s = Serializer::new(color, body).with_color(color);
    s.place(db, cx, place);
    s.output
}

macro_rules! w {
    ($x:ident, $c:ty, $($t:tt)*) => {{
        if $x.start_of_line {
            for _ in 0..$x.indentation {
                write!($x.output, "  ").unwrap();
            }
        }
        if $x.color == Color::Yes {
            write!($x.output, "{}", format!($($t)*).fg::<$c>()).unwrap();
        } else {
            write!($x.output, $($t)*).unwrap();
        }
        $x.start_of_line = false;
    }};
}
macro_rules! wln {
    ($x:ident, $c:ty, $($t:tt)*) => {{
        if $x.start_of_line {
            for _ in 0..$x.indentation {
                write!($x.output, "  ").unwrap();
            }
        }
        if $x.color == Color::Yes {
            writeln!($x.output, "{}", format!($($t)*).fg::<$c>()).unwrap();
        } else {
            writeln!($x.output, $($t)*).unwrap();
        }
        $x.start_of_line = true;
    }};
}

impl Serializer<'_> {
    fn finish(mut self, db: &dyn crate::Db, cx: Option<&ItemContext>) -> String {
        for bid in self.body.blocks.iter().map(|(id, _)| id).collect::<Vec<_>>() {
            self.block(db, cx, bid);
        }

        self.output
    }

    fn indented(&mut self, f: impl FnOnce(&mut Self)) {
        self.indentation += 1;
        f(self);
        self.indentation -= 1;
    }

    fn block(&mut self, db: &dyn crate::Db, cx: Option<&ItemContext>, body: BlockId) {
        self.block_id(Some(body));
        wln!(self, Default, "");
        self.indented(|this| {
            let mut printed = false;
            for &inst in &this.body.blocks[body].instructions {
                printed = true;
                if let Some(f) = &this.annotator {
                    if let Some(s) = f(BlockLocation::Instruction(inst).in_block(body)) {
                        wln!(this, Default, "{s}");
                    }
                }
                this.inst(db, cx, inst);
            }
            if let Some(term) = &this.body.blocks[body].terminator {
                printed = true;
                if let Some(f) = &this.annotator {
                    if let Some(s) = f(BlockLocation::Terminator.in_block(body)) {
                        wln!(this, Default, "{s}");
                    }
                }
                this.terminator(Some(db), cx, term);
            }
            if !printed {
                if let Some(f) = &this.annotator {
                    if let Some(s) = f(BlockLocation::Terminator.in_block(body)) {
                        wln!(this, Default, "{s}");
                    }
                }
            }
        });
    }

    fn inst(&mut self, db: &dyn crate::Db, cx: Option<&ItemContext>, inst: InstructionId) {
        match &self.body.instructions[inst] {
            Instruction::Assign(s, e) => {
                self.place(Some(db), cx, *s);
                w!(self, Default, " := ");
                self.expr(db, cx, e);
                wln!(self, Default, "");
            }
            Instruction::Assertion(kind, expr) => {
                w!(self, Default, "{kind} ");
                self.expr(db, cx, expr);
                wln!(self, Default, "");
            }
            Instruction::PlaceMention(p) => {
                w!(self, Default, "mention ");
                self.place(Some(db), cx, *p);
                wln!(self, Default, "");
            }
            Instruction::Folding(folding) => {
                self.folding(Some(db), cx, *folding);
            }
        }
    }

    fn slot(&mut self, cx: Option<&ItemContext>, s: SlotId) {
        match (&self.body.slots[s], cx) {
            (Slot::Param(v), Some(cx)) => w!(self, Cyan, "{s}_{}", cx.var_name(*v)),
            (Slot::Quantified(v), Some(cx)) => w!(self, Cyan, "{s}_{}", cx.var_name(*v)),
            (Slot::Local(v), Some(cx)) => w!(self, Cyan, "{s}_{}", cx.var_name(*v)),
            (Slot::Result, _) => w!(self, Magenta, "%result"),
            (Slot::Self_, _) => w!(self, Magenta, "%self"),
            _ => w!(self, Cyan, "{s}"),
        }
    }

    fn place(&mut self, db: Option<&dyn crate::Db>, cx: Option<&ItemContext>, s: Place) {
        if self.body[s.projection].is_empty() {
            self.slot(cx, s.slot);
        } else {
            self.slot(cx, s.slot);
            for p in &self.body[s.projection] {
                match p {
                    Projection::Field(f, _) => {
                        if let Some(db) = db {
                            let name = &f.name(db);
                            w!(self, Default, ".{name}");
                        } else {
                            w!(self, Default, ".?");
                        }
                    }
                    Projection::Index(idx, _) => {
                        w!(self, Default, "[");
                        self.slot(cx, *idx);
                        w!(self, Default, "]");
                    }
                }
            }
        }
    }

    fn operand(&mut self, db: Option<&dyn crate::Db>, cx: Option<&ItemContext>, o: &Operand) {
        match o {
            Operand::Copy(s) => self.place(db, cx, *s),
            Operand::Move(s) => self.place(db, cx, *s),
            Operand::Literal(l) => w!(self, Magenta, "${l}"),
        }
    }

    fn folding(&mut self, db: Option<&dyn crate::Db>, cx: Option<&ItemContext>, f: Folding) {
        match f {
            Folding::Fold { into } => {
                w!(self, Red, "fold ");
                self.place(db, cx, into);
                wln!(self, Default, "");
            }
            Folding::Unfold { consume } => {
                w!(self, Red, "unfold ");
                self.place(db, cx, consume);
                wln!(self, Default, "");
            }
        }
    }

    fn expr(&mut self, db: &dyn crate::Db, cx: Option<&ItemContext>, e: &MExpr) {
        match e {
            MExpr::Use(s) => self.operand(Some(db), cx, s),
            MExpr::Ref(bk, p) => {
                match bk {
                    BorrowKind::Shared => w!(self, Default, "&"),
                    BorrowKind::Mutable => w!(self, Default, "&mut "),
                }
                self.place(Some(db), cx, *p);
            }
            MExpr::Struct(s, fields) => {
                w!(self, Default, "{} {{", s.name(db));
                let mut first = true;
                for (field, slot) in fields {
                    if !first {
                        w!(self, Default, ",");
                    }
                    first = false;
                    w!(self, Default, " {}: ", field.name(db));
                    self.operand(Some(db), cx, slot);
                }
                w!(self, Default, " }}");
            }
            // MExpr::Quantifier(_, q, args, body) => {
            //     w!(self, Default, "{q} (");
            //     for arg in args {
            //         self.operand(db, cx, arg);
            //     }
            //     w!(self, Default, ") ");
            //     self.block_id(Some(*body));
            // }
            MExpr::BinaryOp(op, l, r) => {
                w!(self, Default, "({op} ");
                self.operand(Some(db), cx, l);
                w!(self, Default, " ");
                self.operand(Some(db), cx, r);
                w!(self, Default, ")");
            }
            MExpr::UnaryOp(op, x) => {
                w!(self, Default, "({op} ");
                self.operand(Some(db), cx, x);
                w!(self, Default, ")");
            }
        }
    }

    fn function(&mut self, cx: Option<&ItemContext>, f: FunctionId) {
        match &self.body.functions[f].data {
            FunctionData::Named(var) => {
                if let Some(cx) = cx {
                    w!(self, Default, "{}", cx.var_name(*var))
                } else {
                    w!(self, Default, "{var:?}")
                }
            }
            FunctionData::List => w!(self, Default, "#list"),
            FunctionData::ListConcat => w!(self, Default, "#list-concat"),
            FunctionData::Index => w!(self, Default, "#index"),
            FunctionData::RangeIndex => w!(self, Default, "#range-index"),
            FunctionData::Range(kind) => w!(self, Default, "#range[{kind}]"),
        }
    }

    fn block_id(&mut self, bid: Option<BlockId>) {
        if let Some(bid) = bid {
            w!(self, Green, "{bid}")
        } else {
            w!(self, Green, ":B!")
        }
    }
    fn terminator(
        &mut self,
        db: Option<&dyn crate::Db>,
        cx: Option<&ItemContext>,
        term: &Terminator,
    ) {
        match term {
            Terminator::Return => wln!(self, Default, "!return"),
            Terminator::Goto(b) => {
                w!(self, Yellow, "!goto ");
                self.block_id(Some(*b));
                wln!(self, Default, "");
            }
            Terminator::Quantify(q, over, b) => {
                w!(self, Yellow, "!{q} ");
                for s in over {
                    self.slot(cx, *s);
                }
                w!(self, Default, " :: ");
                self.block_id(Some(*b));
                wln!(self, Default, "");
            }
            Terminator::QuantifyEnd(b) => {
                w!(self, Yellow, ":quatifier-end ");
                self.block_id(Some(*b));
                wln!(self, Default, "");
            }
            Terminator::Switch(cond, switch) => {
                w!(self, Yellow, "!switch ");
                self.operand(db, cx, cond);
                w!(self, Default, " {{");
                for (idx, value) in switch.values.iter() {
                    w!(self, Default, " {value} -> ");
                    self.block_id(Some(switch.targets[idx]));
                }
                w!(self, Default, ", otherwise ");
                self.block_id(Some(switch.otherwise));
                wln!(self, Default, " }}");
            }
            Terminator::Call { func, args, destination, target } => {
                w!(self, Yellow, "!call ");

                self.place(db, cx, *destination);
                w!(self, Default, " := ");

                w!(self, Default, "(");
                self.function(cx, *func);
                for arg in args {
                    w!(self, Default, " ");
                    self.operand(db, cx, arg);
                }
                w!(self, Default, ")");
                w!(self, Default, " -> ");
                self.block_id(*target);
                wln!(self, Default, "");
            }
        }
    }

    fn with_color(self, color: Color) -> Self {
        if color == Color::Yes {
            Self { color, indentation: 10, ..self }
        } else {
            Self { color, ..self }
        }
    }

    fn with_annotator(mut self, f: Box<dyn Fn(BodyLocation) -> Option<String>>) -> Self {
        self.annotator = Some(f);
        self
    }
}
