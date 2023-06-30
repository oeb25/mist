use std::fmt::Write;

use derive_new::new;
use owo_colors::{colors::*, OwoColorize};

use crate::mir::{Projection, Terminator};

use super::{
    def::InBlock, Action, BlockId, Body, BorrowKind, Folding, Function, Instruction, InstructionId,
    MExpr, Operand, Place, Slot, SlotId, TerminatorKind,
};

#[derive(new)]
struct Serializer<'a, A> {
    color: Color,
    db: &'a dyn crate::Db,
    body: &'a Body,
    annotator: A,
    #[new(default)]
    output: String,
    #[new(default)]
    start_of_line: bool,
    #[new(default)]
    indentation: usize,
}

impl Body {
    pub fn serialize_with_annotation(
        &self,
        db: &dyn crate::Db,
        color: Color,
        f: impl Fn(InBlock<Action>) -> Option<String>,
    ) -> String {
        Serializer::new(color, db, self, f).finish()
    }
    pub fn serialize(&self, db: &dyn crate::Db, color: Color) -> String {
        Serializer::new(color, db, self, |_| None).finish()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Color {
    No,
    Yes,
}

impl MExpr {
    pub fn serialize(&self, color: Color, db: &dyn crate::Db, body: &Body) -> String {
        let mut s = Serializer::new(color, db, body, |_| None);
        s.expr(self);
        s.output
    }
}
pub fn serialize_terminator(
    color: Color,
    db: &dyn crate::Db,
    body: &Body,
    term: Terminator,
) -> String {
    let mut s = Serializer::new(color, db, body, |_| None).with_color(color);
    s.terminator(term);
    s.output
}
pub fn serialize_block(color: Color, db: &dyn crate::Db, body: &Body, bid: BlockId) -> String {
    let mut s = Serializer::new(color, db, body, |_| None).with_color(color);
    s.block(bid);
    s.output
}
pub fn serialize_slot(color: Color, db: &dyn crate::Db, body: &Body, slot: SlotId) -> String {
    let mut s = Serializer::new(color, db, body, |_| None).with_color(color);
    s.slot(slot);
    s.output
}
pub fn serialize_place(color: Color, db: &dyn crate::Db, body: &Body, place: Place) -> String {
    let mut s = Serializer::new(color, db, body, |_| None).with_color(color);
    s.place(place);
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

impl<'db, A: Fn(InBlock<Action>) -> Option<String>> Serializer<'db, A> {
    fn finish(mut self) -> String {
        for bid in self.body.blocks().collect::<Vec<_>>() {
            self.block(bid);
        }

        self.output
    }

    fn indented(&mut self, f: impl FnOnce(&mut Self)) {
        self.indentation += 1;
        f(self);
        self.indentation -= 1;
    }

    fn block(&mut self, bid: BlockId) {
        self.block_id(Some(bid));
        wln!(self, Default, "");
        self.indented(|this| {
            let mut printed = false;

            for act in bid.actions(this.body) {
                printed = true;
                if let Some(s) = (this.annotator)(act.in_block(bid)) {
                    wln!(this, Default, "{s}");
                }
                this.action(act);
            }

            if !printed {
                if let Some(s) =
                    (this.annotator)(Action::from(Terminator::returns(self.db)).in_block(bid))
                {
                    wln!(this, Default, "{s}");
                }
            }
        });
    }

    fn action(&mut self, act: Action) {
        match act {
            Action::Instruction(inst) => self.inst(inst),
            Action::Terminator(term) => self.terminator(term),
        }
    }
    fn inst(&mut self, inst: InstructionId) {
        match inst.data(self.body) {
            Instruction::Assign(t, e) => {
                self.place(*t);
                w!(self, Default, " := ");
                self.expr(e);
                wln!(self, Default, "");
            }
            Instruction::NewAdt(t, s, fields) => {
                self.place(*t);
                w!(self, Default, " := {} {{", s.name(self.db));
                let mut first = true;
                for (field, slot) in fields {
                    if !first {
                        w!(self, Default, ",");
                    }
                    first = false;
                    w!(self, Default, " {}: ", field.name(self.db));
                    self.operand(slot);
                }
                wln!(self, Default, " }}");
            }
            Instruction::Assertion(kind, expr) => {
                w!(self, Default, "{kind} ");
                self.expr(expr);
                wln!(self, Default, "");
            }
            Instruction::PlaceMention(p) => {
                w!(self, Default, "mention ");
                self.place(*p);
                wln!(self, Default, "");
            }
            Instruction::Folding(folding) => {
                self.folding(*folding);
            }
        }
    }

    fn slot(&mut self, s: SlotId) {
        match s.data(self.body) {
            Slot::Param(v) => w!(self, Cyan, "{s}_{}", v.name(self.db)),
            Slot::Quantified(v) => w!(self, Cyan, "{s}_{}", v.name(self.db)),
            Slot::Local(v) => w!(self, Cyan, "{s}_{}", v.name(self.db)),
            Slot::Result => w!(self, Magenta, "%result"),
            Slot::Self_ => w!(self, Magenta, "%self"),
            _ => w!(self, Cyan, "{s}"),
        }
    }

    fn place(&mut self, s: Place) {
        if !s.has_projection(self.db) {
            self.slot(s.slot());
        } else {
            self.slot(s.slot());
            for p in s.projection_iter(self.db) {
                match p {
                    Projection::Field(f, _) => {
                        let name = &f.name(self.db);
                        w!(self, Default, ".{name}");
                    }
                    Projection::Index(idx, _) => {
                        w!(self, Default, "[");
                        self.slot(idx);
                        w!(self, Default, "]");
                    }
                }
            }
        }
    }

    fn operand(&mut self, o: &Operand) {
        match o {
            Operand::Copy(s) => self.place(*s),
            Operand::Move(s) => self.place(*s),
            Operand::Literal(l) => w!(self, Magenta, "${l}"),
        }
    }

    fn folding(&mut self, f: Folding) {
        match f {
            Folding::Fold { into } => {
                w!(self, Red, "fold ");
                self.place(into);
                wln!(self, Default, "");
            }
            Folding::Unfold { consume } => {
                w!(self, Red, "unfold ");
                self.place(consume);
                wln!(self, Default, "");
            }
        }
    }

    fn expr(&mut self, e: &MExpr) {
        match e {
            MExpr::Use(s) => self.operand(s),
            MExpr::Ref(bk, p) => {
                match bk {
                    BorrowKind::Shared => w!(self, Default, "&"),
                    BorrowKind::Mutable => w!(self, Default, "&mut "),
                }
                self.place(*p);
            }
            // MExpr::Quantifier(_, q, args, body) => {
            //     w!(self, Default, "{q} (");
            //     for arg in args {
            //         self.operand( arg);
            //     }
            //     w!(self, Default, ") ");
            //     self.block_id(Some(*body));
            // }
            MExpr::BinaryOp(op, l, r) => {
                w!(self, Default, "({op} ");
                self.operand(l);
                w!(self, Default, " ");
                self.operand(r);
                w!(self, Default, ")");
            }
            MExpr::UnaryOp(op, x) => {
                w!(self, Default, "({op} ");
                self.operand(x);
                w!(self, Default, ")");
            }
        }
    }

    fn function(&mut self, f: Function) {
        match f {
            Function::Named(var) => w!(self, Default, "{}", var.name(self.db)),
            Function::BuiltinMethod(bf) => w!(self, Default, "{}", bf.name()),
            Function::List => w!(self, Default, "#list"),
            Function::ListConcat => w!(self, Default, "#list-concat"),
            Function::Index => w!(self, Default, "#index"),
            Function::RangeIndex => w!(self, Default, "#range-index"),
            Function::Range(kind) => w!(self, Default, "#range[{kind}]"),
            Function::InRange => w!(self, Default, "#in_range"),
            Function::RangeMin => w!(self, Default, "#range_min"),
            Function::RangeMax => w!(self, Default, "#range_max"),
        }
    }

    fn block_id(&mut self, bid: Option<BlockId>) {
        if let Some(bid) = bid {
            w!(self, Green, "{bid}")
        } else {
            w!(self, Green, ":B!")
        }
    }
    fn terminator(&mut self, term: Terminator) {
        match term.kind(self.db) {
            TerminatorKind::Return => wln!(self, Default, "!return"),
            TerminatorKind::Goto(b) => {
                w!(self, Yellow, "!goto ");
                self.block_id(Some(*b));
                wln!(self, Default, "");
            }
            TerminatorKind::Quantify(q, over, b) => {
                w!(self, Yellow, "!{q} ");
                for s in over {
                    self.slot(*s);
                }
                w!(self, Default, " :: ");
                self.block_id(Some(*b));
                wln!(self, Default, "");
            }
            TerminatorKind::QuantifyEnd(b) => {
                w!(self, Yellow, ":quatifier-end ");
                self.block_id(Some(*b));
                wln!(self, Default, "");
            }
            TerminatorKind::Switch(cond, switch) => {
                w!(self, Yellow, "!switch ");
                self.operand(cond);
                w!(self, Default, " {{");
                let (values, otherwise) = switch.values();
                for (value, target) in values {
                    w!(self, Default, " {value} -> ");
                    self.block_id(Some(target));
                }
                w!(self, Default, ", otherwise ");
                self.block_id(Some(otherwise));
                wln!(self, Default, " }}");
            }
            TerminatorKind::Call { func, args, destination, target } => {
                w!(self, Yellow, "!call ");

                self.place(*destination);
                w!(self, Default, " := ");

                w!(self, Default, "(");
                self.function(*func);
                for arg in args {
                    w!(self, Default, " ");
                    self.operand(arg);
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
}
