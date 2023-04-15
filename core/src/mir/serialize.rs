use std::fmt::Write;

use derive_new::new;

use crate::{
    hir::{self, Program},
    typecheck::ItemContext,
};

use super::{
    BlockId, Body, FunctionData, FunctionId, Instruction, InstructionId, MExpr, Slot, SlotId,
};

#[derive(new)]
struct Serializer<'a> {
    db: &'a dyn crate::Db,
    program: Program,
    cx: &'a ItemContext,
    body: &'a Body,
    #[new(default)]
    output: String,
    #[new(default)]
    start_of_line: bool,
    #[new(default)]
    indentation: usize,
}

impl Body {
    pub fn serialize(&self, db: &dyn crate::Db, program: Program, cx: &ItemContext) -> String {
        Serializer::new(db, program, cx, self).finish()
    }
}

impl MExpr {
    pub fn serialize(
        &self,
        db: &dyn crate::Db,
        program: Program,
        cx: &ItemContext,
        body: &Body,
    ) -> String {
        let mut s = Serializer::new(db, program, cx, body);
        s.expr(self);
        s.output
    }
}
pub fn serialize_slot(
    db: &dyn crate::Db,
    program: Program,
    cx: &ItemContext,
    body: &Body,
    slot: SlotId,
) -> String {
    let mut s = Serializer::new(db, program, cx, body);
    s.slot(slot);
    s.output
}

macro_rules! w {
    ($x:ident, $($t:tt)*) => {{
        if $x.start_of_line {
            for _ in 0..$x.indentation {
                write!($x.output, "  ").unwrap();
            }
        }
        write!($x.output, $($t)*).unwrap();
        $x.start_of_line = false;
    }};
}
macro_rules! wln {
    ($x:ident, $($t:tt)*) => {{
        if $x.start_of_line {
            for _ in 0..$x.indentation {
                write!($x.output, "  ").unwrap();
            }
        }
        writeln!($x.output, $($t)*).unwrap();
        $x.start_of_line = true;
    }};
}

impl Serializer<'_> {
    fn finish(mut self) -> String {
        if let Some(body) = self.body.body_block {
            self.block(body);
        }

        self.output
    }

    fn indented(&mut self, f: impl FnOnce(&mut Self)) {
        self.indentation += 1;
        f(self);
        self.indentation -= 1;
    }

    fn block(&mut self, body: BlockId) {
        wln!(self, "{{");
        self.indented(|this| {
            for inst in &this.body.blocks[body].instructions {
                this.inst(*inst);
            }
        });
        wln!(self, "}}");
    }

    fn inst(&mut self, inst: InstructionId) {
        match &self.body.instructions[inst] {
            Instruction::Assign(s, e) => {
                self.slot(*s);
                w!(self, " := ");
                self.expr(e);
                wln!(self, "");
            }
            &Instruction::If(cond, then_block, else_block) => {
                w!(self, "if ");
                self.slot(cond);
                w!(self, " ");
                self.block(then_block);
                w!(self, "else ");
                self.block(else_block);
            }
            Instruction::While(cond, invs, body) => {
                w!(self, "while ");
                self.slot(*cond);
                wln!(self, "");
                for inv in invs {
                    w!(self, "  inv(");
                    self.slot(self.body.blocks[*inv].dest.unwrap());
                    w!(self, ") ");
                    self.indentation += 1;
                    self.block(*inv);
                    self.indentation -= 1;
                }
                self.block(*body);
            }
            Instruction::Assertion(kind, slot) => {
                w!(self, "{kind} ");
                self.slot(*slot);
                wln!(self, "");
            }
            Instruction::Call(_, _) => todo!(),
            Instruction::Return => todo!(),
        }
    }

    fn slot(&mut self, s: SlotId) {
        match &self.body.slots[s] {
            Slot::Temp => w!(self, "%{}", s.into_raw()),
            Slot::Var(v) => w!(self, "%{}_{}", s.into_raw(), self.cx.var_ident(*v)),
            Slot::Literal(l) => w!(self, "${l}"),
            Slot::Result => w!(self, "%result"),
        }
    }

    fn expr(&mut self, e: &MExpr) {
        match e {
            MExpr::Literal(l) => w!(self, "{l}"),
            MExpr::Call(f, args) => {
                w!(self, "(");
                self.function(*f);
                for arg in args {
                    w!(self, " ");
                    self.slot(*arg);
                }
                w!(self, ")");
            }
            MExpr::Slot(s) => self.slot(*s),
            MExpr::Field(base, f) => {
                self.slot(*base);
                w!(self, ".{}", f.name);
            }
            MExpr::Struct(s, fields) => {
                w!(self, "{} {{", s.name(self.db));
                let mut first = true;
                for (field, slot) in fields {
                    if !first {
                        w!(self, ",");
                    }
                    first = false;
                    w!(self, " {}: ", field.name);
                    self.slot(*slot);
                }
                w!(self, " }}");
            }
            MExpr::Quantifier(_, _, _, _) => todo!(),
        }
    }

    fn function(&mut self, f: FunctionId) {
        match &self.body.functions[f].data {
            FunctionData::Named(var) => w!(self, "{}", self.cx.var_ident(*var)),
            FunctionData::BinaryOp(op) => w!(self, "{op}"),
            FunctionData::UnaryOp(op) => w!(self, "{op}"),
            FunctionData::List => w!(self, "#list"),
            FunctionData::Index => w!(self, "#index"),
            FunctionData::RangeIndex => w!(self, "#range-index"),
            FunctionData::Range(kind) => w!(self, "#range[{kind}]"),
        }
    }
}
