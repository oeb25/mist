use std::collections::HashMap;

use crate::{
    mir::{BlockOrInstruction, InstructionId, SlotId},
    mono::exprs::{ExprPtr, VariablePtr},
    util::{IdxMap, SourceMapped, SourceMappedMulti},
};

use super::BlockId;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BodySourceMap {
    expr_instr_map: HashMap<ExprPtr, Vec<InstructionId>>,
    expr_instr_map_back: IdxMap<InstructionId, ExprPtr>,
    expr_block_map: HashMap<ExprPtr, BlockId>,
    expr_block_map_back: IdxMap<BlockId, ExprPtr>,
    var_map: HashMap<VariablePtr, SlotId>,
    var_map_back: IdxMap<SlotId, VariablePtr>,
}

impl SourceMapped<ExprPtr, BlockId> for BodySourceMap {
    fn register(&mut self, src: ExprPtr, dst: BlockId) {
        self.expr_block_map.insert(src, dst);
        self.expr_block_map_back.insert(dst, src);
    }

    fn find(&self, src: ExprPtr) -> Option<BlockId> {
        self.expr_block_map.get(&src).copied()
    }

    fn back(&self, dst: BlockId) -> Option<ExprPtr> {
        self.expr_block_map_back.get(dst).copied()
    }
}

impl SourceMappedMulti<ExprPtr, InstructionId> for BodySourceMap {
    fn register_multi(&mut self, src: ExprPtr, dst: InstructionId) {
        self.expr_instr_map.entry(src).or_default().push(dst);
        self.expr_instr_map_back.insert(dst, src);
    }

    fn find_multi(&self, src: ExprPtr) -> &[InstructionId] {
        self.expr_instr_map.get(&src).map(|xs| xs.as_slice()).unwrap_or_default()
    }

    fn back_multi(&self, dst: InstructionId) -> Option<ExprPtr> {
        self.expr_instr_map_back.get(dst).copied()
    }
}

impl SourceMapped<VariablePtr, SlotId> for BodySourceMap {
    fn register(&mut self, src: VariablePtr, dst: SlotId) {
        self.var_map.insert(src, dst);
        self.var_map_back.insert(dst, src);
    }

    fn find(&self, src: VariablePtr) -> Option<SlotId> {
        self.var_map.get(&src).copied()
    }

    fn back(&self, dst: SlotId) -> Option<VariablePtr> {
        self.var_map_back.get(dst).copied()
    }
}

impl BodySourceMap {
    pub fn trace_expr(&self, instr_or_block: impl Into<BlockOrInstruction>) -> Option<ExprPtr> {
        match instr_or_block.into() {
            BlockOrInstruction::Block(b) => self.back(b),
            BlockOrInstruction::Instruction(b) => self.back_multi(b),
        }
    }
}
