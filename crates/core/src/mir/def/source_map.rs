use std::collections::HashMap;

use crate::{
    mir::{BlockOrInstruction, InstructionId, LocalId},
    mono::exprs::{ExprPtr, VariablePtr},
    util::{IdxMap, SourceMapped, SourceMappedMulti},
};

use super::BlockId;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BodySourceMap {
    expr_instr_map: HashMap<ExprPtr, Vec<InstructionId>>,
    expr_instr_map_back: IdxMap<InstructionId, ExprPtr>,
    expr_block_map: HashMap<ExprPtr, Vec<BlockId>>,
    expr_block_map_back: IdxMap<BlockId, ExprPtr>,
    var_map: HashMap<VariablePtr, LocalId>,
    var_map_back: IdxMap<LocalId, VariablePtr>,
}

impl SourceMappedMulti<ExprPtr, BlockId> for BodySourceMap {
    fn register_multi(&mut self, src: ExprPtr, dst: BlockId) {
        self.expr_block_map.entry(src).or_default().push(dst);
        if self.expr_block_map_back.insert(dst, src).is_some() {}
    }

    fn find_multi(&self, src: ExprPtr) -> &[BlockId] {
        self.expr_block_map.get(&src).map(|xs| xs.as_slice()).unwrap_or_default()
    }

    fn back_multi(&self, dst: BlockId) -> Option<ExprPtr> {
        dbg!(dst, self.expr_block_map_back.get(dst).copied()).1
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

impl SourceMapped<VariablePtr, LocalId> for BodySourceMap {
    fn register(&mut self, src: VariablePtr, dst: LocalId) {
        self.var_map.insert(src, dst);
        self.var_map_back.insert(dst, src);
    }

    fn find(&self, src: VariablePtr) -> Option<LocalId> {
        self.var_map.get(&src).copied()
    }

    fn back(&self, dst: LocalId) -> Option<VariablePtr> {
        self.var_map_back.get(dst).copied()
    }
}

impl BodySourceMap {
    pub fn trace_expr(&self, instr_or_block: impl Into<BlockOrInstruction>) -> Option<ExprPtr> {
        match instr_or_block.into() {
            BlockOrInstruction::Block(b) => self.back_multi(b),
            BlockOrInstruction::Instruction(b) => self.back_multi(b),
        }
    }
}
