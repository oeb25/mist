use super::{Local, Param, Result as WasmResult, ValType};

impl ValType {
    pub fn num_bytes(&self) -> u32 {
        match self {
            ValType::I32 => 32,
            ValType::I64 => 64,
            ValType::F32 => 32,
            ValType::F64 => 64,
            ValType::V128 => 128,
            ValType::Funcref => 0,
            ValType::Externref => 0,
        }
    }
}

impl From<ValType> for Param {
    fn from(ty: ValType) -> Self {
        Param { id: None, ty }
    }
}

impl From<ValType> for WasmResult {
    fn from(ty: ValType) -> Self {
        WasmResult { ty }
    }
}

impl From<ValType> for Local {
    fn from(ty: ValType) -> Self {
        Local { id: None, ty }
    }
}
