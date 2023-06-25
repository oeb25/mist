use super::Module;

#[derive(Debug, Default)]
pub struct ModuleBuilder {}

impl ModuleBuilder {}

impl Module {
    pub fn builder() -> ModuleBuilder {
        ModuleBuilder::default()
    }
}
