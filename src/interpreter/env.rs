use std::collections::HashMap;

use super::object::Object;

#[derive(Debug, Clone)]
pub(super) struct Env {
    parent: Option<Box<Env>>,
    symbols: HashMap<String, Symbol>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            parent: None,
            symbols: HashMap::new(),
        }
    }

    pub fn get_symbol(&mut self, identifier: &str) -> Option<&mut Symbol> {
        self.symbols
            .get_mut(identifier)
            .or_else(|| self.parent.as_mut()?.get_symbol(identifier))
    }

    pub fn insert_symbol(&mut self, identifier: String, symbol: Symbol) {
        self.symbols.insert(identifier, symbol);
    }

    pub fn enter_scope(&mut self) {
        let new_env = Env {
            parent: Some(Box::new(self.clone())),
            symbols: HashMap::new(),
        };
        *self = new_env;
    }

    pub fn exit_scope(&mut self) {
        if let Some(parent) = self.parent.take() {
            *self = *parent;
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
pub(super) enum Symbol {
    Variable(Object),
}
