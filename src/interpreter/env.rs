use std::collections::HashMap;

use super::object::Object;

#[derive(Debug, Default, Clone)]
pub(super) struct Env {
    parent: Option<Box<Env>>,
    symbols: HashMap<String, Symbol>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_symbol(&mut self, identifier: &str) -> Option<&mut Symbol> {
        if let Some(parent) = self.parent.as_mut() {
            if let Some(value) = parent.get_symbol(identifier) {
                return Some(value);
            }
        }

        self.symbols.get_mut(identifier)
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

#[derive(Debug, Clone)]
pub(super) enum Symbol {
    Variable(Object),
}
