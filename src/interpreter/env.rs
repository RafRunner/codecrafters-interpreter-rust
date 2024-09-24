use std::collections::HashMap;

use replace_with::replace_with_or_abort;

use super::object::Object;

#[derive(Debug)]
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
        replace_with_or_abort(self, |_self| Env {
            parent: Some(Box::new(_self)),
            symbols: HashMap::new(),
        });
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

#[derive(Debug)]
pub(super) enum Symbol {
    Variable(Object),
}
