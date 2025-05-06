use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

use super::object::Object;

#[derive(Debug, Clone)]
pub struct Env {
    parent: Option<Rc<RefCell<Env>>>,
    symbols: HashMap<String, Object>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            parent: None,
            symbols: HashMap::new(),
        }
    }

    pub fn new_from_parent(parent: &Rc<RefCell<Env>>) -> Rc<RefCell<Self>> {
        let new = Self {
            parent: Some(Rc::clone(parent)),
            symbols: HashMap::new(),
        };

        Rc::new(RefCell::new(new))
    }

    pub fn get_symbol(&self, identifier: &str) -> Option<Object> {
        if let Some(symbol) = self.symbols.get(identifier) {
            return Some(symbol.clone());
        }

        if let Some(parent) = &self.parent {
            return parent.borrow().get_symbol(identifier);
        }

        None
    }

    pub fn define(&mut self, identifier: &str, symbol: Object) {
        self.symbols.insert(identifier.to_owned(), symbol);
    }

    pub fn assign(&mut self, identifier: &str, symbol: Object) -> anyhow::Result<()> {
        if let Some(existing_symbol) = self.symbols.get_mut(identifier) {
            *existing_symbol = symbol;
            return Ok(());
        }

        if let Some(parent) = &self.parent {
            return parent.borrow_mut().assign(identifier, symbol);
        }

        Err(anyhow::anyhow!("Symbol {} not found", identifier))
    }

    pub fn get_parent(&self) -> Option<Rc<RefCell<Env>>> {
        self.parent.as_ref().map(Rc::clone)
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (key, value) in &self.symbols {
            writeln!(f, "{}: {}", key, value)?;
        }
        if let Some(parent) = &self.parent {
            Display::fmt(&parent.borrow(), f)?;
        }
        Ok(())
    }
}
