use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

use super::object::Object;

#[derive(Debug)]
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
        let depth = self.find_definition(identifier);
        match depth {
            Some(depth) => {
                self.assing_at_depth(identifier, symbol, depth);
                Ok(())
            }
            None => Err(anyhow::anyhow!("Undefined variable '{}'", identifier)),
        }
    }

    pub fn get_parent(&self) -> Option<Rc<RefCell<Env>>> {
        self.parent.as_ref().map(Rc::clone)
    }

    fn find_definition(&self, identifier: &str) -> Option<usize> {
        if self.symbols.contains_key(identifier) {
            return Some(0);
        }

        if let Some(parent) = &self.parent {
            if let Some(depth) = parent.borrow().find_definition(identifier) {
                return Some(depth + 1);
            }
        }

        None
    }

    /// Depth needs to be checked before calling this function
    fn assing_at_depth(&mut self, identifier: &str, symbol: Object, depth: usize) {
        if depth == 0 {
            self.symbols.insert(identifier.to_owned(), symbol);
        } else {
            self.parent.as_ref().unwrap().borrow_mut().assing_at_depth(
                identifier,
                symbol,
                depth - 1,
            )
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Env {{ symbols: {} }}",
            self.symbols
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}
