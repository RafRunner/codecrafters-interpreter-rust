use std::fmt::{Display, Formatter};

use super::evaluator::Interpreter;

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    True,
    False,
    Nil,
    Number(f64),
    String(String),
    Callable {
        arity: usize,
        call: fn(&mut Interpreter, &[Object]) -> anyhow::Result<Object>,
    },
}

impl Object {
    pub fn bool_as_obj(val: bool) -> Self {
        if val {
            Self::True
        } else {
            Self::False
        }
    }

    pub fn is_truthy(&self) -> bool {
        !matches!(self, Self::False | Self::Nil)
    }

    pub fn as_bool_obj(&self) -> Self {
        Self::bool_as_obj(self.is_truthy())
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Nil => write!(f, "nil"),
            Self::Number(n) => write!(f, "{}", n),
            Self::String(s) => write!(f, "{}", s),
            Self::Callable { arity, .. } => write!(f, "<fn {}>", arity),
        }
    }
}
