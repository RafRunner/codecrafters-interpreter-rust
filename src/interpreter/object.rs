use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    True,
    False,
    Nil,
    Number(f64),
    String(String),
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
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::True => write!(f, "true"),
            Object::False => write!(f, "false"),
            Object::Nil => write!(f, "nil"),
            Object::Number(n) => write!(f, "{}", n),
            Object::String(s) => write!(f, "{}", s),
        }
    }
}
