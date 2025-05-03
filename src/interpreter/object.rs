use std::{
    fmt::{Debug, Display, Formatter},
    rc::Rc,
};

use crate::ast::{IdentifierStruct, Statement};

use super::evaluator::Interpreter;

// Define a trait for callable functions
pub trait Callable: Debug + Display + 'static {
    fn call(&self, interpreter: &mut Interpreter, args: &[Object]) -> anyhow::Result<Object>;
    fn arity(&self) -> usize;
    fn name(&self) -> &str;
}

// Native function implementation
#[derive(Debug, Clone)]
pub struct NativeFunction {
    name: String,
    arity: usize,
    func: fn(&mut Interpreter, &[Object]) -> anyhow::Result<Object>,
}

impl NativeFunction {
    pub fn new(
        name: &str,
        arity: usize,
        func: fn(&mut Interpreter, &[Object]) -> anyhow::Result<Object>,
    ) -> Self {
        Self {
            name: name.to_owned(),
            arity,
            func,
        }
    }
}

impl Callable for NativeFunction {
    fn call(&self, interpreter: &mut Interpreter, args: &[Object]) -> anyhow::Result<Object> {
        (self.func)(interpreter, args)
    }

    fn arity(&self) -> usize {
        self.arity
    }

    fn name(&self) -> &str {
        &self.name
    }
}

impl Display for NativeFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native fn {}>", self.name())
    }
}

// User-defined function that captures parameters and body
#[derive(Debug, Clone)]
pub struct LoxFunction {
    name: String,
    params: Vec<IdentifierStruct>,
    body: Box<Statement>,
}

impl LoxFunction {
    pub fn new(name: &str, params: Vec<IdentifierStruct>, body: Box<Statement>) -> Self {
        Self {
            name: name.to_owned(),
            params,
            body,
        }
    }
}

impl Callable for LoxFunction {
    fn call(&self, interpreter: &mut Interpreter, args: &[Object]) -> anyhow::Result<Object> {
        interpreter.env.enter_scope();

        for (param, arg) in self.params.iter().zip(args) {
            interpreter.env.insert_symbol(&param.name, arg.clone());
        }

        let result = match interpreter.execute_statement(&self.body)? {
            Some(obj) => obj,
            None => Object::Nil,
        };

        interpreter.env.exit_scope();
        Ok(result)
    }

    fn arity(&self) -> usize {
        self.params.len()
    }

    fn name(&self) -> &str {
        &self.name
    }
}

impl Display for LoxFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<fn {}>", self.name())
    }
}

#[derive(Debug, Clone)]
pub enum Object {
    True,
    False,
    Nil,
    Number(f64),
    String(String),
    Function(Rc<dyn Callable>),
}

impl Object {
    pub fn new_bool(val: bool) -> Self {
        if val {
            Self::True
        } else {
            Self::False
        }
    }

    pub fn new_native_fn(
        name: &str,
        arity: usize,
        func: fn(&mut Interpreter, &[Object]) -> anyhow::Result<Object>,
    ) -> Self {
        Self::Function(Rc::new(NativeFunction::new(name, arity, func)))
    }

    pub fn new_user_fn(name: &str, params: Vec<IdentifierStruct>, body: Box<Statement>) -> Self {
        Self::Function(Rc::new(LoxFunction::new(name, params, body)))
    }

    pub fn is_truthy(&self) -> bool {
        !matches!(self, Self::False | Self::Nil)
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Nil => write!(f, "nil"),
            Self::Number(n) => {
                if n.fract() == 0.0 {
                    write!(f, "{:.0}", n)
                } else {
                    write!(f, "{}", n)
                }
            }
            Self::String(s) => write!(f, "{}", s),
            Self::Function(fun) => Display::fmt(fun, f),
        }
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::True, Self::True) => true,
            (Self::False, Self::False) => true,
            (Self::Nil, Self::Nil) => true,
            (Self::Number(a), Self::Number(b)) => a == b,
            (Self::String(a), Self::String(b)) => a == b,
            _ => false,
        }
    }
}
