use std::{
    cell::RefCell,
    fmt::{Debug, Display, Formatter},
    rc::Rc,
};

use crate::ast::{IdentifierStruct, Statement};

use super::{env::Env, evaluator::Interpreter};

#[derive(Debug, Clone)]
pub enum Object {
    True,
    False,
    Nil,
    Number(f64),
    String(String),
    Function(Rc<dyn Callable>),

    // Internal Objects. Cannot be stored in variables. They are a implementation detail of the interpreter.
    /// Represents a return value from a function
    Return(Box<Object>),
    /// Represents an empty value that is returned by statements, like `if` and `while`
    Unit,
}

// Define a trait for callable functions
pub trait Callable: Debug + Display + 'static {
    fn call(&self, interpreter: &mut Interpreter, args: &[Object]) -> anyhow::Result<Object>;
    fn arity(&self) -> usize;
    fn name(&self) -> &str;
}

// Native function implementation
#[derive(Debug)]
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
#[derive(Debug)]
pub struct LoxFunction {
    name: String,
    params: Vec<IdentifierStruct>,
    body: Box<Statement>,
    closure: Rc<RefCell<Env>>,
}

impl LoxFunction {
    pub fn new(
        name: &str,
        params: Vec<IdentifierStruct>,
        body: Box<Statement>,
        closure: Rc<RefCell<Env>>,
    ) -> Self {
        Self {
            name: name.to_owned(),
            params,
            body,
            closure,
        }
    }
}

impl Callable for LoxFunction {
    fn call(&self, interpreter: &mut Interpreter, args: &[Object]) -> anyhow::Result<Object> {
        let previous = Rc::clone(&interpreter.env);
        let env = Env::new_from_parent(&self.closure);

        for (param, arg) in self.params.iter().zip(args) {
            env.borrow_mut().define(&param.name, arg.clone());
        }

        interpreter.env = env;

        let result = match interpreter.execute_statement(&self.body)? {
            // If we get a return object, extract its value
            Object::Return(value) => *value,
            // Otherwise, return nil
            _ => Object::Nil,
        };

        // Restore the previous environment
        interpreter.env = previous;
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

    pub fn new_user_fn(
        name: &str,
        params: Vec<IdentifierStruct>,
        body: Box<Statement>,
        closure: Env,
    ) -> Self {
        let closure = Rc::new(RefCell::new(closure));

        let func = Self::Function(Rc::new(LoxFunction::new(
            name,
            params,
            body,
            Rc::clone(&closure),
        )));

        // Define the function in the closure environment
        // This allows the function to be called recursively
        closure.borrow_mut().define(name, func.clone());
        func
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
            Self::Return(obj) => write!(f, "<return {}>", obj),
            Self::Unit => write!(f, "<unit>"),
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
