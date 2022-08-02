//! Types of an abstract syntax tree (AST) that represents OCR Exam Reference Language code in a way that is much easier for an interpreter, compiler, etc. to
//! process than the characters within the source.

// Represents a sub-program that can be called.
#[derive(Clone, Debug, PartialEq)]
pub enum Callee {
    /// Calling a sub-program directly, e.g. `print("Hello World")`
    SubProgram(String),
    /// Calling a member sub-program, e.g. `"myString".substring(1, 2)`
    Member { object: Expression, member: String },
}

/// Represents a sub-program call, e.g. `print("Hello World")`
#[derive(Clone, Debug, PartialEq)]
pub struct Call {
    /// The sub-program being called
    pub callee: Box<Callee>,
    /// The arguments passed to the sub-program
    pub args: Vec<Expression>,
}

/// Represents any expression that can be assigned to
#[derive(Clone, Debug, PartialEq)]
pub enum Assignable {
    /// An array index, e.g. `myArray[5]` can be assigned
    Index {
        to_index: Box<Expression>,
        indices: Vec<Expression>,
    },
    /// A property value, e.g. `myObject.property` *should* be assignable in theory,
    /// although none of the types in ERL allow this as of now. (e.g. a string's `length` property cannot be assigned).
    Property {
        /// The value to get the property of.
        value: Box<Expression>,
        /// The name of the property to get, e.g. `length`.
        name: String,
    },
    /// Variables can obviously be assigned directly
    Variable(String),
}

/// An operator that takes two operands and produces one output.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BinaryOperator {
    /// `+`
    Add,
    /// `-`
    Subtract,
    /// `*`
    Multiply,
    /// `/`
    Divide,
    /// `^`
    Power,
    /// `>`
    GreaterThan,
    /// `>=`
    GreaterThanOrEquals,
    /// `<`
    LessThan,
    /// `<=`
    LessThanOrEquals,
    /// `==`
    Equals,
    /// `!=`
    NotEquals,
    /// `DIV`
    Quotient,
    /// `MOD`
    Remainder,
    /// `AND`
    And,
    /// `OR`
    Or,
}

/// An operator that takes one operand and produces one output.
/// Currently `NOT` is the only unary operator, but this is declarared as an enum to allow adding more.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum UnaryOperator {
    /// `NOT`
    Not,
}

/// Represents any expression that has a value
#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
    /// e.g. `"Hello World"`
    StringLiteral(String),
    /// e.g. `5`
    IntegerLiteral(i64),
    /// e.g. `6.5`
    RealLiteral(f64),
    /// `false` or `true`
    BooleanLiteral(bool),
    /// The given expressions represent the values within the array.
    /// e.g. `[5, 6]` will give `vec![Expression::IntegerLiteral(5), Expression::IntegerLiteral(6)]`
    ArrayLiteral(Vec<Expression>),
    /// Any expression that can be assigned to.
    /// See [Assignable] for more details.
    Assignable(Assignable),
    /// Calling a sub-program.
    /// See [Call] for more details.
    Call(Call),
    /// Any expression made up of two operands and a binary operator, e.g. `5 + 6`.
    Binary {
        /// The operator used
        operator: BinaryOperator,
        /// The left-hand operand
        left: Box<Expression>,
        /// The right-hand operand
        right: Box<Expression>,
    },
    /// Any expression made up of one operand and a unary operator, e.g. `NOT true`
    Unary {
        /// The singular operand
        operand: Box<Expression>,
        /// The operator used
        operator: UnaryOperator,
    },
}

/// A valid statement at the root of the file. (i.e. not within a sub-program, `if` statement or any other block).
#[derive(Debug, Clone, PartialEq)]
pub enum RootStatement {
    /// Sub-programs can only be declared in the file root. (in fact, they are the reason this enum exists)
    SubProgram {
        /// The name of the sub-program
        name: String,
        /// The statements found within the sub-program.
        block: Vec<Statement>,
        /// The names of the arguments of the sub-program (each element is a unique `String`)
        argument_names: Vec<String>,
        /// `true` if the sub-program is a `function`, false if it is a `procedure`
        is_function: bool,
    },
    /// Regular statements are also permitted at file root
    Statement(Statement),
}

/// A value which can be assigned to a variable
#[derive(Debug, Clone, PartialEq)]
pub enum AssignmentValue {
    /// Regular assignment, e.g. `age = 24`
    Expression(Expression),
    /// Creating a blank array, e.g. `array age[5]`.
    /// The given `Vec` contains expressions that provide the length of each dimension of the array.
    BlankArray(Vec<Expression>),
}

/// Represents an `if` or `elseif` portion of an `if` statement.
#[derive(Debug, Clone, PartialEq)]
pub struct IfSegment {
    /// The condition that must be `true` for this block to be executed.
    pub condition: Expression,
    /// The instructions to be executed if `condition` is `true`.
    pub block: Vec<Statement>,
}

/// Statements are found on their own line within a block.
/// This enum encompasses all valid statements.
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// Calling a function is a valid statemnt, since it can have side effects.
    Call(Call),
    /// Assigning to a variable or other [Assignable].
    Assign {
        /// Whether or not the `const` keyword was used in the assignment.
        is_const: bool,
        /// Whether or not the `global` keyword was used in the assignment.
        is_global: bool,
        /// Whether or not the `array` keyword was used in the assignment.
        is_array: bool,
        /// The value to be assigned.
        /// See [Assignable] for more details about what is/isn't assignable.
        to_assign: Assignable,
        /// What to assign to the value.
        /// See [`AssignmentValue`] for more details on possible assignments.
        assign_with: AssignmentValue,
    },
    /// An `if `statement.
    If {
        /// In the correct order, the `if` and `elseif` parts of the statement.
        /// One element in the array corresponds to each `if` or `elseif`
        segments: Vec<IfSegment>,
        /// Optionally, a block to be executed if none of the conditions within the `segments` yield `true`.
        else_block: Option<Vec<Statement>>,
    },
    /// A `while` loop.
    While {
        /// The condition that must be `true` for the loop to continue executing.
        condition: Expression,
        /// The block to be executed while `condition` is `true`.
        block: Vec<Statement>,
    },
    /// A `for` loop.
    For {
        /// An expression that gives the starting value of the iterator variable.
        start: Expression,
        /// An expression that gives the value of the iterator variable that stops the loop.
        /// Note that this value is *inclusive*.
        end: Expression,
        /// Some if a `step` expression is provided that gives the amount to change the iterator variable by per iteration.
        /// None if this is not specified.
        step: Option<Expression>,
        /// The name of the iterator variable.
        variable_name: String,
        /// The block to be executed upon each iterator.
        block: Vec<Statement>,
    },
    /// A `return` statement.
    Return {
        /// The value to return, if any.
        value: Option<Expression>,
    },
}
