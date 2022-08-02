//! Consumes the token stream created by the lexer and uses it to produce the abstract syntax tree.
//! The parser itself is the most complicated part of this crate, as it has to handle a lot of different edge cases.

use crate::{
    ast::{
        Assignable, AssignmentValue, BinaryOperator, Call, Callee, Expression, IfSegment,
        RootStatement, Statement, UnaryOperator,
    },
    err::SyntaxErrorKind,
    tokens::Token,
    Lexer, SyntaxError,
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Assignable, AssignmentValue, Call, Callee, Expression, UnaryOperator};
    use crate::ast::{BinaryOperator, IfSegment};
    use crate::err::SyntaxErrorKind;
    use crate::file::{File, FilePosition};
    use crate::tokens::Token;

    /// Implementation of a lexer used for testing purposes
    /// This allows us to test the parser entirely separately from the lexer
    #[derive(Clone)]
    struct TestLexer {
        /// The tokens being parsed
        tokens: Vec<Token>,
        /// The token about to be read
        current_idx: u32,
        /// The blank example file used for error reporting
        file: File,
    }

    impl Lexer for TestLexer {
        fn at_next_token(&mut self) -> FilePosition {
            // We use the column to store the index of the token within the error.
            // We can then later check that the correct index was returned (that corresponds to the right token).
            // TODO: Using the [FilePosition] to store the token index is hacky, but necessary to store it within a SyntaxError.
            FilePosition::new(0, self.current_idx, self.file.clone())
        }

        fn at_last_token(&self) -> FilePosition {
            // Avoid panics moving backwards out of the file
            FilePosition::new(
                0,
                if self.current_idx == 0 {
                    0
                } else {
                    self.current_idx - 1
                },
                self.file.clone(),
            )
        }

        fn peek_token(&mut self) -> std::result::Result<Token, SyntaxError> {
            match self.tokens.get(self.current_idx as usize) {
                Some(token) => Ok(token.clone()),
                None => Ok(Token::EndOfFile),
            }
        }

        fn consume_token(&mut self) -> std::result::Result<Token, SyntaxError> {
            let result = self.peek_token()?;
            self.current_idx += 1;
            Ok(result)
        }

        fn skip_to_newline(&mut self) {
            if self.tokens.get(self.current_idx as usize - 1) != Some(&Token::EndOfLine) {
                while self
                    .consume_token()
                    .expect("Reading tokens cannot fail on test lexer")
                    != Token::EndOfLine
                {}
            }
        }
    }

    impl TestLexer {
        /// Creates an example lexer containing the given tokens, in a file named appropriately for the tests
        fn new(mut tokens: Vec<Token>) -> Self {
            if tokens.last() != Some(&Token::EndOfLine) {
                tokens.push(Token::EndOfLine);
            }

            TestLexer {
                tokens,
                file: File::from_string("".to_string()),
                current_idx: 0,
            }
        }
    }

    fn wrap_identifier(identifier: &str) -> Token {
        Token::Identifier(identifier.to_string())
    }

    fn wrap_string_literal(value: &str) -> Token {
        Token::StringLiteral(value.to_string())
    }

    /// Returns a mutable reference to a [TestLexer] that will provide the arguments passed as tokens.
    /// Useful for testing parsers with a predefined list of tokens.
    macro_rules! tokens {
        ($( $next:expr ),*) => {
            {
                #[allow(unused)]
                use $crate::{
                    tokens::Token::*, // Allow tokens to be used without qualifying with `Token::` (reduces test size a lot)
                    parser::tests::{
                        wrap_identifier as Identifier, // Avoid having to call `.to_string()` on identifiers
                        wrap_string_literal as StringLiteral // Avoid having to call `.to_string()` on string literals
                    }
                };
                (&mut $crate::parser::tests::TestLexer::new( vec![$( $next ),*]))
            }
        };
    }

    /// Panics if `$err` does not match an error in `$lexer`'s file, of kind `$kind` and with a highlight from `$from_token_idx` to `$to_token_idx`.
    macro_rules! panic_if_incorrect {
        ($err:expr, $lexer: expr, $kind: expr, $from_token_idx: expr, $to_token_idx: expr) => {
            {
                let from_pos = crate::file::FilePosition::new(0, $from_token_idx, $lexer.file.clone());
                let to_pos = crate::file::FilePosition::new(0, $to_token_idx, $lexer.file.clone());
                let expected_err = SyntaxError::new(from_pos, to_pos, $kind);

                if expected_err != $err {
                    panic!("Expected\nErr of kind `{}` from idx {} ({:?}) to idx {} ({:?}) but got\nErr of kind `{}` from idx {} ({:?}) to idx {} ({:?})",
                        $kind,
                        $from_token_idx, $lexer.tokens.get($from_token_idx),
                        $to_token_idx, $lexer.tokens.get($to_token_idx),
                        $err.kind(),
                        $err.tag().from_column(), $lexer.tokens.get($err.tag().from_column() as usize),
                        $err.tag().to_column(), $lexer.tokens.get($err.tag().to_column() as usize)
                    )
                }
            }
        };
    }

    macro_rules! iter_errs {
        ($iter:ident, $lexer: expr, $err:expr $(,$more:expr)*) => {
            let err = $iter.next().expect("Wrong number of errors received");
            panic_if_incorrect!(err, $lexer, $err.0, $err.1, $err.2);

            iter_errs!($iter, $lexer $($more),*);
        };
        ($iter:ident, $lexer: expr) => {};
    }

    macro_rules! assert_errs {
        ($result: expr, $lexer: expr $( , $errs:expr )*) => {
            match $result {
                Ok(_) => panic!("Expected errors but got Ok"),
                Err(errs) => {
                    let mut iter = errs.into_iter();
                    iter_errs!(iter, $lexer, $( $errs ),*);
                }
            }
        };
    }

    /// Expect token checks that the next token is the one that you pass as an argument, so should succeed if given the right token
    #[test]
    fn expect_token_should_ok_if_correct_token_given() {
        let lexer = tokens!(CloseBrace);
        expect_token(lexer, Token::CloseBrace).unwrap();
    }

    #[test]
    fn expect_token_should_err_if_wrong_token_given() {
        let lexer = tokens!(NotEquals);
        assert_errs!(
            expect_token(lexer, Token::CloseBrace),
            lexer,
            (
                SyntaxErrorKind::ExpectedOneOf(vec![Token::CloseBrace]),
                0,
                0
            )
        )
    }

    #[test]
    fn parse_binary_operator_should_return_correct_operator() {
        // TODO: Use a phf_map here instead?
        assert_eq!(
            BinaryOperator::Add,
            parse_binary_operator(tokens!(Add)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Subtract,
            parse_binary_operator(tokens!(Subtract)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Multiply,
            parse_binary_operator(tokens!(Multiply)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Divide,
            parse_binary_operator(tokens!(Divide)).unwrap()
        );
        assert_eq!(
            BinaryOperator::And,
            parse_binary_operator(tokens!(And)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Or,
            parse_binary_operator(tokens!(Or)).unwrap()
        );
        assert_eq!(
            BinaryOperator::LessThan,
            parse_binary_operator(tokens!(LessThan)).unwrap()
        );
        assert_eq!(
            BinaryOperator::GreaterThan,
            parse_binary_operator(tokens!(GreaterThan)).unwrap()
        );
        assert_eq!(
            BinaryOperator::LessThanOrEquals,
            parse_binary_operator(tokens!(LessThanOrEquals)).unwrap()
        );
        assert_eq!(
            BinaryOperator::GreaterThanOrEquals,
            parse_binary_operator(tokens!(GreaterThanOrEquals)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Equals,
            parse_binary_operator(tokens!(Equals)).unwrap()
        );
        assert_eq!(
            BinaryOperator::NotEquals,
            parse_binary_operator(tokens!(NotEquals)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Power,
            parse_binary_operator(tokens!(Power)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Quotient,
            parse_binary_operator(tokens!(Quotient)).unwrap()
        );
        assert_eq!(
            BinaryOperator::Remainder,
            parse_binary_operator(tokens!(Remainder)).unwrap()
        );
    }

    #[test]
    fn parse_binary_operator_should_err_upon_invalid_operator() {
        let lexer = tokens!(Not);
        assert_errs!(
            parse_binary_operator(lexer), // An identifier cannot be parsed as a binary operator
            lexer,
            (SyntaxErrorKind::ExpectedBinaryOperator, 0, 0)
        )
    }

    #[test]
    fn parse_unary_operator_should_return_correct_operator() {
        assert_eq!(
            UnaryOperator::Not,
            parse_unary_operator(tokens!(Not)).unwrap()
        );
    }

    #[test]
    fn parse_unary_operator_should_err_upon_invalid_operator() {
        let lexer = tokens!(NotEquals); // != is a binary operator, not a unary operator
        assert_errs!(
            parse_unary_operator(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedUnaryOperator, 0, 0)
        )
    }

    #[test]
    fn parse_identifier_should_return_correct_identifier() {
        let lexer = tokens!(Identifier("exampleident"));
        assert_eq!("exampleident", parse_identifier(lexer).unwrap())
    }

    #[test]
    fn parse_identifier_should_err_on_wrong_token() {
        let lexer = tokens!(NotEquals);
        assert_errs!(
            parse_identifier(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedIdentifier, 0, 0)
        )
    }

    #[test]
    fn parse_unary_expression_should_return_correct_literal() {
        // Check all literal types
        assert_eq!(
            Expression::IntegerLiteral(5),
            parse_unary_expression(tokens!(IntegerLiteral(5))).unwrap()
        );
        assert_eq!(
            Expression::RealLiteral(5.5),
            parse_unary_expression(tokens!(RealLiteral(5.5))).unwrap()
        );
        assert_eq!(
            Expression::BooleanLiteral(true),
            parse_unary_expression(tokens!(BooleanLiteral(true))).unwrap()
        );
        assert_eq!(
            Expression::BooleanLiteral(false),
            parse_unary_expression(tokens!(BooleanLiteral(false))).unwrap()
        );
        assert_eq!(
            Expression::StringLiteral("Hello World".to_string()),
            parse_unary_expression(tokens!(StringLiteral("Hello World"))).unwrap()
        );
    }

    #[test]
    fn parse_unary_expression_should_apply_unary_operators() {
        let lexer = tokens!(Not, BooleanLiteral(true));

        assert_eq!(
            Expression::Unary {
                operand: Box::new(Expression::BooleanLiteral(true)),
                operator: UnaryOperator::Not
            },
            parse_unary_expression(lexer).unwrap()
        );
    }

    #[test]
    fn parse_unary_expression_should_return_correct_variable_expression() {
        let lexer = tokens!(Identifier("myVariable"));
        assert_eq!(
            Expression::Assignable(Assignable::Variable("myVariable".to_string())),
            parse_unary_expression(lexer).unwrap()
        )
    }

    #[test]
    fn parse_unary_expression_should_return_correct_property_expression() {
        let lexer = tokens!(Identifier("variable"), Period, Identifier("example"));

        assert_eq!(
            Expression::Assignable(Assignable::Property {
                value: Box::new(Expression::Assignable(Assignable::Variable(
                    "variable".to_string()
                ))),
                name: "example".to_string()
            }),
            parse_unary_expression(lexer).unwrap()
        );
    }

    /// `ExpectedExpression` is used here instead of `ExpectedOneOf` with all possible tokens listed, since
    /// it makes it clearer what code the user could write to fix the issue.
    #[test]
    fn parse_unary_expression_should_return_expected_expression_if_first_token_invalid() {
        let lexer = tokens!(LessThanOrEquals, IntegerLiteral(2));
        assert_errs!(
            parse_unary_expression(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedExpression, 0, 0)
        );
    }

    /// A period in a unary expression indicates that we are getting a property value
    /// The property name should be supplied as an identifier
    #[test]
    fn parse_unary_expression_should_return_expected_identifier_if_no_identifier_after_period() {
        let lexer = tokens!(Identifier("test"), Period, LessThanOrEquals);
        assert_errs!(
            parse_unary_expression(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedIdentifier, 2, 2)
        );
    }

    /// A `[` token in a unary expression should cause an array literal to be parsed
    #[test]
    fn parse_unary_expression_should_return_correct_array_literal() {
        let lexer = tokens!(
            OpenSquareBrace,
            IntegerLiteral(4),
            Comma,
            RealLiteral(5.5),
            CloseSquareBrace
        );
        assert_eq!(
            Expression::ArrayLiteral(vec![
                Expression::IntegerLiteral(4),
                Expression::RealLiteral(5.5)
            ]),
            parse_unary_expression(lexer).unwrap()
        )
    }

    /// A `(` token in a unary expression should cause a call to be parsed
    #[test]
    fn parse_unary_expression_should_return_correct_call() {
        let lexer = tokens!(
            Identifier("test"),
            OpenBrace,
            IntegerLiteral(3),
            Comma,
            RealLiteral(4.5),
            CloseBrace
        );
        assert_eq!(
            Expression::Call(Call {
                callee: Box::new(Callee::SubProgram("test".to_string())),
                args: vec![Expression::IntegerLiteral(3), Expression::RealLiteral(4.5)]
            }),
            parse_unary_expression(lexer).unwrap()
        )
    }

    /// Calling a property assignable expression should lead to `Callee::Member` being returned.
    #[test]
    fn parse_unary_expression_should_return_correct_property_call() {
        let lexer = tokens!(
            StringLiteral("Test"),
            Period,
            Identifier("substring"),
            OpenBrace,
            IntegerLiteral(3),
            Comma,
            IntegerLiteral(4),
            CloseBrace
        );
        assert_eq!(
            Expression::Call(Call {
                callee: Box::new(Callee::Member {
                    object: Expression::StringLiteral("Test".to_string()),
                    member: "substring".to_string()
                }),
                args: vec![Expression::IntegerLiteral(3), Expression::IntegerLiteral(4)]
            }),
            parse_unary_expression(lexer).unwrap()
        )
    }

    /// Currently, storing functions as variables is unsupported (since it is not specified by OCR)
    /// Thus, calling an expression that isn't a property value or identifier (function name) should fail.
    #[test]
    fn parse_unary_expression_should_return_cannot_call_if_callee_not_property_or_variable() {
        let lexer = tokens!(
            Identifier("jazz"),
            OpenSquareBrace,
            IntegerLiteral(5),
            CloseSquareBrace,
            OpenBrace,
            CloseBrace
        );
        assert_errs!(
            parse_unary_expression(lexer),
            lexer,
            (SyntaxErrorKind::CannotCall, 0, 3)
        );
    }

    #[test]
    fn parse_unary_expression_should_return_correct_array_index_expression() {
        let lexer = tokens!(
            Identifier("test"),
            OpenSquareBrace,
            IntegerLiteral(5),
            Comma,
            IntegerLiteral(4),
            CloseSquareBrace
        );
        assert_eq!(
            Expression::Assignable(Assignable::Index {
                to_index: Box::new(Expression::Assignable(Assignable::Variable(
                    "test".to_string()
                ))),
                indices: vec![Expression::IntegerLiteral(5), Expression::IntegerLiteral(4)]
            }),
            parse_unary_expression(lexer).unwrap()
        )
    }

    /// Unary expressions starting with `(` should trigger the inner expression to parsed as a binary expression
    #[test]
    fn parse_unary_expression_should_parse_expressions_within_brackets() {
        let lexer = tokens!(
            OpenBrace,
            IntegerLiteral(5),
            Add,
            IntegerLiteral(6),
            CloseBrace
        );
        assert_eq!(
            Expression::Binary {
                operator: BinaryOperator::Add,
                left: Box::new(Expression::IntegerLiteral(5)),
                right: Box::new(Expression::IntegerLiteral(6))
            },
            parse_unary_expression(lexer).unwrap()
        )
    }

    /// A bracketed expression requires a close bracket `)` to be valid.
    #[test]
    fn parse_unary_expression_should_return_expected_close_brace_if_no_close_brace_for_expression_within_brackets(
    ) {
        let lexer = tokens!(OpenBrace, BooleanLiteral(true));
        assert_errs!(
            parse_unary_expression(lexer),
            lexer,
            (
                SyntaxErrorKind::ExpectedOneOf(vec![Token::CloseBrace]),
                2,
                2
            )
        )
    }

    /// Binary expressions should be parsed in the given order.
    /// TODO: Operator precedence
    #[test]
    fn parse_expression_should_parse_binary_expressions_in_order() {
        let lexer = tokens!(
            IntegerLiteral(5),
            Add,
            IntegerLiteral(4),
            Add,
            IntegerLiteral(3)
        );
        assert_eq!(
            Expression::Binary {
                operator: BinaryOperator::Add,
                left: Box::new(Expression::Binary {
                    operator: BinaryOperator::Add,
                    left: Box::new(Expression::IntegerLiteral(5)),
                    right: Box::new(Expression::IntegerLiteral(4))
                }),
                right: Box::new(Expression::IntegerLiteral(3))
            },
            parse_expression(lexer).unwrap()
        )
    }

    /// Parsing an expression list should return the expressions within the list
    #[test]
    fn parse_expression_list_should_return_correct_expressions_within_list() {
        let lexer = tokens!(IntegerLiteral(5), Comma, RealLiteral(4.5), CloseSquareBrace);
        assert_eq!(
            vec![Expression::IntegerLiteral(5), Expression::RealLiteral(4.5)],
            // No `[` is given here since `parse_expression_list` assumes that this has already been parsed.
            parse_expression_list(lexer, Token::CloseSquareBrace).unwrap()
        );
    }

    /// This test exists to avoid a past regression where `parse_expression_list` fails on empty list.
    #[test]
    fn parse_expression_list_should_return_blank_vec_for_empty_lists() {
        let lexer = tokens!(CloseSquareBrace);
        assert_eq!(
            Vec::<Expression>::new(),
            parse_expression_list(lexer, Token::CloseSquareBrace).unwrap()
        );
    }

    /// Expression lists must end with the ending token passed an argument. e.g. an array literal should end with `]` not `)`
    #[test]
    fn parse_expression_list_should_err_if_wrong_ending_token() {
        let lexer = tokens!(IntegerLiteral(5), Comma, RealLiteral(4.5), CloseBrace);
        assert_errs!(
            parse_expression_list(lexer, Token::CloseSquareBrace),
            lexer,
            (
                SyntaxErrorKind::ExpectedOneOf(vec![Token::Comma, Token::CloseSquareBrace]),
                3,
                3
            )
        )
    }

    /// A function call is the only expression type that is valid as a statement (since it is the only one that we have seen OCR use),
    /// TODO: Discuss whether other expressions should be valid statements since an expression such as `myFunctionCausingSideEffects() + 5` would lead to a side effect
    #[test]
    fn parse_statement_should_allow_call_expressions_as_statements() {
        let lexer = tokens!(Identifier("test"), OpenBrace, CloseBrace, EndOfLine);
        assert_eq!(
            Statement::Call(Call {
                callee: Box::new(Callee::SubProgram("test".to_string())),
                args: vec![]
            }),
            parse_statement(lexer).unwrap()
        );
    }

    /// After calls, the next statement should begin, thus an end of line is needed
    #[test]
    fn parse_statement_should_err_if_no_end_of_line_after_call() {
        let lexer = tokens!(
            Identifier("test"),
            OpenBrace,
            CloseBrace,
            Identifier("test")
        );
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 3, 3)
        )
    }

    /// Verifies that parsing an assignment correctly identifies all the modifier tokens given.
    /// This also checks that the other details of an assignment are parsed correctly for a variable assignment.
    #[test]
    fn parse_statement_should_return_assignment_with_correct_modifiers() {
        // Contains all possible modifier combinations
        const MODIFIER_SETS: [[bool; 3]; 8] = [
            [false, false, false],
            [false, false, true],
            [false, true, false],
            [false, true, true],
            [true, false, false],
            [true, false, true],
            [true, true, false],
            [true, true, true],
        ];

        for set in MODIFIER_SETS {
            let mut tokens = Vec::new();
            let (is_const, is_global, is_array) = (set[0], set[1], set[2]);
            if is_const {
                tokens.push(Token::Const);
            }
            if is_global {
                tokens.push(Token::Global);
            }
            if is_array {
                tokens.push(Token::Array);
            }
            tokens.push(Token::Identifier("test".to_string()));
            tokens.push(Token::Assign);
            tokens.push(Token::IntegerLiteral(5));
            tokens.push(Token::EndOfLine);
            assert_eq!(
                Statement::Assign {
                    is_const: is_const,
                    is_global: is_global,
                    is_array: is_array,
                    to_assign: Assignable::Variable("test".to_string()),
                    assign_with: AssignmentValue::Expression(Expression::IntegerLiteral(5))
                },
                parse_statement(&mut TestLexer::new(tokens)).unwrap()
            );
        }
    }

    /// Empty arrays can be defined in ERL as `array myArray[5]`, so we will check that these are parsed correctly.
    #[test]
    fn parse_statement_should_return_correct_empty_array_declaration() {
        let lexer = tokens!(
            Array,
            Identifier("test"),
            OpenSquareBrace,
            IntegerLiteral(5),
            Comma,
            IntegerLiteral(4),
            CloseSquareBrace,
            EndOfLine
        );
        assert_eq!(
            Statement::Assign {
                is_const: false,
                is_global: false,
                is_array: true,
                to_assign: Assignable::Variable("test".to_string()),
                assign_with: AssignmentValue::BlankArray(vec![
                    Expression::IntegerLiteral(5),
                    Expression::IntegerLiteral(4)
                ])
            },
            parse_statement(lexer).unwrap()
        );
    }

    /// After an assignment, there should be a different statement, and thus a new line
    #[test]
    fn parse_statement_should_err_if_no_end_of_line_after_assignment() {
        let lexer = tokens!(
            Identifier("test"),
            Assign,
            IntegerLiteral(5),
            Identifier("test")
        );
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 3, 3)
        )
    }

    /// Assignable expressions aren't valid statements on their own, and must be
    /// part of an assignment. If attempting to use one as a statement, we must provide the correct error kind
    /// that will report to the programmer that assigning to their expression with `=` would make a valid statement.
    #[test]
    fn parse_statement_should_suggest_assignment_if_parsed_value_assignable() {
        let lexer = tokens!(Identifier("test"), Period, Identifier("length"), EndOfLine);
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (
                SyntaxErrorKind::CannotUseAssignableExpressionAsStatement,
                0,
                2
            )
        )
    }

    /// Expressions cannot be used as statements. See `parse_statement_should_allow_call_expressions_as_statements` for notes about this.
    #[test]
    fn parse_statement_should_err_if_using_expression_as_statement() {
        let lexer = tokens!(IntegerLiteral(5), Add, IntegerLiteral(5), EndOfLine);
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::CannotUseExpressionAsStatement, 0, 2)
        )
    }

    /// If an assignment related keyword, (`global`, `const` or `array`) has already been provided as part of a statement,
    /// then we know that the statement is "supposed" to be an assignment. That means that if the given expression is assignable,
    /// then we should expect an `=` after it, since an assignment is almost certainly the intent.
    #[test]
    fn parse_statement_should_expect_assignment_if_assignment_related_keyword_supplied_and_expression_is_assignable(
    ) {
        let lexer = tokens!(Global, Identifier("test"), EndOfLine);
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::Assign]), 2, 2)
        )
    }

    /// If the given expression is callable, but assignment related keywords are supplied, the simplest way
    /// to make the statement valid is to remove these keywords, so this is the error we give.
    #[test]
    fn parse_statement_should_return_unexpected_keywords_if_assignment_related_keyword_supplied_and_expression_is_not_assignable(
    ) {
        let lexer = tokens!(
            Global,
            Const,
            Identifier("test"),
            OpenBrace,
            CloseBrace,
            EndOfLine
        );
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (
                SyntaxErrorKind::UnexpectedKeyWords(vec![Token::Global, Token::Const]),
                0,
                1
            )
        )
    }

    #[test]
    fn parse_statement_should_return_correct_return_value() {
        let lexer = tokens!(Return, IntegerLiteral(5), EndOfLine);
        assert_eq!(
            Statement::Return {
                value: Some(Expression::IntegerLiteral(5))
            },
            parse_statement(lexer).unwrap()
        );
    }

    #[test]
    fn parse_statement_should_return_return() {
        let lexer = tokens!(Return, EndOfLine);
        assert_eq!(
            Statement::Return { value: None }, // None indicates no return value
            parse_statement(lexer).unwrap()
        );
    }

    /// After a `return` statement another statement is expected, so we will error if no end of line is found.
    #[test]
    fn parse_statement_should_err_if_no_end_of_line_after_return() {
        let lexer = tokens!(Return, IntegerLiteral(5), Identifier("test"));
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 2, 2)
        )
    }

    /// It would be very difficult to list all the valid tokens that could begin a statement,
    /// and this would also probably just confuse the programmer more, so we give `SyntaxErrorKind::ExpectedStatement`,
    /// to indicate that a valid statement is needed. The error itself should give information about what the programmer
    /// can use as a statement.
    ///
    /// TODO: This test is disabled due to an issue with resolving ambiguity between expected expression within an inner expression and an outer expression
    /*
    #[test]
    fn parse_statement_should_return_expected_statement_if_no_valid_expression_or_keyword() {
        let lexer = tokens!(NotEquals, IntegerLiteral(5), EndOfLine);
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedStatement, 0, 1)
        )
    }*/

    /// Makes sure that all details of the `for` loop are correctly parsed
    #[test]
    fn parse_statement_should_return_correct_for_loop() {
        let lexer = tokens!(
            For,
            Identifier("i"),
            Assign,
            IntegerLiteral(0),
            To,
            IntegerLiteral(10),
            Step,
            IntegerLiteral(2),
            EndOfLine,
            Next,
            Identifier("i"),
            EndOfLine
        );

        assert_eq!(
            Statement::For {
                start: Expression::IntegerLiteral(0),
                end: Expression::IntegerLiteral(10),
                step: Some(Expression::IntegerLiteral(2)),
                variable_name: "i".to_string(),
                block: vec![]
            },
            parse_statement(lexer).unwrap()
        )
    }

    /// `step` expressions are optional in for loops
    #[test]
    fn parse_statement_should_allow_for_loop_without_step() {
        let lexer = tokens!(
            For,
            Identifier("i"),
            Assign,
            IntegerLiteral(0),
            To,
            IntegerLiteral(10),
            EndOfLine,
            Next,
            Identifier("i"),
            EndOfLine
        );

        assert_eq!(
            Statement::For {
                start: Expression::IntegerLiteral(0),
                end: Expression::IntegerLiteral(10),
                step: None,
                variable_name: "i".to_string(),
                block: vec![]
            },
            parse_statement(lexer).unwrap()
        )
    }

    /// An identifier is needed to give the variable to update each iteration
    #[test]
    fn parse_statement_should_expect_identifier_after_for() {
        let lexer = tokens!(For, LessThan);
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedIdentifier, 1, 1)
        )
    }

    /// The identifier then needs to be assigned a lower bound.
    #[test]
    fn parse_statement_should_expect_assign_after_identifier_of_for() {
        let lexer = tokens!(For, Identifier("i"), Equals);
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::Assign]), 2, 2)
        )
    }

    /// A `to` keyword is then used to separate the lower bound and upper bound.
    #[test]
    fn parse_statement_should_expect_to_after_lower_bound_of_for() {
        let lexer = tokens!(
            For,
            Identifier("i"),
            Assign,
            IntegerLiteral(0),
            Identifier("invalid")
        );
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::To]), 4, 4)
        )
    }

    /// Since `step` expressions are optional, after the upper bound of the for loop, both a new line or a `step` keyword are valid tokens.
    #[test]
    fn parse_statement_should_expect_end_of_line_or_step_after_upper_bound_of_for() {
        let lexer = tokens!(
            For,
            Identifier("i"),
            Assign,
            IntegerLiteral(0),
            To,
            IntegerLiteral(10),
            Identifier("invalid")
        );
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (
                SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine, Token::Step]),
                6,
                6
            )
        )
    }

    /// After the step expression, a new line is required before the first statement in the for loop
    #[test]
    fn parse_statement_should_expect_end_of_line_after_step_expr() {
        let lexer = tokens!(
            For,
            Identifier("i"),
            Assign,
            IntegerLiteral(0),
            To,
            IntegerLiteral(10),
            Step,
            IntegerLiteral(5),
            Identifier("invalid")
        );
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 8, 8)
        )
    }

    #[test]
    fn parse_statement_should_expect_correct_next_variable_of_for() {
        let lexer = tokens!(
            For,
            Identifier("i"),
            Assign,
            IntegerLiteral(0),
            To,
            IntegerLiteral(10),
            EndOfLine,
            Next,
            Identifier("j")
        );

        assert_errs!(
            parse_statement(lexer),
            lexer,
            (
                SyntaxErrorKind::ExpectedOneOf(vec![Token::Identifier("i".to_string())]),
                8,
                8
            )
        )
    }

    #[test]
    fn parse_statement_should_return_correct_while_loop() {
        let lexer = tokens!(
            While,
            IntegerLiteral(5),
            LessThan,
            IntegerLiteral(6),
            EndOfLine,
            EndWhile,
            EndOfLine
        );

        assert_eq!(
            Statement::While {
                condition: Expression::Binary {
                    operator: BinaryOperator::LessThan,
                    left: Box::new(Expression::IntegerLiteral(5)),
                    right: Box::new(Expression::IntegerLiteral(6)),
                },
                block: vec![]
            },
            parse_statement(lexer).unwrap()
        )
    }

    #[test]
    fn parse_statement_should_expect_end_of_line_after_while_condition() {
        let lexer = tokens!(While, BooleanLiteral(true), Identifier("invalid"));
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 2, 2)
        )
    }

    #[test]
    fn parse_statement_should_return_correct_if_statement_with_if_and_elseif() {
        let lexer = tokens!(
            If,
            IntegerLiteral(6),
            GreaterThan,
            IntegerLiteral(5),
            Then,
            EndOfLine,
            ElseIf,
            IntegerLiteral(7),
            GreaterThan,
            IntegerLiteral(6),
            Then,
            EndOfLine,
            Else,
            EndOfLine,
            EndIf,
            EndOfLine
        );

        assert_eq!(
            Statement::If {
                segments: vec![
                    IfSegment {
                        condition: Expression::Binary {
                            operator: BinaryOperator::GreaterThan,
                            left: Box::new(Expression::IntegerLiteral(6)),
                            right: Box::new(Expression::IntegerLiteral(5))
                        },
                        block: vec![]
                    },
                    IfSegment {
                        condition: Expression::Binary {
                            operator: BinaryOperator::GreaterThan,
                            left: Box::new(Expression::IntegerLiteral(7)),
                            right: Box::new(Expression::IntegerLiteral(6))
                        },
                        block: vec![]
                    },
                ],
                else_block: Some(vec![])
            },
            parse_statement(lexer).unwrap()
        )
    }

    #[test]
    fn parse_statement_should_allow_if_without_elseif() {
        let lexer = tokens!(
            If,
            IntegerLiteral(6),
            GreaterThan,
            IntegerLiteral(5),
            Then,
            EndOfLine,
            Else,
            EndOfLine,
            EndIf,
            EndOfLine
        );

        assert_eq!(
            Statement::If {
                segments: vec![IfSegment {
                    condition: Expression::Binary {
                        operator: BinaryOperator::GreaterThan,
                        left: Box::new(Expression::IntegerLiteral(6)),
                        right: Box::new(Expression::IntegerLiteral(5))
                    },
                    block: vec![]
                }],
                else_block: Some(vec![])
            },
            parse_statement(lexer).unwrap()
        );
    }

    #[test]
    fn parse_statement_should_allow_if_without_else() {
        let lexer = tokens!(
            If,
            IntegerLiteral(6),
            GreaterThan,
            IntegerLiteral(5),
            Then,
            EndOfLine,
            EndIf,
            EndOfLine
        );

        assert_eq!(
            Statement::If {
                segments: vec![IfSegment {
                    condition: Expression::Binary {
                        operator: BinaryOperator::GreaterThan,
                        left: Box::new(Expression::IntegerLiteral(6)),
                        right: Box::new(Expression::IntegerLiteral(5))
                    },
                    block: vec![]
                }],
                else_block: None
            },
            parse_statement(lexer).unwrap()
        );
    }

    #[test]
    fn parse_statement_should_expect_then_and_end_of_line_after_if_expr() {
        let lexer = tokens!(If, BooleanLiteral(true), Identifier("invalid"));

        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::Then]), 2, 2)
        );

        let lexer = tokens!(If, BooleanLiteral(true), Then, Identifier("invalid"));
        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 3, 3)
        );
    }

    #[test]
    fn parse_statement_should_expect_then_and_end_of_line_after_elseif_expr() {
        let lexer = tokens!(
            If,
            BooleanLiteral(true),
            Then,
            EndOfLine,
            ElseIf,
            BooleanLiteral(true),
            Identifier("invalid")
        );

        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::Then]), 6, 6)
        );

        let lexer = tokens!(
            If,
            BooleanLiteral(true),
            Then,
            EndOfLine,
            ElseIf,
            BooleanLiteral(true),
            Then,
            Identifier("invalid")
        );

        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 7, 7)
        );
    }

    #[test]
    fn parse_statement_should_expect_end_of_line_after_else() {
        let lexer = tokens!(
            If,
            BooleanLiteral(true),
            Then,
            EndOfLine,
            Else,
            Identifier("invalid")
        );

        assert_errs!(
            parse_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 5, 5)
        )
    }

    #[test]
    fn parse_block_should_parse_multiple_statements_within_block() {
        let lexer = tokens!(
            Identifier("example"),
            Assign,
            IntegerLiteral(5),
            EndOfLine,
            Identifier("another_example"),
            Assign,
            IntegerLiteral(6),
            EndOfLine,
            EndIf
        );
        assert_eq!(
            (
                vec![
                    Statement::Assign {
                        is_const: false,
                        is_global: false,
                        is_array: false,
                        to_assign: Assignable::Variable("example".to_string()),
                        assign_with: AssignmentValue::Expression(Expression::IntegerLiteral(5))
                    },
                    Statement::Assign {
                        is_const: false,
                        is_global: false,
                        is_array: false,
                        to_assign: Assignable::Variable("another_example".to_string()),
                        assign_with: AssignmentValue::Expression(Expression::IntegerLiteral(6))
                    },
                ],
                Token::EndIf
            ),
            parse_block(lexer, vec![Token::EndIf]).unwrap()
        )
    }

    #[test]
    fn parse_block_should_accept_all_given_ending_tokens() {
        let with_endif = tokens!(EndIf);
        let with_else = tokens!(Else);
        assert_eq!(
            (vec![], Token::EndIf),
            parse_block(with_endif, vec![Token::EndIf, Token::Else]).unwrap()
        );
        assert_eq!(
            (vec![], Token::Else),
            parse_block(with_else, vec![Token::EndIf, Token::Else]).unwrap()
        );
    }

    #[test]
    fn parse_block_should_err_if_eof_within_block() {
        let lexer = tokens!(EndOfFile);
        assert_errs!(
            parse_block(lexer, vec![Token::EndIf, Token::Else]),
            lexer,
            (
                SyntaxErrorKind::ExpectedOneOf(vec![Token::EndIf, Token::Else]),
                0,
                0
            )
        )
    }

    #[test]
    fn parse_root_statement_should_return_correct_function() {
        let lexer = tokens!(
            Function,
            Identifier("example"),
            OpenBrace,
            Identifier("arg1"),
            Comma,
            Identifier("arg2"),
            CloseBrace,
            EndOfLine,
            EndFunction,
            EndOfLine
        );

        assert_eq!(
            RootStatement::SubProgram {
                name: "example".to_string(),
                block: vec![],
                argument_names: vec!["arg1".to_string(), "arg2".to_string()],
                is_function: true
            },
            parse_root_statement(lexer).unwrap()
        )
    }

    #[test]
    fn parse_root_statement_should_return_correct_procedure() {
        let lexer = tokens!(
            Procedure,
            Identifier("example"),
            OpenBrace,
            Identifier("arg1"),
            Comma,
            Identifier("arg2"),
            CloseBrace,
            EndOfLine,
            EndProcedure,
            EndOfLine
        );

        assert_eq!(
            RootStatement::SubProgram {
                name: "example".to_string(),
                block: vec![],
                argument_names: vec!["arg1".to_string(), "arg2".to_string()],
                is_function: false
            },
            parse_root_statement(lexer).unwrap()
        )
    }

    #[test]
    fn parse_root_statement_should_expect_end_of_line_after_sub_program_definition() {
        let lexer = tokens!(
            Procedure,
            Identifier("example"),
            OpenBrace,
            CloseBrace,
            Identifier("invalid")
        );

        assert_errs!(
            parse_root_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine]), 4, 4)
        )
    }

    #[test]
    fn parse_root_statement_should_expect_sub_program_name() {
        let lexer = tokens!(Procedure, NotEquals);

        assert_errs!(
            parse_root_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedIdentifier, 1, 1)
        )
    }

    #[test]
    fn parse_root_statement_should_expect_open_brace_after_sub_program_name() {
        let lexer = tokens!(Procedure, Identifier("example"), Identifier("invalid"));

        assert_errs!(
            parse_root_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedOneOf(vec![Token::OpenBrace]), 2, 2)
        )
    }

    #[test]
    fn parse_root_statement_should_expect_identifier_for_first_param_of_sub_program() {
        let lexer = tokens!(Procedure, Identifier("example"), OpenBrace, NotEquals);

        assert_errs!(
            parse_root_statement(lexer),
            lexer,
            (SyntaxErrorKind::ExpectedIdentifier, 3, 3)
        )
    }

    #[test]
    fn parse_root_statement_should_expect_comma_or_close_brace_after_param_of_sub_program() {
        let lexer = tokens!(
            Procedure,
            Identifier("example"),
            OpenBrace,
            Identifier("arg1"),
            Identifier("invalid")
        );

        assert_errs!(
            parse_root_statement(lexer),
            lexer,
            (
                SyntaxErrorKind::ExpectedOneOf(vec![Token::Comma, Token::CloseBrace]),
                4,
                4
            )
        )
    }

    #[test]
    fn parse_root_statement_should_allow_sub_program_with_no_args() {
        let lexer = tokens!(
            Procedure,
            Identifier("example"),
            OpenBrace,
            CloseBrace,
            EndOfLine,
            EndProcedure,
            EndOfLine
        );

        assert_eq!(
            RootStatement::SubProgram {
                name: "example".to_string(),
                block: vec![],
                argument_names: vec![],
                is_function: false
            },
            parse_root_statement(lexer).unwrap()
        )
    }

    #[test]
    fn parse_root_statement_should_allow_ordinary_statements() {
        let lexer = tokens!(Identifier("i"), Assign, IntegerLiteral(6), EndOfLine);

        assert_eq!(
            RootStatement::Statement(Statement::Assign {
                is_const: false,
                is_global: false,
                is_array: false,
                to_assign: Assignable::Variable("i".to_string()),
                assign_with: AssignmentValue::Expression(Expression::IntegerLiteral(6))
            }),
            parse_root_statement(lexer).unwrap()
        )
    }

    #[test]
    fn parse_root_block_should_parse_root_statements_in_block() {
        let lexer = tokens!(
            Procedure,
            Identifier("example"),
            OpenBrace,
            CloseBrace,
            EndOfLine,
            EndProcedure,
            EndOfLine,
            Identifier("i"),
            Assign,
            IntegerLiteral(6),
            EndOfLine
        );

        assert_eq!(
            vec![
                RootStatement::SubProgram {
                    name: "example".to_string(),
                    block: vec![],
                    argument_names: vec![],
                    is_function: false
                },
                RootStatement::Statement(Statement::Assign {
                    is_const: false,
                    is_global: false,
                    is_array: false,
                    to_assign: Assignable::Variable("i".to_string()),
                    assign_with: AssignmentValue::Expression(Expression::IntegerLiteral(6))
                })
            ],
            parse_root_block(lexer).unwrap()
        )
    }
}

/// Result type for ERL syntax error handling.
/// A [Vec] of [SyntaxError] is used, since parsing some statements can result in up to one error per line.
pub type Result<T> = std::result::Result<T, Vec<SyntaxError>>;

fn parse_rh_of_assignment(
    lexer: &mut impl Lexer,
    is_global: bool,
    is_array: bool,
    is_const: bool,
    left: Assignable,
) -> Result<Statement> {
    let right = AssignmentValue::Expression(parse_expression(lexer)?);
    expect_token(lexer, Token::EndOfLine)?;

    Ok(Statement::Assign {
        is_const,
        is_global,
        is_array,
        to_assign: left,
        assign_with: right,
    })
}

fn parse_while_loop(lexer: &mut impl Lexer) -> Result<Statement> {
    let condition = parse_expression(lexer)?;
    expect_token(lexer, Token::EndOfLine)?;

    let (block, _) = parse_block(lexer, vec![Token::EndWhile])?;
    expect_token(lexer, Token::EndOfLine)?;

    Ok(Statement::While { condition, block })
}

fn parse_for_loop(lexer: &mut impl Lexer) -> Result<Statement> {
    let variable_name = parse_identifier(lexer)?;
    expect_token(lexer, Token::Assign)?;

    let lower_bound = parse_expression(lexer)?;
    expect_token(lexer, Token::To)?;
    let upper_bound = parse_expression(lexer)?;

    let step_err_start = lexer.at_next_token();
    let step = match lexer.consume_token()? {
        Token::EndOfLine => None,
        Token::Step => {
            let step = parse_expression(lexer)?;
            expect_token(lexer, Token::EndOfLine)?;
            Some(step)
        }
        _ => {
            return Err(SyntaxError::new_single(
                step_err_start,
                lexer.at_last_token(),
                SyntaxErrorKind::ExpectedOneOf(vec![Token::EndOfLine, Token::Step]),
            ))
        }
    };

    let (block, _) = parse_block(lexer, vec![Token::Next])?;

    let identifier_err_start = lexer.at_next_token();
    if parse_identifier(lexer)? != variable_name {
        return Err(SyntaxError::new_single(
            identifier_err_start,
            lexer.at_last_token(),
            SyntaxErrorKind::ExpectedOneOf(vec![Token::Identifier(variable_name.to_string())]),
        ));
    }

    expect_token(lexer, Token::EndOfLine)?;

    Ok(Statement::For {
        start: lower_bound,
        end: upper_bound,
        step: step,
        variable_name: variable_name,
        block: block,
    })
}

fn parse_if_segment_condition(lexer: &mut impl Lexer) -> Result<Expression> {
    let condition = parse_expression(lexer)?;
    expect_token(lexer, Token::Then)?;
    expect_token(lexer, Token::EndOfLine)?;

    Ok(condition)
}

fn parse_if_statement(lexer: &mut impl Lexer) -> Result<Statement> {
    let mut segments = Vec::new();
    let else_block = loop {
        let condition = parse_if_segment_condition(lexer)?;
        lexer.skip_to_newline();

        let (block, ending_token) =
            parse_block(lexer, vec![Token::Else, Token::ElseIf, Token::EndIf])?;

        segments.push(IfSegment { condition, block });

        match ending_token {
            Token::Else => {
                expect_token(lexer, Token::EndOfLine)?;
                let (else_block, _) = parse_block(lexer, vec![Token::EndIf])?;
                break Some(else_block);
            }
            Token::EndIf => break None,
            _ => continue,
        }
    };

    expect_token(lexer, Token::EndOfLine)?;

    Ok(Statement::If {
        segments,
        else_block,
    })
}

/// Parses the statements within the root of the file (either sub-programs or [Statement]s).
///
/// Returns `Ok` with the list of statements if all parsed successfully, or
/// `Err` with a [Vec] of all of the errors that occured if one or more statements failed to parse.
///
/// # Arguments
/// * `lexer` - the lexer to parse the tokens from.
///
/// # Examples
/// ```
///
/// let beginning = erl_parser::File::from_string("example = 5".to_owned()).beginning();
/// let mut lexer = erl_parser::FileLexer::new(beginning);
///
/// let ast = erl_parser::parse_root_block(&mut lexer).unwrap();
/// ```
pub fn parse_root_block(lexer: &mut impl Lexer) -> Result<Vec<RootStatement>> {
    let mut result = Vec::new();
    let mut errors = Vec::new();

    loop {
        match lexer.peek_token()? {
            Token::EndOfLine => {
                lexer.consume_token()?;
                continue;
            }
            Token::EndOfFile => {
                return if errors.len() > 0 {
                    Err(errors)
                } else {
                    Ok(result)
                }
            }
            _ => {}
        }

        match parse_root_statement(lexer) {
            Ok(statement) => result.push(statement),
            Err(mut errs) => {
                lexer.skip_to_newline();
                errors.append(&mut errs)
            }
        }
    }
}

fn parse_sub_program(lexer: &mut impl Lexer, is_function: bool) -> Result<RootStatement> {
    let name = parse_identifier(lexer)?;
    expect_token(lexer, Token::OpenBrace)?;

    let argument_names = match lexer.peek_token()? {
        Token::CloseBrace => {
            lexer.consume_token()?;
            vec![]
        }
        _ => {
            let mut result = Vec::new();
            loop {
                result.push(parse_identifier(lexer)?);
                let expected_err_start = lexer.at_next_token();
                match lexer.consume_token()? {
                    Token::Comma => continue,
                    Token::CloseBrace => break,
                    _ => {
                        return Err(SyntaxError::new_single(
                            expected_err_start,
                            lexer.at_last_token(),
                            SyntaxErrorKind::ExpectedOneOf(vec![Token::Comma, Token::CloseBrace]),
                        ))
                    }
                }
            }

            result
        }
    };

    expect_token(lexer, Token::EndOfLine)?;
    let ending_token = if is_function {
        Token::EndFunction
    } else {
        Token::EndProcedure
    };
    let (block, _) = parse_block(lexer, vec![ending_token])?;

    expect_token(lexer, Token::EndOfLine)?;

    Ok(RootStatement::SubProgram {
        name,
        block,
        argument_names,
        is_function,
    })
}

fn parse_root_statement(lexer: &mut impl Lexer) -> Result<RootStatement> {
    match lexer.peek_token()? {
        Token::Function => {
            lexer.consume_token()?;
            return parse_sub_program(lexer, true);
        }
        Token::Procedure => {
            lexer.consume_token()?;
            return parse_sub_program(lexer, false);
        }
        _ => {}
    };

    Ok(RootStatement::Statement(parse_statement(lexer)?))
}

fn is_block_separator(token: Token) -> bool {
    match token {
        Token::EndIf => true,
        Token::EndFunction => true,
        Token::EndProcedure => true,
        Token::EndWhile => true,
        Token::Next => true,
        Token::ElseIf => true,
        Token::Else => true,
        Token::EndSwitch => true,
        Token::EndOfFile => true,
        _ => false,
    }
}

fn parse_block(
    lexer: &mut impl Lexer,
    ending_tokens: Vec<Token>,
) -> Result<(Vec<Statement>, Token)> {
    let mut result = Vec::new();
    let mut errors = Vec::new();
    let ending_token = loop {
        let eof_err_pos = lexer.at_next_token();

        let next_token = lexer.peek_token()?;
        if ending_tokens.contains(&next_token) {
            lexer.consume_token()?;
            break next_token;
        }
        if next_token == Token::EndOfLine {
            lexer.consume_token()?;
            continue;
        }
        if is_block_separator(next_token) {
            errors.push(SyntaxError::new(
                eof_err_pos.clone(),
                eof_err_pos,
                SyntaxErrorKind::ExpectedOneOf(ending_tokens),
            ));
            return Err(errors);
        }

        match parse_statement(lexer) {
            Ok(statement) => result.push(statement),
            Err(mut err) => {
                lexer.skip_to_newline();
                errors.append(&mut err);
            }
        }
    };

    if errors.len() > 0 {
        return Err(errors);
    } else {
        return Ok((result, ending_token));
    }
}

impl From<SyntaxError> for Vec<SyntaxError> {
    fn from(err: SyntaxError) -> Self {
        vec![err]
    }
}

fn parse_statement(lexer: &mut impl Lexer) -> Result<Statement> {
    match lexer.peek_token()? {
        Token::Return => {
            lexer.consume_token()?;
            let before_expr_parse = lexer.clone();
            let return_value = match parse_expression(lexer) {
                Ok(expr) => Some(expr),
                Err(_) => {
                    *lexer = before_expr_parse;
                    None
                }
            };

            expect_token(lexer, Token::EndOfLine)?;
            return Ok(Statement::Return {
                value: return_value,
            });
        }
        Token::For => {
            lexer.consume_token()?;
            return parse_for_loop(lexer);
        }
        Token::While => {
            lexer.consume_token()?;
            return parse_while_loop(lexer);
        }
        Token::If => {
            lexer.consume_token()?;
            return parse_if_statement(lexer);
        }
        _ => {}
    };

    let mut is_global = false;
    let mut is_const = false;
    let mut is_array = false;
    let before_keywords = lexer.at_next_token();
    loop {
        match lexer.peek_token()? {
            Token::Global => is_global = true,
            Token::Const => is_const = true,
            Token::Array => is_array = true,
            _ => break,
        }
        lexer.consume_token()?;
    }
    let after_keywords = lexer.at_last_token();

    let must_be_assignment = is_global || is_array || is_const;

    let statement_expr_start = lexer.at_next_token();
    let expr = parse_expression(lexer)?;

    match expr {
        Expression::Call(call) if !must_be_assignment => {
            expect_token(lexer, Token::EndOfLine)?;
            Ok(Statement::Call(call))
        }
        Expression::Assignable(value_expr) => {
            if must_be_assignment {
                if is_array {
                    match value_expr.clone() {
                        Assignable::Index { to_index, indices } => {
                            expect_token(lexer, Token::EndOfLine)?;
                            if let Expression::Assignable(Assignable::Variable(variable)) =
                                *to_index
                            {
                                return Ok(Statement::Assign {
                                    is_const,
                                    is_global,
                                    is_array,
                                    to_assign: Assignable::Variable(variable),
                                    assign_with: AssignmentValue::BlankArray(indices),
                                });
                            }
                        }
                        _ => {}
                    }
                }

                expect_token(lexer, Token::Assign)?;
                parse_rh_of_assignment(lexer, is_global, is_array, is_const, value_expr)
            } else {
                match lexer.peek_token()? {
                    Token::Assign => {
                        lexer.consume_token()?;
                        parse_rh_of_assignment(lexer, is_global, is_array, is_const, value_expr)
                    }
                    _ => Err(SyntaxError::new_single(
                        statement_expr_start,
                        lexer.at_last_token(),
                        SyntaxErrorKind::CannotUseAssignableExpressionAsStatement,
                    )),
                }
            }
        }
        _ => {
            if must_be_assignment {
                let mut keywords = Vec::new();
                if is_global {
                    keywords.push(Token::Global);
                }
                if is_const {
                    keywords.push(Token::Const);
                }
                if is_array {
                    keywords.push(Token::Array);
                }

                Err(SyntaxError::new_single(
                    before_keywords,
                    after_keywords,
                    SyntaxErrorKind::UnexpectedKeyWords(keywords),
                ))
            } else {
                Err(SyntaxError::new_single(
                    statement_expr_start,
                    lexer.at_last_token(),
                    SyntaxErrorKind::CannotUseExpressionAsStatement,
                ))
            }
        }
    }
}

fn expect_token(lexer: &mut impl Lexer, token: Token) -> Result<()> {
    let expected_token_err_start = lexer.at_next_token();
    if lexer.consume_token()? != token {
        Err(SyntaxError::new_single(
            expected_token_err_start,
            lexer.at_last_token(),
            SyntaxErrorKind::ExpectedOneOf(vec![token]),
        ))
    } else {
        Ok(())
    }
}

fn parse_binary_operator(lexer: &mut impl Lexer) -> Result<BinaryOperator> {
    let operator_err_start = lexer.at_next_token();
    match lexer.consume_token()? {
        Token::Add => Ok(BinaryOperator::Add),
        Token::Subtract => Ok(BinaryOperator::Subtract),
        Token::Multiply => Ok(BinaryOperator::Multiply),
        Token::Divide => Ok(BinaryOperator::Divide),
        Token::And => Ok(BinaryOperator::And),
        Token::Or => Ok(BinaryOperator::Or),
        Token::GreaterThan => Ok(BinaryOperator::GreaterThan),
        Token::LessThan => Ok(BinaryOperator::LessThan),
        Token::GreaterThanOrEquals => Ok(BinaryOperator::GreaterThanOrEquals),
        Token::LessThanOrEquals => Ok(BinaryOperator::LessThanOrEquals),
        Token::Equals => Ok(BinaryOperator::Equals),
        Token::NotEquals => Ok(BinaryOperator::NotEquals),
        Token::Quotient => Ok(BinaryOperator::Quotient),
        Token::Remainder => Ok(BinaryOperator::Remainder),
        Token::Power => Ok(BinaryOperator::Power),
        _ => Err(SyntaxError::new_single(
            operator_err_start,
            lexer.at_last_token(),
            SyntaxErrorKind::ExpectedBinaryOperator,
        )),
    }
}

fn parse_identifier(lexer: &mut impl Lexer) -> Result<String> {
    let identifier_err_start = lexer.at_next_token();
    match lexer.consume_token()? {
        Token::Identifier(ident) => Ok(ident),
        _ => Err(SyntaxError::new_single(
            identifier_err_start,
            lexer.at_last_token(),
            SyntaxErrorKind::ExpectedIdentifier,
        )),
    }
}

fn parse_unary_operator(lexer: &mut impl Lexer) -> Result<UnaryOperator> {
    let operator_err_start = lexer.at_next_token();
    match lexer.consume_token()? {
        Token::Not => Ok(UnaryOperator::Not),
        _ => Err(SyntaxError::new_single(
            operator_err_start,
            lexer.at_last_token(),
            SyntaxErrorKind::ExpectedUnaryOperator,
        )),
    }
}

fn parse_expression_list(lexer: &mut impl Lexer, ending_token: Token) -> Result<Vec<Expression>> {
    let mut result = Vec::new();

    loop {
        let expected_separator_err = lexer.at_next_token();
        let next = lexer.peek_token()?;
        if next == ending_token {
            lexer.consume_token()?;
            return Ok(result);
        }

        if result.len() == 0 || next == Token::Comma {
            if result.len() != 0 {
                lexer.consume_token()?;
            }
            result.push(parse_expression(lexer)?);
        } else {
            lexer.consume_token()?;
            return Err(SyntaxError::new_single(
                expected_separator_err,
                lexer.at_last_token(),
                SyntaxErrorKind::ExpectedOneOf(vec![Token::Comma, ending_token]),
            ));
        }
    }
}

fn parse_unary_expression(lexer: &mut impl Lexer) -> Result<Expression> {
    let beginning_of_expr = lexer.at_next_token();

    let mut expr = match lexer.peek_token()? {
        Token::IntegerLiteral(i) => {
            lexer.consume_token()?;
            Expression::IntegerLiteral(i)
        }
        Token::RealLiteral(r) => {
            lexer.consume_token()?;
            Expression::RealLiteral(r)
        }
        Token::BooleanLiteral(b) => {
            lexer.consume_token()?;
            Expression::BooleanLiteral(b)
        }
        Token::StringLiteral(s) => {
            lexer.consume_token()?;
            Expression::StringLiteral(s)
        }
        Token::Identifier(ident) => {
            lexer.consume_token()?;
            Expression::Assignable(Assignable::Variable(ident))
        }
        Token::OpenBrace => {
            lexer.consume_token()?;
            let result = parse_expression(lexer)?;
            expect_token(lexer, Token::CloseBrace)?;
            result
        }
        Token::OpenSquareBrace => {
            lexer.consume_token()?;
            Expression::ArrayLiteral(parse_expression_list(lexer, Token::CloseSquareBrace)?)
        }
        _ => {
            return match parse_unary_operator(lexer) {
                Ok(operator) => Ok(Expression::Unary {
                    operand: Box::new(parse_unary_expression(lexer)?),
                    operator: operator,
                }),
                _ => Err(SyntaxError::new_single(
                    beginning_of_expr,
                    lexer.at_last_token(),
                    SyntaxErrorKind::ExpectedExpression,
                )),
            }
        }
    };

    loop {
        match lexer.peek_token()? {
            Token::Period => {
                lexer.consume_token()?;
                expr = Expression::Assignable(Assignable::Property {
                    value: Box::new(expr),
                    name: parse_identifier(lexer)?,
                });
            }
            Token::OpenSquareBrace => {
                lexer.consume_token()?;
                expr = Expression::Assignable(Assignable::Index {
                    to_index: Box::new(expr),
                    indices: parse_expression_list(lexer, Token::CloseSquareBrace)?,
                });
            }
            Token::OpenBrace => {
                let callee = match expr.clone() {
                    Expression::Assignable(Assignable::Variable(identifier)) => {
                        Callee::SubProgram(identifier)
                    }
                    Expression::Assignable(Assignable::Property { value, name }) => {
                        Callee::Member {
                            object: *value,
                            member: name,
                        }
                    }
                    _ => {
                        return Err(SyntaxError::new_single(
                            beginning_of_expr,
                            lexer.at_last_token(),
                            SyntaxErrorKind::CannotCall,
                        ))
                    }
                };

                lexer.consume_token()?;
                let args = parse_expression_list(lexer, Token::CloseBrace)?;

                expr = Expression::Call(Call {
                    callee: Box::new(callee),
                    args: args,
                });
            }
            _ => return Ok(expr),
        }
    }
}

fn parse_expression(lexer: &mut impl Lexer) -> Result<Expression> {
    let mut first_expr = parse_unary_expression(lexer)?;
    let mut expressions = Vec::new();

    loop {
        let before = lexer.clone();
        match parse_binary_operator(lexer) {
            Ok(operator) => {
                let next = parse_unary_expression(lexer)?;
                expressions.push((next, operator));
            }
            Err(_) => {
                *lexer = before;

                for (expr, operator) in expressions.into_iter() {
                    first_expr = Expression::Binary {
                        operator: operator,
                        left: Box::new(first_expr),
                        right: Box::new(expr),
                    }
                }

                return Ok(first_expr);
            }
        }
    }
}
