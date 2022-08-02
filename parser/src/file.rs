//! This module handles loading a file of code and splitting it up into lines and characters to be more easily read by the interpreter.

use core::fmt;
use std::{
    fmt::{Display, Formatter, Write},
    fs, io,
    path::PathBuf,
    rc::Rc,
};

use colored::Colorize;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn file_from_string_characters_should_be_split_into_lines() {
        let file = File::from_string("t1\nt2\r\nt3".to_string());

        assert_eq!(
            vec![
                vec!['t', '1', '\n'],
                vec!['t', '2', '\n'],
                vec!['t', '3', '\n']
            ],
            file.inner.contents
        )
    }

    #[test]
    fn file_beginning_should_be_at_start_of_file() {
        let file = File::from_string("example".to_string());
        assert_eq!(
            file.beginning(),
            FilePosition {
                row: 0,
                column: 0,
                file: file
            }
        )
    }

    #[test]
    fn file_get_char_should_return_correct_char() {
        let file = File::from_string("line1\n2line".to_string());
        assert_eq!(Some('1'), file.get_char(0, 4));
        assert_eq!(Some('2'), file.get_char(1, 0));
    }

    #[test]
    fn file_get_char_should_return_none_if_out_of_bounds() {
        let file = File::from_string("line1\n2line".to_string());
        assert_eq!(None, file.get_char(0, 6));
        assert_eq!(None, file.get_char(2, 0));
    }

    #[test]
    fn file_columns_in_line_should_match() {
        let file = File::from_string("test\ntest2".to_string());
        assert_eq!(Some(5), file.columns_in_line(0));
        assert_eq!(Some(6), file.columns_in_line(1));
    }

    #[test]
    fn file_columns_in_line_should_give_none_if_out_of_bounds() {
        let file = File::from_string("test\ntest2".to_string());
        assert_eq!(None, file.columns_in_line(2));
    }

    #[test]
    fn file_partialeq_should_return_true_if_same_internal_file() {
        let a = File::from_string("example".to_string());
        let b = a.clone();
        assert!(PartialEq::eq(&a, &b));
    }

    #[test]
    fn file_partialeq_should_return_false_if_different_internal_file() {
        // Despite these files being identical, the pointer to the underlying file is different, and thus this comparison should give `false`.
        let a = File::from_string("example".to_string());
        let b = File::from_string("example".to_string());
        assert!(!PartialEq::eq(&a, &b));
    }

    #[test]
    fn file_position_new_should_give_correct_values() {
        let file = File::from_string("example".to_string());
        assert_eq!(
            FilePosition {
                row: 3,
                column: 4,
                file: file.clone()
            },
            FilePosition::new(3, 4, file)
        );
    }

    #[test]
    fn file_position_advance_to_next_char_should_move_to_correct_next_char() {
        let file = File::from_string("line1\n2line".to_string());
        let mut position = FilePosition::new(0, 4, file);
        position.advance_to_next_char();
        assert_eq!(5, position.column);
        assert_eq!(0, position.row);
        position.advance_to_next_char();
        assert_eq!(0, position.column);
        assert_eq!(1, position.row);
    }

    #[test]
    fn file_position_move_to_next_line_should_skip_line() {
        let file = File::from_string("line1\n2line".to_string());
        let mut position = FilePosition::new(0, 4, file);

        position.move_to_next_line();
        assert_eq!(0, position.column);
        assert_eq!(1, position.row);
    }

    #[test]
    fn file_position_move_back_should_return_true_if_within_file() {
        let file = File::from_string("line1\n2line".to_string());

        let mut position = FilePosition::new(1, 1, file.clone());
        assert!(position.rewind_to_previous_char_if_possible());
        assert_eq!(1, position.row);
        assert_eq!(0, position.column);
        assert!(position.rewind_to_previous_char_if_possible());
        assert_eq!(0, position.row);
        assert_eq!(5, position.column);
    }

    #[test]
    fn file_position_move_back_should_return_false_if_out_of_file() {
        let file = File::from_string("line1\n2line".to_string());
        let mut position = FilePosition::new(0, 0, file.clone());

        assert!(!position.rewind_to_previous_char_if_possible());
    }

    #[test]
    fn line_highlight_new_should_succeed_if_on_same_line_and_file() {
        let file = File::from_string("line1\n2line".to_string());
        let a = FilePosition::new(1, 1, file.clone());
        let b = FilePosition::new(1, 3, file.clone());

        assert_eq!(
            LineHighlight {
                from_column: 1,
                to_column: 3,
                row: 1,
                file
            },
            LineHighlight::new(&a, &b)
        )
    }

    #[test]
    #[should_panic]
    fn line_highlight_new_should_panic_if_on_different_lines() {
        let file = File::from_string("line1\n2line".to_string());
        let a = FilePosition::new(1, 1, file.clone());
        let b = FilePosition::new(2, 3, file.clone());

        LineHighlight::new(&a, &b);
    }

    #[test]
    #[should_panic]
    fn line_highlight_new_should_panic_if_in_different_files() {
        let file_a = File::from_string("myFile".to_string());
        let file_b = File::from_string("myOtherFile".to_string());
        let a = FilePosition::new(1, 1, file_a);
        let b = FilePosition::new(1, 3, file_b);

        LineHighlight::new(&a, &b);
    }
}

/// Used to handle a file already separated into its characters.
/// Internally refers to the file content using an [Rc] to avoid expensive cloning.
#[derive(Debug, Clone)]
pub struct File {
    inner: Rc<InternalFile>,
}

#[derive(Debug)]
struct InternalFile {
    /// Lines within the file
    contents: Vec<Vec<char>>,
    /// Path of the file for use during error reporting
    path: Option<PathBuf>,
}

impl File {
    /// Creates a [File] from the given contents.
    ///
    /// # Arguments
    /// * `contents` - the contents of the file.
    ///
    /// # Examples
    /// ```
    /// use erl_parser::File;
    /// let file = File::from_string("example = 5".to_owned());
    ///
    /// let ast = erl_parser::parse_program(file).unwrap();
    /// ```
    pub fn from_string(contents: String) -> Self {
        Self::new_internal(contents, None)
    }

    /// Reads a [File] from the given path.
    ///
    /// # Arguments
    /// * `path` - the path of the file to read from. This is also used for error-reporting purposes when parsing.
    ///
    /// # Examples
    /// ```no_run
    /// use erl_parser::File;
    /// use std::path::PathBuf;
    ///
    /// let file = File::read(PathBuf::from("code.erl")).unwrap();
    ///
    /// let ast = erl_parser::parse_program(file).unwrap();
    /// ```
    pub fn read(path: PathBuf) -> io::Result<Self> {
        let contents = fs::read_to_string(&path)?;
        Ok(Self::new_internal(contents, Some(path)))
    }

    fn new_internal(contents: String, path: Option<PathBuf>) -> Self {
        Self {
            inner: Rc::new(InternalFile {
                contents: contents
                    .lines()
                    .map(|line| line.chars().chain(['\n']).collect())
                    .collect(),
                path,
            }),
        }
    }

    /// Returns the [FilePosition] at the start of the file.
    ///
    /// # Examples
    /// ```
    /// use erl_parser::File;
    ///
    /// let beginning = File::from_string("example = 5".to_owned()).beginning();
    ///
    /// let mut lexer = erl_parser::FileLexer::new(beginning);
    /// let ast = erl_parser::parse_root_block(&mut lexer).unwrap();
    /// ```
    pub fn beginning(&self) -> FilePosition {
        FilePosition {
            row: 0,
            column: 0,
            file: self.clone(),
        }
    }

    /// Gets the number of columns (characters) in the given row in this file.
    /// Panics if the given row is out of range of the lines in the file.
    pub(crate) fn columns_in_line(&self, row: usize) -> Option<usize> {
        self.inner
            .contents
            .get(row)
            .map(|row_contents| row_contents.len())
    }

    /// Writes the given line to the given formatter.
    /// If the line is out of bounds of the file, only a newline is written.
    fn fmt_line(&self, f: &mut Formatter, row: usize) -> fmt::Result {
        if let Some(row) = self.inner.contents.get(row) {
            for i in 0..row.len() {
                f.write_char(row[i])?;
            }

            Ok(())
        } else {
            f.write_char('\n')
        }
    }

    /// Gets the char at the given row and column.
    pub(crate) fn get_char(&self, row: usize, column: usize) -> Option<char> {
        match self.inner.contents.get(row) {
            Some(row_contents) => row_contents.get(column).copied(),
            None => None,
        }
    }
}

impl PartialEq for File {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner)
    }
}

/// A reference to a particular character within a file.
#[derive(Clone, PartialEq, Debug)]
pub struct FilePosition {
    row: u32,
    column: u32,
    file: File,
}

impl FilePosition {
    /// Creates a new [FilePosition].
    ///
    /// # Arguments
    /// * `row` - the row (line number) of this position, starting from 0.
    /// * `column` - the column number of this position, starting from 0.
    /// * `file` - the file that this position is within.
    ///
    /// # Examples
    /// ```
    /// use erl_parser::{File, FilePosition};
    ///
    /// let file = File::from_string("test = 5\ntest = 6".to_owned());
    ///
    /// // Skip the first line of the file
    /// let position = FilePosition::new(1, 0, file);
    ///
    /// let mut lexer = erl_parser::FileLexer::new(position);
    /// let root_statements = erl_parser::parse_root_block(&mut lexer).unwrap();
    ///
    /// // The first line was skipped, so only one statement will have been parsed.
    /// assert_eq!(1, root_statements.len());
    /// ```
    pub fn new(row: u32, column: u32, file: File) -> FilePosition {
        FilePosition { row, column, file }
    }

    /// Moves this [FilePosition] to the next character.
    pub(crate) fn advance_to_next_char(&mut self) {
        self.column += 1;

        if self.column as usize
            >= match self.file.columns_in_line(self.row as usize) {
                Some(columns) => columns,
                None => return,
            }
        {
            self.move_to_next_line();
        }
    }

    /// Moves this [FilePosition] to the previous character, if that character is within the file.
    pub(crate) fn rewind_to_previous_char_if_possible(&mut self) -> bool {
        if self.column == 0 {
            if self.row > 0 {
                self.row -= 1;
            } else {
                return false;
            }

            self.column = match self.file.columns_in_line(self.row as usize) {
                Some(columns) => columns as u32 - 1,
                None => {
                    self.row += 1;
                    return false;
                }
            };
        } else {
            self.column -= 1;
        }
        true
    }

    /// Gets the character at this position.
    pub(crate) fn get_char(&self) -> Option<char> {
        self.file.get_char(self.row as usize, self.column as usize)
    }

    /// Skips the current line of characters and moves to the leftmost character in the next line.
    pub(crate) fn move_to_next_line(&mut self) {
        self.row += 1;
        self.column = 0;
    }

    /// The row number of this [FilePosition].
    pub fn row(&self) -> u32 {
        self.row
    }

    /// The column number of this [FilePosition].
    pub fn column(&self) -> u32 {
        self.column
    }

    /// The [File] that this [FilePosition] is within.
    pub fn file(&self) -> File {
        self.file.clone()
    }
}

/// A reference to a range of characters within a line in a file for error reporting.
#[derive(Clone, Debug, PartialEq)]
pub struct LineHighlight {
    from_column: u32,
    to_column: u32,
    row: u32,
    file: File,
}

impl LineHighlight {
    /// Creates a [LineHighlight] between these two positions, which must be on the same line in the same file.
    /// Panics if the two positions are on different lines, or are in different files
    pub(crate) fn new(from: &FilePosition, to: &FilePosition) -> Self {
        if from.file != to.file {
            panic!("Cannot create `LineHighlight` between two different files")
        }

        if from.row != to.row {
            panic!("Cannot create `LineHighlight` between characters on different rows")
        }

        Self {
            from_column: from.column,
            to_column: to.column,
            row: from.row,
            file: from.file.clone(),
        }
    }

    /// Gets the column index at which this [LineHighlight] starts.
    pub fn from_column(&self) -> u32 {
        self.from_column
    }

    /// Gets the column index at which this [LineHighlight] ends (inclusive).
    pub fn to_column(&self) -> u32 {
        self.from_column
    }

    /// Gets the row that this [LineHighlight] is on.
    pub fn row(&self) -> u32 {
        self.row
    }

    /// Gets the [File] that this [LineHighlight] is in.
    pub fn file(&self) -> File {
        self.file.clone()
    }

    /// Formats a a message, displaying the line of this highlight, then indicating the highlighted characters underneath with `^`.
    pub fn display_msg<T: Display>(&self, f: &mut Formatter, msg: T) -> fmt::Result {
        f.write_fmt(format_args!("\n{}", "error:\n".red().bold()))?;

        let path = match &self.file.inner.path {
            Some(path) => path.display().to_string(),
            None => "<anonymous>".to_owned(),
        };

        f.write_fmt(format_args!(
            "{} {}:{}:{}\n",
            "-->".bright_blue().bold(),
            path,
            self.row + 1,
            self.from_column + 1
        ))?;

        f.write_fmt(format_args!("  {} ", "|".bright_blue().bold()))?;
        self.file.fmt_line(f, self.row as usize)?;
        f.write_fmt(format_args!("  {} ", "|".bright_blue().bold()))?;
        for _ in 0..self.from_column {
            f.write_str(" ")?;
        }

        for _ in self.from_column..=self.to_column {
            f.write_fmt(format_args!("{}", "^".red().bold()))?;
        }

        f.write_fmt(format_args!(" {}\n", format!("{}", msg).red().bold()))
    }
}
