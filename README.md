# OCR ERL Interpreter

This project is an interpreter for OCR Exam Reference Language (ERL), which is a structured pseudocode
that is used by the OCR exam board in GCSE computer science exams. 

An overview of the language can be found [here](https://www.ocr.org.uk/Images/558027-specification-gcse-computer-science-j277.pdf),
specifically section 3c on page 32. However, the specification can hardly be described as exhaustive, so this interpreter makes several
assumptions about parts of the language.

## Usage
Download the latest nightly build [here](https://nightly.link/Lauriethefish/ocr-erl/workflows/build/master) and extract the ZIP file.
You can run code by passing the path to a file as a command line argument:
```sh
./erl code.erl
```

__Additional arguments:__
`--emit-bytecode`: prints the bytecode generated from the AST before running the program.

`--time`: displays the time (in seconds) that the program took to execute.

## Why
In the OCR exams (specifically section B), you can write code in a high-level language of your choosing (usually python), or in OCR Exam
Reference Language. (pseudocode is NOT allowed in section B).
Therefore, learning ERL thoroughly is usually unnecessary for a competant programmer, as it is self-explanatory enough to be understood
in the questions.

However, in my experience, writing python in the exams is really annoying, due to its dependance on whitespace an indentation.
Using another high-level language such as C# or Java is possible, but these are very verbose and there often isn't enough room. It also brings a higher chance that the examiner might not fully understand your code.
Therefore, learning ERL can be useful. Using this interpreter, anybody can write and run ERL code, making it much easier to learn.

## TODO List (pulled from spec)
- [x] All operators.
- [x] Comments.
- [x] Assignment.
- [x] Basic IO (`input()`/`print()`).
- [x] Casting.
- [x] `for` loops.
- [x] `while` loops.
- [ ] `do until` loops
- [x] `if then elseif` statements.
- [ ] `switch` statements.
- [x] String length.
- [x] Substrings
- [x] Concatenation
- [x] ASCII conversion
- [ ] File IO
- [ ] Arrays
- [x] Procedures
- [x] Functions
- [x] Random numbers


## Project Structure
This interpreter is made up of three main crates:
- `erl_cli`: command line interface for parsing and executing ERL.
- `erl_parser`: defines the AST for ERL, and implements a simple parser.
- `erl_bytecode_exec`: executes the ERL AST, by first converting it into bytecode.

## Licensing
This project is available under the GNU General Public License, version 3.
The full license text is [here](https://github.com/Lauriethefish/ocr-erl/tree/main/LICENSE).
