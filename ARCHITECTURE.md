## Software architecture of mypyvy

### Manifest of important files

- `examples/` example protocols modeled in mypyvy
- `regression/` regression test inputs
- `src/` source files
  - `mypyvy.py` main entry point
  - `syntax.py` definitions of AST classes
  - `parser.py` grammar in the `ply` parser generator DSL
  - `typechecker.py` type checker
  - `translator.py` converts mypyvy expressions into solver expressions
  - `logic.py` "medium-level" interface to the SMT solver
  - `solver.py` low-level interface to the SMT solver
  - `test.py` unit and regression tests
  - `updr.py` implementation of UPDR inference algorithm
  - `pd.py` implementation of primal-dual Houdini inference algorithm

### A note on python types

- mypyvy is written in statically typed python using mypy.
- The types provide good documentation for how data flows through the program.
- We generally do not use escape hatches from mypy, so we expect the annotations
  to be sound.

### Entry points

- mypyvy consists of many subcommands that each operate on a `.pyv` file.

- The main entry point is the `main` method in `src/mypyvy.py`.
  - `main` is responsible for type checking the program and then dispatching to
    the relevant subcommand.
  - Most code that implements the command-line interface (CLI) is contained in this file.
    - Each subcommand defines a method in this file. The more complex methods
      typically dispatch to other files.
  - For some files and subcommands that are considered separate projects, mypyvy
    supports a form of extensibility by moving the CLI dispatch into those projects.
    - For example, `pd.py` implements an `add_argparsers` method that is called by `main`.

- A good example subcommand to start with is `verify`. See the method of the same name.
  - The `verify` method calls `logic.check_init` and `logic.check_transitions`
    to check whether the protocol's invariants are inductive.

  - The file `logic` implements a "medium level" interface to the SMT solver.
    - It supports reasoning at the mypyvy expression and transition level,
      rather than lower level exploded-vocabulary formulas.

- Another good example is the `updr` subcommand. See the method `do_updr` in
  `mypyvy.py`.
  - This method orchestrates the search and then hands it off to the file
    `updr.py`.
  - The file `updr.py` makes extensive use of `logic.py` to implement the UPDR algorithm [1].

[1] Karbyshev et al. 2017. Property-Directed Inference of Universal Invariants or Proving Their Absence. J. ACM 64, 1, Article 7.

### Data structures

- ASTs
  - ASTs are produced by the parser and consumed by the rest of mypyvy.
  - The AST is generally *not* transformed very much after the parser, so by
    understanding the AST, you can understand how most of mypyvy works.
  - Start by reading the `Program` class defined in `src/syntax.py`.
    - A program is a sequence of declarations
    - A declaration can be one of many (roughly 10) different kinds, including
      relations, functions, definitions, transitions, invariants, etc.
  - Then, read `ConstantDecl` and `RelationDecl` in the same file.
    - Declarations such as these generally have a name, argument sorts, and return sort.
    - Declarations can be declared mutable or not.
    - Declarations have a `span`, which is their location in the original input
      file, for error reporting.

- Scope
  - The class `Scope`, also defined in `src/syntax.py` is the main data
    structure of the type checker.
  - The scope binds various names, including sorts, constants, functions, etc.
    - There are two namespaces: sorts and everything else. See `Scope.get_sort`
      and `Scope.get`.
