# Lambda Calculus Examples

An exploration of Lambda Calculus, programming language design, and type theory
starting from a foundation of Bidirectional Typechecking and Normalization by
Evaluation.

The `foundation` series sets the stage with a cohesive STLC implementation we
can build on. The `feature museum` then grafts on a variety of popular language
features. `program` and `proof` build up System Fomega and MLTT based systems
respectively.

Every module is a standalone executable written in a direct style of Haskell
with tests. We skip parsing for brevity but include pretty printers from the
concrete syntax to a human readable notation to make the examples easier to
read.

Each section will eventually conclude with a capstone project implementing a
full language including parsing and a repl.

The goal is to provide best practices examples of all the features you might
want to include in your custom language in one place.

1. Foundation
  - [X] Simply Typed Evaluation
  - [X] Bidirectional Typechecking
  - [X] Normalization By Evaluation
  - [X] Elaboration
  - [X] Typed Holes
  - [X] First Order Unification
2. Feature Museum
  - [X] Records
  - [X] System T
  - [X] Nominal Inductive Types
  - [X] Structural Iso-Recursive Types
    - [ ] Equi-Recursive Types
  - [X] Recursion Principles
  - [ ] Subtyping
  - [ ] Row Polymorphism
  - [ ] Linear Types
  - [ ] Modules
3. Program
  - [X] System F
  - [ ] System Omega
  - [ ] System Fomega
  - [ ] Nominal Recursion
  - [ ] First Order Unification up to definitional equality
  - [ ] Implicits
  - [ ] View Patterns
4. Proof
  - [X] Martin-Lof Type Theory
  - [X] Type Universes
  - [X] Universe Polymorphism
  - [ ] Indexed Inductive Types (with eliminators)
  - [ ] Dependent Pattern Matching
  - [ ] Case-Trees
  - [ ] Termination / Coverage Checking
  - [ ] Implicit Universe Levels with Constraint Solving
  - [ ] Tarski Universes
  - [ ] Dependent View Patterns
  - [ ] Cubical

Additionally we plan to provide complete examples of STLC, SystemF, and MLTT
compiling to the following targets:

- [ ] Javascript
- [ ] A simple stack machine
- [ ] LLVM

The ultimate goal is build a [1lab](https://www.1lab.dev) style literate coded
webapp that allows exploring Lambda Calculus in all its forms.
