# Lambda Calculus Examples

A series of Lambda Calculus implementations starting from Simply Typed
evaluation, then work up through bidirectional typechecking,
normalization by evaluation, elaboration and then various type system
extensions.

These examples build up sequentially, but each module is a standalone program
that can be read independently. we skip parsing for brevity but include pretty
printers from the concrete syntax to a human readable notation to make the
examples easier to read.

The goal is to provide best practices examples of all the features you
might want to include in your custom language in one place.

- [X] SimplyTypedEvaluation
- [X] BidirectionalTypechecking
- [X] NormalizationByEvaluation
- [X] Elaboration
- [X] TypedHoles
- [X] SystemT
- [X] Records
- [X] Subtyping
- [X] Nominal Inductive Types
- [X] Iso-Inductive Types
- [X] System F
- [X] Martin-Lof Type Theory (Pi and Sigma Types)
- [ ] Type Universes
- [ ] Universe Polymorphism
- [ ] Implicit Universe Levels with Constraint Solving
- [ ] Tarski Universes
- [ ] Indexed Inductive Types
- [ ] Equality
- [ ] Case-Trees
- [ ] Row Polymorphism
- [ ] Linear Types

Additionally we plan to provide complete examples of STLC, SystemF, and MLTT
compiling to the following targets:

- [ ] Javascript
- [ ] A simple stack machine
- [ ] LLVM

The ultimate term goal is build a [1lab](https://www.1lab.dev) style literate coded webapp that
allows exploring Lambda Calculus in all its forms.
