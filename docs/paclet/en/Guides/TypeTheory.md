---
Template: Guide
Name: TypeTheory
Title: TypeTheory Proof Engine
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/guide/TypeTheory
Description: A proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language with its own symbols.
Keywords: [type theory, dependent types, Calculus of Inductive Constructions, proof assistant, proof checking, kernel, inductive types, tactics, Lean]
RelatedTutorials: [TypeTheoryIntroduction]
Links: ["[LeanLink, whose LeanToTypeTheory and TypeTheoryToLean exchange proofs with Lean](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink)"]
---

## Abstract

<code>WolframInstitute\`TypeTheory\`</code> is a proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language. Its terms are ordinary expressions built from the language's own symbols - [Function](), [Typed](), [ForAll](), [Implies](), [Equal](), [Plus]() - held in a [TypeTheoryTerm](). Declarations are constructors, such as [TypeTheoryTheorem]() and [TypeTheoryInductiveType](), that a [TypeTheoryEnvironment]() checks with a small kernel; terms, proofs and declarations that name no environment are in the prelude, of logic, equality and the natural numbers. [TypeTheoryProof]() and [TypeTheoryTactic]() build proofs step by step, and nothing a tactic does is trusted: the kernel checks the finished proof.

## Functions

### Terms

- [TypeTheoryTerm]() a term of the type theory, held, in the environment its constants come from
- [TypeUniverse]() a universe: <code>[TypeUniverse]()[0]</code> is Prop, <code>[TypeUniverse]()[1]</code> is Type
- [ImpredicativeMaximum]() the universe level of a function type into a universe
- [InductiveRecursor]() the recursor of an inductive type, generated with it

### Environments and declarations

- [TypeTheoryEnvironment]() an environment of declared constants: the prelude extended with declarations, or built from none
- [TypeTheoryAxiom]() declares an axiom
- [TypeTheoryDefinition]() declares a definition
- [TypeTheoryTheorem]() declares a theorem with its proof
- [TypeTheoryInductiveType]() declares an inductive type with its constructors
- [TypeTheoryNaturalNumbers]() registers the natural numbers that literals belong to

### Checking and computing

- [TypeTheoryCheck]() the type of a term, a term checked against a type, or a whole environment checked again
- [DefinitionallyEqualQ]() whether two terms are equal by computation
- [WeakHeadNormalForm]() a term reduced until its head can no longer reduce

### Proofs

- [TypeTheoryProof]() a proof in progress, with its open goals
- [TypeTheoryTactic]() a tactic: `"Introduce"`, `"Exact"`, `"Apply"`, `"Reflexivity"`, `"Induction"`, `"Assumption"`

### The prelude

- [TrueIntroduction]() the proof of [True]()
- [AndIntroduction](), [AndEliminationLeft](), [AndEliminationRight]() proving and using [And]()
- [OrIntroductionLeft](), [OrIntroductionRight]() proving [Or]()
- [FalseElimination]() anything follows from [False]()
- [EqualityReflexivity](), [EqualitySymmetry](), [EqualityTransitivity](), [EqualityCongruence](), [EqualitySubstitution]() equality
- [ExistsIntroduction]() proving [Exists]() with a witness
- [NaturalNumberZero](), [NaturalNumberSuccessor]() the constructors of the natural numbers [NonNegativeIntegers]()
