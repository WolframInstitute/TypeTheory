---
Template: Guide
Name: TypeTheory
Title: TypeTheory Proof Engine
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/guide/TypeTheory
Description: A proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language with its own symbols.
Keywords: [type theory, dependent types, Calculus of Inductive Constructions, proof assistant, proof checking, kernel, inductive types, tactics, classical logic, Booleans, Lean]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude]
Links: ["[LeanLink, whose LeanToTypeTheory and TypeTheoryToLean exchange proofs with Lean](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink)"]
---

## Abstract

<code>WolframInstitute\`TypeTheory\`</code> is a proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language. Its terms are ordinary expressions built from the language's own symbols - [Function](), [Typed](), [ForAll](), [Implies](), [Equal](), [Plus]() - held in a [TypeTheoryTerm](). Declarations are constructors, such as [TypeTheoryTheorem]() and [TypeTheoryInductiveType](), that a [TypeTheoryEnvironment]() checks with a small kernel; terms, proofs and declarations that name no environment are in the prelude, of classical logic, equality, the natural numbers and the Booleans. [True](), [And]() and the other connectives are propositions or Booleans, as their types decide. [TypeTheoryProof]() and [TypeTheoryTactic]() build proofs step by step, and nothing a tactic does is trusted: the kernel checks the finished proof.

## Functions

### Terms

- [TypeTheoryTerm]() a term of the type theory, held, in the environment its constants come from
- [TypeUniverse]() a universe: <code>[TypeUniverse]()[0]</code> is Prop, <code>[TypeUniverse]()[1]</code> is Type
- [ImpredicativeMaximum]() the universe level of a function type into a universe
- [InductiveRecursor]() the recursor of an inductive type, generated with it

### Environments and declarations

- [TypeTheoryEnvironment]() an environment of declared constants: the prelude extended with declarations, the constructive environment without its axioms, or one built from none
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

### The prelude: logic and equality

- [TrueIntroduction]() the proof of [True](); [FalseElimination]() anything follows from [False]()
- [AndIntroduction](), [AndEliminationLeft](), [AndEliminationRight]() proving and using [And]()
- [OrIntroductionLeft](), [OrIntroductionRight]() proving [Or]()
- [EquivalentIntroduction](), [EquivalentForward](), [EquivalentBackward]() proving and using [Equivalent]()
- [EquivalentReflexivity](), [EquivalentSymmetry](), [EquivalentTransitivity]() the laws of [Equivalent]()
- [ExistsIntroduction]() proving [Exists]() with a witness
- [EqualityReflexivity](), [EqualitySymmetry](), [EqualityTransitivity](), [EqualityCongruence](), [EqualitySubstitution]() equality, with [Unequal]() its negation
- [Identity](), [Composition]() the identity function and composition

### The prelude: classical logic

- [PropositionalExtensionality](), [FunctionExtensionality](), [Choice]() the axioms of the prelude
- [NonemptyIntroduction]() proving [Nonempty](), which [Choice]() takes to an element
- [SubtypeIntroduction]() an element of a [Subtype](), with a proof of its property
- [ChosenWitness](), [ChosenWitnessProperty]() a witness chosen from a proof of [Exists](), and its property
- [ExcludedMiddle](), [DoubleNegationElimination]() classical logic, proved from the axioms

### The prelude: natural numbers

- [NaturalNumberZero](), [NaturalNumberSuccessor](), [NaturalNumberPredecessor]() the constructors of [NonNegativeIntegers](), and the number before
- [Plus](), [Times](), [Power](), [Subtract]() arithmetic, each by recursion on its second argument
- [LessEqualReflexivity](), [LessEqualStep]() the constructors of [LessEqual](), with [Less](), [GreaterEqual]() and [Greater]() defined from it

### The prelude: Booleans

- [BooleanFalse](), [BooleanTrue]() the values of [Booleans](), which [False]() and [True]() stand for where a Boolean is expected
- [BooleanNot](), [BooleanAnd](), [BooleanOr]() the operations on Booleans, which [Not](), [And]() and [Or]() stand for on Booleans

### The prelude: theorems about the natural numbers

- [AdditionZeroRight](), [AdditionZeroLeft](), [AdditionSuccessorRight](), [AdditionSuccessorLeft](), [AdditionCommutativity](), [AdditionAssociativity]() addition
- [MultiplicationZeroRight](), [MultiplicationZeroLeft](), [MultiplicationSuccessorRight](), [MultiplicationSuccessorLeft](), [MultiplicationOneRight](), [MultiplicationOneLeft]() multiplication by small numbers
- [MultiplicationCommutativity](), [MultiplicationAssociativity](), [MultiplicationDistributivityLeft](), [MultiplicationDistributivityRight]() the laws of multiplication
- [SubtractionZeroRight](), [SubtractionZeroLeft](), [SubtractionSuccessor](), [SubtractionSelf](), [AdditionSubtractionCancellation]() subtraction
- [PowerZero](), [PowerSuccessor](), [PowerOne](), [PowerAddition]() powers
- [SuccessorInjectivity](), [SuccessorNotZero]() the successor
- [LessEqualZero](), [LessEqualSuccessor](), [LessEqualPredecessor](), [LessEqualAddition](), [PredecessorLessEqual]() the order and the successor
- [LessEqualTransitivity](), [LessEqualAntisymmetry](), [LessIrreflexivity](), [SuccessorNotLessEqualZero]() the laws of the order
