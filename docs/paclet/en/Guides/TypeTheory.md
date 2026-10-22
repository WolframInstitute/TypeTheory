---
Template: Guide
Name: TypeTheory
Title: TypeTheory Proof Engine
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/guide/TypeTheory
Description: A proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language with its own symbols.
Keywords: [type theory, dependent types, Calculus of Inductive Constructions, proof assistant, proof checking, kernel, inductive types, tactics, classical logic, Booleans, decidability, lists, instances, type classes, coercions, Lean]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude, InstancesAndCoercions, TheIntegers, RulesAndComputation, Quantities, HomotopyTypeTheory, MathlibInTypeTheory]
Links: ["[LeanLink, whose LeanToTypeTheory and TypeTheoryToLean exchange proofs with Lean](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink)"]
---

## Abstract

<code>WolframInstitute\`TypeTheory\`</code> is a proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language. Its terms are ordinary expressions built from the language's own symbols - [Function](), [Typed](), [ForAll](), [Implies](), [Equal](), [Plus]() - held in a [TypeTheoryTerm](). Declarations are constructors, such as [TypeTheoryTheorem]() and [TypeTheoryInductiveType](), that a [TypeTheoryEnvironment]() checks with a small kernel; terms, proofs and declarations that name no environment are in the default environment, the prelude of classical logic, equality, the natural numbers, the Booleans, decisions, quotients, pairs, sums, options and lists, unless [SetTypeTheoryEnvironment]() sets another; the integers are a quotient in an environment of their own. [True](), [And]() and the other connectives are propositions or Booleans, as their types decide, and elaboration fills in instances and inserts coercions, as Lean's type classes and coercions do. The rules the kernel checks by are a value, [TypeTheoryRules](): the HoTT environment follows Martin-Löf type theory, without Prop, with univalence and the circle, and rules with quantities erase variables or use them at most once, as affine type theories do. [TypeTheoryProof]() and [TypeTheoryTactic]() build proofs step by step, and nothing a tactic does is trusted: the kernel checks the finished proof.

## Functions

### Terms

- [TypeTheoryTerm]() a term of the type theory, held, in the environment its constants come from
- [TypedImplicit]() an implicit binder, whose argument is found from the others
- [TypeUniverse]() a universe: <code>[TypeUniverse]()[0]</code> is Prop, <code>[TypeUniverse]()[1]</code> is Type
- [ImpredicativeMaximum]() the universe level of a function type into a universe
- [InductiveRecursor]() the recursor of an inductive type, generated with it

### Environments and declarations

- [TypeTheoryEnvironment]() an environment of declared constants: the prelude extended with declarations, the constructive environment without its axioms, or one built from none
- [SetTypeTheoryEnvironment]() makes an environment the default, [$TypeTheoryEnvironment](), of the terms, proofs and declarations that name none
- [TypeTheoryAxiom]() declares an axiom
- [TypeTheoryDefinition]() declares a definition, an instance of a class or a coercion
- [TypeTheoryTheorem]() declares a theorem with its proof
- [TypeTheoryInductiveType]() declares an inductive type with its constructors, or mutually inductive types
- [TypeTheoryNaturalNumbers]() registers the natural numbers that literals belong to, and the operations the kernel computes on them
- [TypeTheoryRewriteRule]() makes an axiom compute, where the rules allow it
- [TypeTheoryQuotients]() declares the quotient types of Lean's kernel
- [TypeTheoryRules]() the rules an environment follows: the calculus of inductive constructions, with quotients, or Martin-Löf type theory without Prop, and either with quantities that bound how many times code uses a variable
- [TypeTheoryTranslate]() moves the declarations of an environment to other rules, whose kernel checks them again

### Checking and computing

- [TypeTheoryCheck]() the type of a term, a term checked against a type, or a whole environment checked again
- [DefinitionallyEqualQ]() whether two terms are equal by computation
- [WeakHeadNormalForm]() a term reduced until its head can no longer reduce

### Proofs

- [TypeTheoryProof]() a proof in progress, with its open goals
- [TypeTheoryTactic]() a tactic: `"Introduce"`, `"Exact"`, `"Apply"`, `"Reflexivity"`, `"Induction"`, `"Cases"`, `"Generalize"`, `"Constructor"`, `"Assumption"`, `"Rewrite"`, `"Change"`, `"Simplify"`, `"Decide"`, `"Ring"`, and the Wolfram oracles `"FindInstance"`, `"PolynomialReduce"`, `"LinearArithmetic"` and `"FindEquationalProof"`

### The prelude: logic and equality

- [TrueIntroduction]() the proof of [True](); [FalseElimination]() anything follows from [False]()
- [AndIntroduction](), [AndEliminationLeft](), [AndEliminationRight]() proving and using [And]()
- [OrIntroductionLeft](), [OrIntroductionRight]() proving [Or]()
- [EquivalentIntroduction](), [EquivalentForward](), [EquivalentBackward]() proving and using [Equivalent]()
- [EquivalentReflexivity](), [EquivalentSymmetry](), [EquivalentTransitivity]() the laws of [Equivalent]()
- [ExistsIntroduction]() proving [Exists]() with a witness
- [EqualityReflexivity](), [EqualitySymmetry](), [EqualityTransitivity](), [EqualityCongruence](), [EqualitySubstitution]() equality, with [Unequal]() its negation
- [Identity](), [Composition]() the identity function and composition

### The prelude: quotients

- [QuotientType]() the type of the classes of a relation, Lean's `Quot`
- [QuotientIntroduction]() the class of an element
- [QuotientLift]() a function that respects the relation, applied to classes, computing on a class
- [QuotientInduction]() a property of every class, from the classes of the elements

### The prelude: classical logic

- [PropositionalExtensionality](), [QuotientSoundness](), [Choice]() the axioms of the prelude, Lean's three
- [FunctionExtensionality]() functions equal at every point are equal, proved from [QuotientSoundness]()
- [NonemptyIntroduction]() proving [Nonempty](), which [Choice]() takes to an element
- [SubtypeIntroduction]() an element of a [Subtype](), with a proof of its property
- [ChosenWitness](), [ChosenWitnessProperty]() a witness chosen from a proof of [Exists](), and its property
- [ExcludedMiddle](), [DoubleNegationElimination]() classical logic, proved from the axioms

### The prelude: natural numbers

- [Naturals]() the natural numbers, [NonNegativeIntegers](), by a shorter name
- [NaturalNumberZero](), [NaturalNumberSuccessor](), [NaturalNumberPredecessor]() the constructors of [NonNegativeIntegers](), and the number before
- [Plus](), [Times](), [Power](), [Subtract]() arithmetic, each by recursion on its second argument
- [LessEqualReflexivity](), [LessEqualStep]() the constructors of [LessEqual](), with [Less](), [GreaterEqual]() and [Greater]() defined from it

### The prelude: Booleans

- [Booleans]() with the values `"false"` and `"true"` and the operations `"not"`, `"and"` and `"or"`, constants named by strings, which [False](), [True](), [Not](), [And]() and [Or]() stand for where a Boolean is expected

### The prelude: decisions

- [Decidable]() the class of decisions of a proposition, made with [DecidableTrue]() and [DecidableFalse]()
- [Decide]() the Boolean of a proposition's decision, found among the instances, and [DecideSoundness]() the proof from a decision that computes to `"true"`
- [NaturalNumberEqualityDecidable](), [LessEqualDecidable]() the instances deciding `==` and `<=` of natural numbers
- [NotDecidable](), [AndDecidable](), [OrDecidable]() the instances deciding [Not](), [And]() and [Or]() from the decisions of their parts

### The integers

- <code>[TypeTheoryEnvironment]()["Integers"]</code> the prelude with the integers, classes of pairs of natural numbers, where `+`, `*`, `-` and the comparisons are the integers' wherever the types say so
- [IntegerAdditionCommutativity](), [IntegerAdditionAssociativity](), [IntegerAdditionZero](), [IntegerAdditionNegation](), [IntegerSubtractionNegation]() addition and negation
- [IntegerMultiplicationCommutativity](), [IntegerMultiplicationAssociativity](), [IntegerMultiplicationOne](), [IntegerDistributivity]() multiplication
- [IntegerOfNaturalAddition](), [IntegerOfNaturalMultiplication]() the natural numbers among the integers, and [IntegerLessEqualReflexivity]() the order

### The prelude: pairs, sums, options and lists

- [CartesianProduct]() pairs, made with [Pair]()
- [DisjointUnion]() sums, made with [LeftInjection]() and [RightInjection]()
- [Option]() optional values, [OptionNone]() and [OptionSome]()
- [Lists]() lists, built from [EmptyList]() by [ListPrepend](), with [Join](), [Length](), [Map](), [Append]() and [Reverse]()
- [JoinEmptyRight](), [JoinAssociativity](), [LengthJoin](), [LengthMap](), [MapJoin](), [MapComposition](), [ReverseJoin](), [ReverseReverse](), [LengthReverse]() the laws of lists

### Homotopy type theory

- [Transport](), [DependentCongruence](), [TransportConstant]() carrying along paths, which compute on reflexivity
- [IsEquivalence](), [EquivalenceProof](), [Equivalence](), [EquivalenceIntroduction](), [IdentityEquivalence]() equivalences
- [EqualityToEquivalence](), [Univalence](), [EquivalenceToEquality](), [UnivalenceComputation]() univalence
- [NegationEquivalence](), [IsSet](), [UniverseNotSet]() the universe is not a set
- [CircleBase](), [CircleLoop](), [CircleInduction](), [CircleInductionBase](), [CircleInductionLoop]() the circle, a higher inductive type

### The prelude: theorems about the natural numbers

- [AdditionZeroRight](), [AdditionZeroLeft](), [AdditionSuccessorRight](), [AdditionSuccessorLeft](), [AdditionCommutativity](), [AdditionAssociativity]() addition
- [MultiplicationZeroRight](), [MultiplicationZeroLeft](), [MultiplicationSuccessorRight](), [MultiplicationSuccessorLeft](), [MultiplicationOneRight](), [MultiplicationOneLeft]() multiplication by small numbers
- [MultiplicationCommutativity](), [MultiplicationAssociativity](), [MultiplicationDistributivityLeft](), [MultiplicationDistributivityRight]() the laws of multiplication
- [SubtractionZeroRight](), [SubtractionZeroLeft](), [SubtractionSuccessor](), [SubtractionSelf](), [AdditionSubtractionCancellation]() subtraction, and [MultiplicationCancellation]() cancelling a positive factor
- [PowerZero](), [PowerSuccessor](), [PowerOne](), [PowerAddition]() powers
- [SuccessorInjectivity](), [SuccessorNotZero]() the successor
- [LessEqualZero](), [LessEqualSuccessor](), [LessEqualPredecessor](), [LessEqualAddition](), [PredecessorLessEqual]() the order and the successor
- [LessEqualTransitivity](), [LessEqualAntisymmetry](), [LessIrreflexivity](), [SuccessorNotLessEqualZero](), [LessEqualTotality]() the laws of the order
- [AdditionMonotonicity](), [MultiplicationMonotonicity]() sums and multiples of inequalities
