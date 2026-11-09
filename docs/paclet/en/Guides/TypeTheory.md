---
Template: Guide
Name: TypeTheory
Title: TypeTheory Proof Engine
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/guide/TypeTheory
Description: A proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language with its own symbols.
Keywords: [type theory, dependent types, Calculus of Inductive Constructions, proof assistant, proof checking, kernel, inductive types, tactics, classical logic, Booleans, decidability, lists, instances, type classes, coercions, Lean]
RelatedTutorials: [TypeTheoryIntroduction, Elaboration, ProgramsAndProofs, TheWolframLanguage, PatternsAndRewriting, ThePrelude, InstancesAndCoercions, TheIntegers, TheRationals, RulesAndComputation, Paradoxes, Quantities, HomotopyTypeTheory, CubicalTypeTheory, MathlibInTypeTheory]
Links: ["[LeanLink, whose LeanToTypeTheory and TypeTheoryToLean exchange proofs with Lean](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink)"]
---

## Abstract

<code>WolframInstitute\`TypeTheory\`</code> is a proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language. Its terms are ordinary expressions built from the language's own symbols - [Function](), [Typed](), [ForAll](), [Implies](), [Equal](), [Plus]() - held in a [TypeTheoryTerm](). Declarations are constructors, such as [TypeTheoryTheorem]() and [TypeTheoryInductiveType](), that a [TypeTheoryEnvironment]() checks with a small kernel; terms, proofs and declarations that name no environment are in the default environment, the prelude of classical logic, equality, the natural numbers, the Booleans, decisions, quotients, pairs, sums, options and lists, unless [SetTypeTheoryEnvironment]() sets another; the integers are a quotient in an environment of their own. [True](), [And]() and the other connectives are propositions or Booleans, as their types decide, and elaboration fills in instances and inserts coercions, as Lean's type classes and coercions do. The rules the kernel checks by are a value, [TypeTheoryRules](): the HoTT environment follows Martin-Löf type theory, without Prop, with univalence and the circle, the cubical environment follows cubical type theory, where univalence computes, and rules with quantities erase variables or use them at most once, as affine type theories do. [TypeTheoryProof]() and [TypeTheoryTactic]() build proofs step by step, and nothing a tactic does is trusted: the kernel checks the finished proof.

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
- [TypeTheoryHole]() a part of a proof left to give, as Lean's `sorry`, with an annotation such as a citation
- [TypeTheoryInductiveType]() declares an inductive type with its constructors, or mutually inductive types
- [TypeTheoryNaturalNumbers]() registers the natural numbers that literals belong to, and the operations the kernel computes on them
- [TypeTheoryRewriteRule]() makes an axiom compute, where the rules allow it
- [TypeTheoryQuotients]() declares the quotient types of Lean's kernel
- [TypeTheoryRules]() the rules an environment follows: the calculus of inductive constructions, with quotients, Martin-Löf type theory without Prop, or cubical type theory, and any with quantities that bound how many times code uses a variable
- [TypeTheoryTranslate]() moves the declarations of an environment to other rules, whose kernel checks them again

### Checking and computing

- [TypeTheoryType]() the type of a term
- [TypeTheoryCheck]() a term checked against a type, or a whole environment checked again
- [TypeTheoryAxiomClosure]() the axioms a term rests on, as Lean's `#print axioms`
- [TypeTheoryProofTree]() the natural-deduction derivation of a proof of propositional logic, drawn
- [TypeTheoryFormalize]() the declarations that make a Wolfram Language function a constant: a definition where its definitions translate, an axiom it computes otherwise
- [Expressions]() the expressions of the Wolfram Language, written as they are, as `a + b c`, `Unevaluated[e]` keeping one from computing, with [Atoms](), `"atom"`, [Construct](), [Arguments]() and [ExpressionEvaluate](), all in the prelude, where [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated]() rewrite with rules translated to matches
- [Strings]() the strings, each literal one where a string is expected, with signatures for the string functions; [FromString]() the value of a type written by a string, of the class `"IsString"`
- `"emptySequence"` and `"sequencePrepend"` the sequences of elements of different types, `Sequence[a, b]`, of the type `Sequence[A, B]`: the arguments a Wolfram Language function is applied to
- `A...` the sequences of any number of elements of `A`, written held as the Wolfram Language holds them, `Unevaluated[a, b, ...]`, and shown in brackets, `[a, b, ...]`, with [Prepend]() and `Unevaluated @@ l`: the arguments of an expression, which [Construct]() takes
- [Match]() the matches, lists of results, with [MatchValue]() one result, [MatchSum]() alternatives in order, [MatchBind]() parts in turn, [MatchPart]() a part of an expression and [MatchFirst]() the result the Wolfram Language applies
- [DefinitionallyEqualQ]() whether two terms are equal by computation
- [WeakHeadNormalForm]() a term reduced until its head can no longer reduce
- [NormalForm]() a term reduced in every part, under its binders too: its value, as Lean's `#reduce`
- [TypeTheoryExpression]() the expression of the Wolfram Language a term is written as, and of a normal form the value the kernel computes: a number, a list, a [Function]()

### Proofs

- [TypeTheoryProof]() a proof in progress, with its open goals
- [TypeTheoryTactic]() a tactic: `"Introduce"`, `"Exact"`, `"Apply"`, `"Reflexivity"`, `"Induction"`, `"Cases"`, `"Generalize"`, `"Constructor"`, `"Assumption"`, `"Hole"`, `"Rewrite"`, `"Change"`, `"RewriteRepeated"`, `"Decide"`, `"Ring"`, `"Classical"`, and the Wolfram oracles `"FindInstance"`, `"PolynomialReduce"`, `"LinearArithmetic"`, `"FindEquationalProof"` and `"SumOfSquares"`

### The prelude: logic and equality

- `"trueIntroduction"` the proof of [True](); `"falseElimination"` anything follows from [False]()
- `"andIntroduction"`, `"andEliminationLeft"`, `"andEliminationRight"` proving and using [And]()
- `"orIntroductionLeft"`, `"orIntroductionRight"` proving [Or]()
- `"equivalentIntroduction"`, `"equivalentForward"`, `"equivalentBackward"` proving and using [Equivalent]()
- `"equivalentReflexivity"`, `"equivalentSymmetry"`, `"equivalentTransitivity"` the laws of [Equivalent]()
- `"existsIntroduction"` proving [Exists]() with a witness
- `"equalityReflexivity"`, `"equalitySymmetry"`, `"equalityTransitivity"`, `"equalityCongruence"`, `"equalitySubstitution"` equality, with [Unequal]() its negation
- [Identity](), [Composition]() the identity function and composition

### The prelude: quotients

- [QuotientType]() the type of the classes of a relation, Lean's `Quot`
- [QuotientIntroduction]() the class of an element
- [QuotientLift]() a function that respects the relation, applied to classes, computing on a class
- [QuotientInduction]() a property of every class, from the classes of the elements

### The prelude: classical logic

- `"propositionalExtensionality"`, `"quotientSoundness"`, `"choice"` the axioms of the prelude, Lean's three
- `"functionExtensionality"` functions equal at every point are equal, proved from `"quotientSoundness"`
- `"nonempty"` proving [Nonempty](), which `"choice"` takes to an element
- `"subtype"` an element of a [Subtype](), with a proof of its property
- [ChosenWitness](), `"chosenWitnessProperty"` a witness chosen from a proof of [Exists](), and its property
- `"excludedMiddle"`, `"doubleNegationElimination"` classical logic, proved from the axioms

### The prelude: natural numbers

- [Naturals]() the natural numbers, [NonNegativeIntegers](), by a shorter name
- `"zero"`, `"successor"`, [NaturalNumberPredecessor]() the constructors of [NonNegativeIntegers](), and the number before
- [Plus](), [Times](), [Power](), [Subtract]() arithmetic, each by recursion on its second argument
- `"lessEqualReflexivity"`, `"lessEqualStep"` the constructors of [LessEqual](), with [Less](), [GreaterEqual]() and [Greater]() defined from it

### The prelude: Booleans

- [Booleans]() with the values `"false"` and `"true"` and the operations `"not"`, `"and"` and `"or"`, constants named by strings, which [False](), [True](), [Not](), [And]() and [Or]() stand for where a Boolean is expected

### The prelude: decisions

- [Decidable]() the class of decisions of a proposition, made with `"decidableTrue"` and `"decidableFalse"`
- [Decide]() the Boolean of a proposition's decision, found among the instances, and `"decideSoundness"` the proof from a decision that computes to `"true"`
- `"naturalNumberEqualityDecidable"`, `"lessEqualDecidable"` the instances deciding `==` and `<=` of natural numbers
- `"notDecidable"`, `"andDecidable"`, `"orDecidable"` the instances deciding [Not](), [And]() and [Or]() from the decisions of their parts
- `"trueDecidable"`, `"falseDecidable"`, `"booleanEqualityDecidable"` the instances deciding [True](), [False]() and `==` of Booleans

### The integers

- <code>[TypeTheoryEnvironment]()["Integers"]</code> the prelude with the integers, classes of pairs of natural numbers, where `+`, `*`, `-`, [Quotient]() and [Mod]() and the comparisons are the integers' wherever the types say so
- `"integerAdditionCommutativity"`, `"integerAdditionAssociativity"`, `"integerAdditionZero"`, `"integerAdditionNegation"`, `"integerSubtractionNegation"` addition and negation
- `"integerMultiplicationCommutativity"`, `"integerMultiplicationAssociativity"`, `"integerMultiplicationOne"`, `"integerDistributivity"` multiplication
- `"integerOfNaturalAddition"`, `"integerOfNaturalMultiplication"` the natural numbers among the integers, and `"integerLessEqualReflexivity"` the order
- `"integerEqualityDecidable"` the instance deciding `==` of integers
- `"integerSquareNonnegative"`, `"integerNonnegativeAddition"`, `"integerNonnegativeScaling"` squares, sums and natural multiples at least 0
- `"integerNonnegativeCancellation"`, `"integerLessEqualOfDifference"`, `"integerLessEqualOfMultiple"` inequalities from differences and their multiples, as `"SumOfSquares"` proves them
- `"integerOfNaturalLessEqual"` an inequality of natural numbers from that of their integers

### The rationals

- <code>[TypeTheoryEnvironment]()["Rationals"]</code> the integers with the rationals, classes of pairs of an integer and a natural number, where `+`, `*`, `-`, `/`, `^` and the comparisons are the rationals' wherever the types say so
- `"rationalAdditionCommutativity"`, `"rationalAdditionAssociativity"`, `"rationalAdditionZero"`, `"rationalAdditionNegation"`, `"rationalSubtractionNegation"` addition and negation
- `"rationalMultiplicationCommutativity"`, `"rationalMultiplicationAssociativity"`, `"rationalMultiplicationOne"`, `"rationalDistributivity"` multiplication
- `"rationalMultiplicationInverse"`, `"rationalInverseZero"` the inverse, which makes the rationals a field
- `"rationalOfIntegerAddition"`, `"rationalOfIntegerMultiplication"` the integers among the rationals
- `"rationalEqualityDecidable"` the instance deciding `==` of rationals
- `"rationalLessEqualReflexivity"`, `"rationalSquareNonnegative"` the order
- <code>[TypeTheoryEnvironment]()["Machine"]</code> the integers with the 64-bit integers of the compiler's typed entries, `"Integer64"` or `"MachineInteger"`, the compiler's names, a subtype of the integers in range, and `"machinePlus"`, `"machineTimes"`, `"machineQuotient"` and `"machineMod"`, whose results out of range are the leave `Failure["IntegerOverflow", <||>]`, and by 0 `Failure["DivideByZero", <||>]`

### Cubical type theory

- <code>[TypeTheoryEnvironment]()["Cubical"]</code> cubical type theory with a small library, where univalence computes
- [TypeTheoryCubical]() declares the interval, paths, transport, composition and Glue types
- [IntervalZero](), [IntervalOne](), [IntervalMeet](), [IntervalJoin](), [IntervalReverse]() the endpoints and operations of the interval
- [CubicalTransport]() transport along a line of types, constant where its face holds
- [CubicalComposition]() the lid of an open box, from its base and its sides over faces
- [GlueType](), [GlueIntroduction](), [GlueElimination]() types glued along equivalences, their elements, and the elements under them
- [DependentSum](), `"dependentPair"` the dependent sum of the cubical environment
- `"pathSymmetry"`, `"pathTransitivity"`, `"pathCongruence"`, `"pathFunctionExtensionality"`, `"pathInduction"` the operations on paths, as terms
- [Fiber](), [IsContractible](), `"isomorphismEquivalence"`, `"negationInvolution"` equivalences as functions with contractible fibers
- `"equivalenceToPath"` univalence, a path of Glue types along which transport applies the equivalence

### The prelude: pairs, sums, options and lists

- [CartesianProductType]() pairs, made with `"pair"`
- [DisjointUnionType]() sums, written `A | B`, made with `"left"` and `"right"`, or injected where the sum is expected
- [Failure]() failures, `Failure[tag, details]`: a computation that may fail has a value of `A | Failure`, written with [Enclose]() and [Confirm](), and [If]() branches by a [Decidable]() condition
- [Association]() associations, `<|k -> v, ...|>`, with [Lookup]() giving `V | Missing`, [Keys](), [Values](), [KeyExistsQ]() and [Length](); [Missing]() missing values, `Missing[reason, details...]`
- [Option]() optional values, `"none"` and `"some"`
- [List]() lists, built from `{}` by [Prepend](), with [Join](), [Length](), [Map](), [Append]() and [Reverse]()
- `"joinEmptyRight"`, `"joinAssociativity"`, `"lengthJoin"`, `"lengthMap"`, `"mapJoin"`, `"mapComposition"`, `"reverseJoin"`, `"reverseReverse"`, `"lengthReverse"` the laws of lists

### Homotopy type theory

- [Transport](), `"dependentCongruence"`, `"transportConstant"` carrying along paths, which compute on reflexivity
- [IsEquivalence](), [EquivalenceProof](), [Equivalence](), `"equivalenceIntroduction"`, `"identityEquivalence"` equivalences
- `"equalityToEquivalence"`, `"univalence"`, `"equivalenceToEquality"`, `"univalenceComputation"` univalence
- `"negationEquivalence"`, [IsSet](), `"universeNotSet"` the universe is not a set
- `"circleBase"`, `"circleLoop"`, `"circleInduction"`, `"circleInductionBase"`, `"circleInductionLoop"` the circle, a higher inductive type

### The prelude: theorems about the natural numbers

- `"additionZeroRight"`, `"additionZeroLeft"`, `"additionSuccessorRight"`, `"additionSuccessorLeft"`, `"additionCommutativity"`, `"additionAssociativity"` addition
- `"multiplicationZeroRight"`, `"multiplicationZeroLeft"`, `"multiplicationSuccessorRight"`, `"multiplicationSuccessorLeft"`, `"multiplicationOneRight"`, `"multiplicationOneLeft"` multiplication by small numbers
- `"multiplicationCommutativity"`, `"multiplicationAssociativity"`, `"multiplicationDistributivityLeft"`, `"multiplicationDistributivityRight"` the laws of multiplication
- `"subtractionZeroRight"`, `"subtractionZeroLeft"`, `"subtractionSuccessor"`, `"subtractionSelf"`, `"additionSubtractionCancellation"` subtraction, and `"multiplicationCancellation"` cancelling a positive factor
- `"powerZero"`, `"powerSuccessor"`, `"powerOne"`, `"powerAddition"` powers
- `"successorInjectivity"`, `"successorNotZero"` the successor
- `"lessEqualZero"`, `"lessEqualSuccessor"`, `"lessEqualPredecessor"`, `"lessEqualAddition"`, `"predecessorLessEqual"` the order and the successor
- `"lessEqualTransitivity"`, `"lessEqualAntisymmetry"`, `"lessIrreflexivity"`, `"successorNotLessEqualZero"`, `"lessEqualTotality"` the laws of the order
- `"additionMonotonicity"`, `"multiplicationMonotonicity"` sums and multiples of inequalities
