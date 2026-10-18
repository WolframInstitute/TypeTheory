---
Template: TechNote
Name: ThePrelude
Title: The TypeTheory Prelude
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/ThePrelude
Keywords: [prelude, logic, equality, natural numbers, arithmetic, order, theorems, induction, Equivalent, LessEqual]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction]
---

The prelude is the environment of every term, proof and list of declarations that names no other. It declares the propositions of logic and their proofs, equality, a few functions, and the natural numbers with their arithmetic, their order and the theorems about them. Each theorem is a constant whose type is its statement, so it applies to arguments like a function. This tutorial goes through all of it.

## What the Prelude Declares

The prelude has inductive types, with their constructors and recursors, definitions and theorems:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Kinds"]
```

<!-- => <|"InductiveType" -> 9, "Constructor" -> 11, "Recursor" -> 9, "Definition" -> 12, "Theorem" -> 48|> -->

It is built when the paclet loads, and every declaration in it is checked by the kernel; nothing in it is an axiom:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Axioms"]
```

<!-- => {} -->

## Propositions

[True]() has one proof, [TrueIntroduction](), and [False]() none. [Not]() is a definition, which unfolds to an implication into [False]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

From [False](), [FalseElimination]() proves anything:

```wl
TypeTheoryCheck[TypeTheoryTerm[FalseElimination]]
```

<!-- => ∀_{a ∶ Prop} False ⇒ a -->

[And]() is proved by [AndIntroduction]() and used by [AndEliminationLeft]() and [AndEliminationRight](); a proof of a conjunction is a structure, so `h[[1]]` and `h[[2]]` are its two parts. Conjunction is commutative:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, p && q]}, AndIntroduction[h[[2]], h[[1]]]]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop (p ∧ q) ⇒ (q ∧ p) -->

`a && b && c` is read as `a && (b && c)`, as in Lean:

```wl
TypeTheoryCheck[TypeTheoryTerm[AndIntroduction[TrueIntroduction, AndIntroduction[TrueIntroduction, TrueIntroduction]]], TypeTheoryTerm[True && True && True]]
```

<!-- => True -->

[Or]() is proved by [OrIntroductionLeft]() or [OrIntroductionRight](), and used by its recursor, one case for each side. Disjunction is commutative too:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, p || q]},
    InductiveRecursor[Or][
        Function[{Typed[t, p || q]}, q || p],
        Function[{Typed[x, p]}, OrIntroductionRight[x]],
        Function[{Typed[y, q]}, OrIntroductionLeft[y]],
        h
    ]
]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop (p ∨ q) ⇒ (q ∨ p) -->

[Equivalent](), shown as `⧦`, is proved by [EquivalentIntroduction]() from the two implications, and used by [EquivalentForward]() and [EquivalentBackward](). It is reflexive, symmetric and transitive:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentTransitivity]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} ∀_{c ∶ Prop} (a ⧦ b) ⇒ (b ⧦ c) ⇒ (a ⧦ c) -->

[Exists]() is proved by [ExistsIntroduction]() from a witness and a proof about it:

```wl
TypeTheoryCheck[TypeTheoryTerm[ExistsIntroduction[3, EqualityReflexivity[6]]], TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 6]]]
```

<!-- => True -->

## Equality

[Equal]() is proved by [EqualityReflexivity](), and computation counts: `2 + 2 == 4` holds because both sides compute to `4`. [EqualitySymmetry](), [EqualityTransitivity](), [EqualityCongruence]() and [EqualitySubstitution]() are its laws; congruence applies a function to both sides:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityCongruence]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{β ∶ Sort v} ∀_{x ∶ α} ∀_{y ∶ α} ∀_f∶α → β x == y ⇒ f[x] == f[y] -->

[Unequal](), written `x != y`, unfolds to <code>[Not]()[*x* == *y*]</code>, which unfolds in turn to an implication into [False]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[3 != 4]]
```

<!-- => 3 == 4 ⇒ False -->

## Functions

[Identity]() is the polymorphic identity function, and [Composition]() composes two functions:

```wl
TypeOf[TypeTheoryTerm[Composition[NaturalNumberSuccessor, Identity]]]
```

<!-- => ℕ → ℕ -->

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Composition[NaturalNumberSuccessor, Identity][3]], TypeTheoryTerm[4]]
```

<!-- => True -->

## The Natural Numbers

[NonNegativeIntegers](), shown as ℕ, is an inductive type with the constructors [NaturalNumberZero]() and [NaturalNumberSuccessor](). It is registered as the natural numbers, so the literals `0`, `1`, `2`, ... are its elements, and the constructors show as `0` and `n + 1`:

```wl
TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberSuccessor[NaturalNumberZero]]]
```

<!-- => 0 + 1 + 1 -->

[NaturalNumberPredecessor]() is the number before, shown as `n - 1`; the number before `0` is `0`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[0]]]
```

<!-- => 0 -->

[Plus](), [Times](), [Power]() and [Subtract]() are defined by recursion on their second argument, as in Lean. They compute; addition of literals is done with Wolfram integers:

```wl
WeakHeadNormalForm[TypeTheoryTerm[3 * 4 + 2^3 - 5]]
```

<!-- => 15 -->

Subtraction stops at `0`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[3 - 5]]
```

<!-- => 0 -->

The recursor [InductiveRecursor]() of the natural numbers defines functions by recursion, and proves statements by induction; the `"Induction"` tactic builds it.

## The Laws of Arithmetic

The prelude proves the laws of addition, multiplication, subtraction and powers. Commutativity of addition:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionCommutativity]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + n == n + m -->

Distributivity:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityLeft]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a (b + c) == a b + a c -->

Powers add their exponents:

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerAddition]]
```

<!-- => ∀_m∶ℕ ∀_a∶ℕ ∀_b∶ℕ m^(a + b) == m^a m^b -->

The others are [AdditionZeroRight](), [AdditionZeroLeft](), [AdditionSuccessorRight](), [AdditionSuccessorLeft](), [AdditionAssociativity](), [MultiplicationZeroRight](), [MultiplicationZeroLeft](), [MultiplicationSuccessorRight](), [MultiplicationSuccessorLeft](), [MultiplicationOneRight](), [MultiplicationOneLeft](), [MultiplicationCommutativity](), [MultiplicationDistributivityRight](), [MultiplicationAssociativity](), [SubtractionZeroRight](), [SubtractionZeroLeft](), [SubtractionSuccessor](), [SubtractionSelf](), [AdditionSubtractionCancellation](), [PowerZero](), [PowerSuccessor]() and [PowerOne](), with [SuccessorInjectivity]() and [SuccessorNotZero]().

A theorem applies like a function. Here `n * 2` computes to `0 + n + n`, and [AdditionZeroLeft]() under [EqualityCongruence]() finishes a proof that doubling is adding:

```wl
doubling = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n * 2 == n + n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Exact", EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, x + n], AdditionZeroLeft[n]]]
}]
```

<!-- => Proof complete -->

## Order

[LessEqual](), written `m <= n`, is inductive as in Lean: [LessEqualReflexivity]() proves `n <= n`, and [LessEqualStep]() goes from `n <= m` to `n <= m + 1`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualStep[LessEqualStep[LessEqualReflexivity]]], TypeTheoryTerm[2 <= 4]]
```

<!-- => True -->

[Less](), [GreaterEqual]() and [Greater]() are defined from it: `m < n` is `m + 1 <= n`. So [LessEqualAddition]() proves strict inequalities too:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition[4, 2]], TypeTheoryTerm[3 < 6]]
```

<!-- => True -->

The order is reflexive, transitive and antisymmetric, and `n < n` never holds:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAntisymmetry]]
```

<!-- => ∀_{a ∶ ℕ} ∀_{b ∶ ℕ} a ≤ b ⇒ b ≤ a ⇒ a == b -->

The other theorems are [LessEqualZero](), [LessEqualSuccessor](), [LessEqualPredecessor](), [LessEqualTransitivity](), [LessIrreflexivity](), [SuccessorNotLessEqualZero]() and [PredecessorLessEqual]().

## What the Prelude Does Not Have Yet

Lean's library is much larger than this prelude. Booleans and decidability, pairs, sums, options and lists, and type classes are not here yet, and the kernel does not yet have mutual and nested inductive types or quotients, which parts of Lean's library need. Lean's axioms of propositional extensionality and choice are not assumed: everything here is proved.
