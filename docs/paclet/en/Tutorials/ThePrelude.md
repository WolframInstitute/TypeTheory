---
Template: TechNote
Name: ThePrelude
Title: The TypeTheory Prelude
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/ThePrelude
Keywords: [prelude, logic, equality, natural numbers, arithmetic, order, theorems, induction, Equivalent, LessEqual, Booleans, classical logic, axioms, choice, excluded middle, constructive]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, HomotopyTypeTheory]
---

The prelude is the environment of every term, proof and list of declarations that names no other. It declares the propositions of logic and their proofs, equality, a few functions, the natural numbers with their arithmetic, their order and the theorems about them, and the Booleans. It is classical: it assumes propositional extensionality, function extensionality and choice, and proves the excluded middle from them. Each theorem is a constant whose type is its statement, so it applies to arguments like a function. This tutorial goes through all of it.

## What the Prelude Declares

The prelude has inductive types, with their constructors and recursors, definitions, theorems and axioms:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Kinds"]
```

<!-- => <|"InductiveType" -> 12, "Constructor" -> 15, "Recursor" -> 12, "Definition" -> 16, "Theorem" -> 51, "Axiom" -> 3|> -->

It is built when the paclet loads, and every declaration in it is checked by the kernel, under the rules of the calculus of inductive constructions, [TypeTheoryRules](). Three of its constants are axioms, assumed and not proved:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Axioms"]
```

<!-- => {PropositionalExtensionality, FunctionExtensionality, Choice} -->

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

<!-- => Success["TypeChecked", ...] -->

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
TypeTheoryCheck[TypeTheoryTerm[ExistsIntroduction[3, EqualityReflexivity[6]]], TypeTheoryTerm[Exists[{Typed[n, Naturals]}, n + n == 6]]]
```

<!-- => Success["TypeChecked", ...] -->

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

[NonNegativeIntegers](), shown as ℕ and written [Naturals]() for short, is an inductive type with the constructors [NaturalNumberZero]() and [NaturalNumberSuccessor](). It is registered as the natural numbers, so the literals `0`, `1`, `2`, ... are its elements, and the constructors show as `0` and `n + 1`:

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
doubling = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n * 2 == n + n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Exact", EqualityCongruence[Function[{Typed[x, Naturals]}, x + n], AdditionZeroLeft[n]]]
}]
```

<!-- => Proof complete -->

## Order

[LessEqual](), written `m <= n`, is inductive as in Lean: [LessEqualReflexivity]() proves `n <= n`, and [LessEqualStep]() goes from `n <= m` to `n <= m + 1`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualStep[LessEqualStep[LessEqualReflexivity]]], TypeTheoryTerm[2 <= 4]]
```

<!-- => Success["TypeChecked", ...] -->

[Less](), [GreaterEqual]() and [Greater]() are defined from it: `m < n` is `m + 1 <= n`. So [LessEqualAddition]() proves strict inequalities too:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition[4, 2]], TypeTheoryTerm[3 < 6]]
```

<!-- => Success["TypeChecked", ...] -->

The order is reflexive, transitive and antisymmetric, and `n < n` never holds:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAntisymmetry]]
```

<!-- => ∀_{a ∶ ℕ} ∀_{b ∶ ℕ} a ≤ b ⇒ b ≤ a ⇒ a == b -->

The other theorems are [LessEqualZero](), [LessEqualSuccessor](), [LessEqualPredecessor](), [LessEqualTransitivity](), [LessIrreflexivity](), [SuccessorNotLessEqualZero]() and [PredecessorLessEqual]().

## Booleans

[Booleans]() has two values, `"false"` and `"true"`, and `"not"`, `"and"` and `"or"` compute with them by cases on their first argument, as with Lean's `Bool`. These constants are named by strings, and you rarely write them: where a Boolean is expected, [True](), [False](), [Not](), [And]() and [Or]() stand for them, and so do `!`, `&&` and `||`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[True && Not[False], Booleans]]]
```

<!-- => true -->

A Boolean shows in lower case, and its operations as Lean writes them, which tells them apart from the propositions. The arguments decide too: on Booleans, `||` is the operation on Booleans, and on propositions it is the disjunction:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[b, Booleans]}, b || False]]]
```

<!-- => 𝔹 → 𝔹 -->

When nothing decides, a term is ambiguous: here both sides could be propositions, or both Booleans:

```wl
TypeOf[TypeTheoryTerm[True == False]]
```

<!-- => Failure["Ambiguous", ...] -->

[Typed]() says which it is, and the other side follows:

```wl
TypeOf[TypeTheoryTerm[Typed[True, Booleans] == False]]
```

<!-- => Prop -->

A statement about every Boolean is proved by cases, with the recursor of [Booleans]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[b, Booleans]},
    InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Not[Not[t]] == t], EqualityReflexivity[False], EqualityReflexivity[True], b]
]]]
```

<!-- => ∀_b∶𝔹 !!b == b -->

## Classical Logic

The prelude's three axioms are those of Lean's library. [PropositionalExtensionality]() makes equivalent propositions equal:

```wl
TypeTheoryCheck[TypeTheoryTerm[PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[h, True]}, AndIntroduction[h, h]], Function[{Typed[h, True && True]}, AndEliminationLeft[h]]]]]]
```

<!-- => True == (True ∧ True) -->

[FunctionExtensionality]() makes functions equal that agree on every argument. Lean proves it from quotients, which the kernel does not have, so here it is an axiom:

```wl
TypeTheoryCheck[TypeTheoryTerm[FunctionExtensionality[AdditionZeroLeft]]]
```

<!-- => ((n∶ℕ) ↦ 0 + n) == ((n∶ℕ) ↦ n) -->

[Choice]() takes a proof that a type has an element, a proof of [Nonempty](), to an element of it. Being an axiom, it does not compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Choice[NonemptyIntroduction[3]]]]
```

<!-- => Choice[NonemptyIntroduction[3]] -->

A proof of an existential statement cannot be taken apart to give its witness as data. [ChosenWitness]() chooses one instead, an element of a [Subtype]() that holds a witness and its proof, and [ChosenWitnessProperty]() proves that the witness has the property:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Exists[Function[{Typed[n, Naturals]}, n + n == 6]]]}, ChosenWitnessProperty[h]]]]
```

<!-- => ∀_h∶∃_n∶ℕ n + n == 6 ChosenWitness[h] + ChosenWitness[h] == 6 -->

From the three axioms the prelude proves the excluded middle, by Diaconescu's argument, as Lean does:

```wl
TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle]]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

So every proposition is [True]() or [False](), by cases on the excluded middle and propositional extensionality:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]]},
    InductiveRecursor[Or][
        Function[{Typed[t, p || Not[p]]}, p == True || p == False],
        Function[{Typed[h, p]}, OrIntroductionLeft[PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[k, p]}, TrueIntroduction], Function[{Typed[k, True]}, h]]]]],
        Function[{Typed[h, Not[p]]}, OrIntroductionRight[PropositionalExtensionality[EquivalentIntroduction[h, Function[{Typed[k, False]}, FalseElimination[k]]]]]],
        ExcludedMiddle[p]
    ]
]]]
```

<!-- => ∀_p∶Prop (p == True ∨ p == False) -->

[DoubleNegationElimination]() is proved from the excluded middle too.

## The Constructive Environment

<code>[TypeTheoryEnvironment]()["Constructive"]</code> is the prelude without its axioms and the declarations that need them:

```wl
constructive = TypeTheoryEnvironment["Constructive"];
{Information[constructive, "Axioms"], KeyExistsQ[constructive, ExcludedMiddle]}
```

<!-- => {{}, False} -->

Whatever is proved in it uses no axiom. Other axioms can be assumed there with [TypeTheoryAxiom](), such as the excluded middle without choice:

```wl
excludedMiddle = TypeTheoryEnvironment[constructive, {TypeTheoryAxiom[ExcludedMiddle, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]}];
Information[excludedMiddle, "Axioms"]
```

<!-- => {ExcludedMiddle} -->

## What the Prelude Does Not Have Yet

Lean's library is much larger than this prelude. Decidability, pairs, sums, options and lists, and type classes are not here yet, and the kernel does not yet have mutual and nested inductive types or quotients, which parts of Lean's library need.
