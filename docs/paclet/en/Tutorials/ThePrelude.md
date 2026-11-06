---
Template: TechNote
Name: ThePrelude
Title: The TypeTheory Prelude
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/ThePrelude
Keywords: [prelude, logic, equality, natural numbers, arithmetic, order, theorems, induction, Equivalent, LessEqual, Booleans, decidability, Decidable, quotients, pairs, sums, options, lists, classical logic, axioms, choice, excluded middle, constructive]
RelatedGuides: [TypeTheory]
RelatedTutorials: [InstancesAndCoercions, TypeTheoryIntroduction, HomotopyTypeTheory]
---

The prelude is the environment of every term, proof and list of declarations that names no other, unless [SetTypeTheoryEnvironment]() makes another the default. It declares the propositions of logic and their proofs, equality, a few functions, the natural numbers with their arithmetic, their order and the theorems about them, the Booleans, decisions of propositions, quotient types, pairs, sums, optional values, and lists with their operations and laws. It is classical: it assumes propositional extensionality, quotient soundness and choice, Lean's three axioms, and proves function extensionality and the excluded middle from them. Each theorem is a constant whose type is its statement, so it applies to arguments like a function. This tutorial goes through all of it.

## What the Prelude Declares

The prelude has inductive types, with their constructors and recursors, definitions, theorems and axioms:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Kinds"]
```

<!-- => <|"InductiveType" -> 23, "Constructor" -> 37, "Recursor" -> 24, "Definition" -> 66, "Quotient" -> 4, "Theorem" -> 72, "Axiom" -> 4|> -->

It is read when the paclet loads from a file saved with the paclet, whose declarations the kernel checked when it was saved, under the rules of the calculus of inductive constructions, [TypeTheoryRules](). Three of its constants are axioms, assumed and not proved:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Axioms"]
```

<!-- => {propositionalExtensionality, quotientSoundness, choice, ExpressionEvaluate} -->

## Propositions

[True]() has one proof, `"trueIntroduction"`, and [False]() none. [Not]() is a definition, which unfolds to an implication into [False]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

From [False](), `"falseElimination"` proves anything:

```wl
TypeTheoryType["falseElimination"]
```

<!-- => ∀_{a ∶ Prop} False ⇒ a -->

[And]() is proved by `"andIntroduction"` and used by `"andEliminationLeft"` and `"andEliminationRight"`; a proof of a conjunction is a structure, so `h[[1]]` and `h[[2]]` are its two parts. Conjunction is commutative:

```wl
TypeTheoryType[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, p && q]} |-> "andIntroduction"[h[[2]], h[[1]]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop (p ∧ q) ⇒ (q ∧ p) -->

`a && b && c` is read as `a && (b && c)`, as in Lean:

```wl
TypeTheoryCheck[TypeTheoryTerm["andIntroduction"["trueIntroduction", "andIntroduction"["trueIntroduction", "trueIntroduction"]]], TypeTheoryTerm[True && True && True]]
```

<!-- => Success["TypeChecked", ...] -->

[Or]() is proved by `"orIntroductionLeft"` or `"orIntroductionRight"`, and used by its recursor, one case for each side. Disjunction is commutative too:

```wl
TypeTheoryType[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, p || q]},
    InductiveRecursor[Or][
        Function[{Typed[t, p || q]}, q || p],
        Function[{Typed[x, p]}, "orIntroductionRight"[x]],
        Function[{Typed[y, q]}, "orIntroductionLeft"[y]],
        h
    ]
]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop (p ∨ q) ⇒ (q ∨ p) -->

[Equivalent](), shown as `⧦`, is proved by `"equivalentIntroduction"` from the two implications, and used by `"equivalentForward"` and `"equivalentBackward"`. It is reflexive, symmetric and transitive:

```wl
TypeTheoryType["equivalentTransitivity"]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} ∀_{c ∶ Prop} (a ⧦ b) ⇒ (b ⧦ c) ⇒ (a ⧦ c) -->

[Exists]() is proved by `"existsIntroduction"` from a witness and a proof about it:

```wl
TypeTheoryCheck[TypeTheoryTerm["existsIntroduction"[3, "equalityReflexivity"[6]]], TypeTheoryTerm[Exists[{Typed[n, Naturals]}, n + n == 6]]]
```

<!-- => Success["TypeChecked", ...] -->

## Equality

[Equal]() is proved by `"equalityReflexivity"`, and computation counts: `2 + 2 == 4` holds because both sides compute to `4`. `"equalitySymmetry"`, `"equalityTransitivity"`, `"equalityCongruence"` and `"equalitySubstitution"` are its laws; congruence applies a function to both sides:

```wl
TypeTheoryType["equalityCongruence"]
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
TypeTheoryType[Composition["successor", Identity]]
```

<!-- => ℕ → ℕ -->

Applied to 3, it gives the successor of 3:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Composition["successor", Identity][3]], TypeTheoryTerm[4]]
```

<!-- => True -->

## Quotients

The prelude has the quotient types of Lean's kernel, which [TypeTheoryQuotients]() declares: <code>[QuotientType]()[r]</code> is the type of the classes of a relation `r`, <code>[QuotientIntroduction]()[r, a]</code> is the class of `a`, [QuotientLift]() applies a function that respects `r` to a class, and [QuotientInduction]() proves a property of every class. Here is equality of natural numbers, as a relation:

```wl
equalNaturals = TypeTheoryTerm[Typed[{Typed[m, Naturals], Typed[n, Naturals]} |-> m == n, Naturals -> Naturals -> TypeUniverse[0]]]
```

<!-- => (m ∶ ℕ) (n ∶ ℕ) ↦ m == n ∶ ℕ → ℕ → Prop -->

The successor respects it, so it lifts to the classes, and the lift computes on a class, as in Lean's kernel:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[
    Function[{Typed[k, Naturals]}, k + 1],
    Function[{Typed[a, Naturals], Typed[b, Naturals], Typed[e, a == b]}, "equalityCongruence"[Typed[k, Naturals] |-> k + 1, e]],
    QuotientIntroduction[equalNaturals, 5]
]]]
```

<!-- => 6 -->

That the classes of related elements are equal is an axiom, `"quotientSoundness"`, one of the three below.

## The Natural Numbers

[NonNegativeIntegers](), shown as ℕ and written [Naturals]() for short, is an inductive type with the constructors `"zero"` and `"successor"`. It is registered as the natural numbers, so the literals `0`, `1`, `2`, ... are its elements, and the constructors show as `0` and `n + 1`:

```wl
TypeTheoryTerm["successor"["successor"["zero"]]]
```

<!-- => 0 + 1 + 1 -->

[NaturalNumberPredecessor]() is the number before, shown as `n - 1`; the number before `0` is `0`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[0]]]
```

<!-- => 0 -->

[Plus](), [Times](), [Power]() and [Subtract]() are defined by recursion on their second argument, as in Lean. They compute, and on literals the kernel computes them with Wolfram integers, as Lean's kernel does with GMP:

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
TypeTheoryType["additionCommutativity"]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + n == n + m -->

Distributivity:

```wl
TypeTheoryType["multiplicationDistributivityLeft"]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a (b + c) == a b + a c -->

Powers add their exponents:

```wl
TypeTheoryType["powerAddition"]
```

<!-- => ∀_m∶ℕ ∀_a∶ℕ ∀_b∶ℕ m^(a + b) == m^a m^b -->

The others are `"additionZeroRight"`, `"additionZeroLeft"`, `"additionSuccessorRight"`, `"additionSuccessorLeft"`, `"additionAssociativity"`, `"multiplicationZeroRight"`, `"multiplicationZeroLeft"`, `"multiplicationSuccessorRight"`, `"multiplicationSuccessorLeft"`, `"multiplicationOneRight"`, `"multiplicationOneLeft"`, `"multiplicationCommutativity"`, `"multiplicationDistributivityRight"`, `"multiplicationAssociativity"`, `"subtractionZeroRight"`, `"subtractionZeroLeft"`, `"subtractionSuccessor"`, `"subtractionSelf"`, `"additionSubtractionCancellation"`, `"multiplicationCancellation"`, `"powerZero"`, `"powerSuccessor"` and `"powerOne"`, with `"successorInjectivity"` and `"successorNotZero"`.

A theorem applies like a function. Here `n * 2` computes to `0 + n + n`, and `"additionZeroLeft"` under `"equalityCongruence"` finishes a proof that doubling is adding:

```wl
doubling = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n * 2 == n + n], {
    "Introduce"[n],
    "Exact"["equalityCongruence"[Typed[x, Naturals] |-> x + n, "additionZeroLeft"[n]]]
}]
```

<!-- => Proof complete -->

## Order

[LessEqual](), written `m <= n`, is inductive as in Lean: `"lessEqualReflexivity"` proves `n <= n`, and `"lessEqualStep"` goes from `n <= m` to `n <= m + 1`:

```wl
TypeTheoryCheck[TypeTheoryTerm["lessEqualStep"["lessEqualStep"["lessEqualReflexivity"]]], TypeTheoryTerm[2 <= 4]]
```

<!-- => Success["TypeChecked", ...] -->

[Less](), [GreaterEqual]() and [Greater]() are defined from it: `m < n` is `m + 1 <= n`. So `"lessEqualAddition"` proves strict inequalities too:

```wl
TypeTheoryCheck[TypeTheoryTerm["lessEqualAddition"[4, 2]], TypeTheoryTerm[3 < 6]]
```

<!-- => Success["TypeChecked", ...] -->

The order is reflexive, transitive and antisymmetric, and `n < n` never holds:

```wl
TypeTheoryType["lessEqualAntisymmetry"]
```

<!-- => ∀_{a ∶ ℕ} ∀_{b ∶ ℕ} a ≤ b ⇒ b ≤ a ⇒ a == b -->

The other theorems are `"lessEqualZero"`, `"lessEqualSuccessor"`, `"lessEqualPredecessor"`, `"lessEqualTransitivity"`, `"lessIrreflexivity"`, `"successorNotLessEqualZero"`, `"predecessorLessEqual"` and `"lessEqualTotality"`, and `"additionMonotonicity"` and `"multiplicationMonotonicity"`, which add and multiply inequalities.

## Booleans

[Booleans]() has two values, `"false"` and `"true"`, and `"not"`, `"and"` and `"or"` compute with them by cases on their first argument, as with Lean's `Bool`. These constants are named by strings, and you rarely write them: where a Boolean is expected, [True](), [False](), [Not](), [And]() and [Or]() stand for them, and so do `!`, `&&` and `||`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[True && Not[False], Booleans]]]
```

<!-- => true -->

A Boolean shows in lower case, and its operations as Lean writes them, which tells them apart from the propositions. The arguments decide too: on Booleans, `||` is the operation on Booleans, and on propositions it is the disjunction:

```wl
TypeTheoryType[Typed[b, Booleans] |-> b || False]
```

<!-- => 𝔹 → 𝔹 -->

When nothing decides, a term is ambiguous: here both sides could be propositions, or both Booleans:

```wl
TypeTheoryType[True == False]
```

<!-- => Failure["Ambiguous", ...] -->

[Typed]() says which it is, and the other side follows:

```wl
TypeTheoryType[Typed[True, Booleans] == False]
```

<!-- => Prop -->

A statement about every Boolean is proved by cases, with the recursor of [Booleans]():

```wl
TypeTheoryType[Function[{Typed[b, Booleans]},
    InductiveRecursor[Booleans][Typed[t, Booleans] |-> Not[Not[t]] == t, "equalityReflexivity"[False], "equalityReflexivity"[True], b]
]]
```

<!-- => ∀_b∶𝔹 !!b == b -->

## Decisions

A decision of a proposition `p`, an element of <code>[Decidable]()[p]</code>, is a proof of `p` or a proof of its negation, made with `"decidableTrue"` or `"decidableFalse"`. It is data, so it computes, and <code>[Decide]()[p]</code> turns the decision of `p` into a Boolean. [Decidable]() is a class, as in Lean: <code>[Decide]()[p]</code> finds the decision among its instances. The prelude's instances decide equations and inequalities of natural numbers with `"naturalNumberEqualityDecidable"` and `"lessEqualDecidable"`, combine decisions with `"notDecidable"`, `"andDecidable"` and `"orDecidable"`, and decide [True](), [False]() and equations of Booleans. The first two are what the Boolean comparisons `"equal"` and `"lessEqual"` give, as Lean's `Nat.decEq` is what `Nat.beq` gives; the kernel computes the comparisons on literals with integers, so deciding literals of any size is one step:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[1 <= 2 && 2 == 2]]]
```

<!-- => true -->

`"decideSoundness"` turns a decision that computes to `"true"` into a proof of the proposition it is checked against, which the kernel checks by computing:

```wl
TypeTheoryType[Typed["decideSoundness"["equalityReflexivity"["true"]], 1 <= 2 && 2 == 2]]
```

<!-- => 1 ≤ 2 ∧ 2 == 2 -->

The tactic `"Decide"` finds the decision of a closed statement and proves it so:

```wl
TypeTheoryProof[And[3 + 4 == 7, Or[5 <= 2, Not[2 == 3]]], {"Decide"}]
```

<!-- => Proof complete -->

The tutorial *Instances and Coercions* shows how an environment adds instances of its own.

## Pairs, Sums and Options

<code>[CartesianProductType]()[α, β]</code> is the type of pairs, made with `"pair"`, whose fields are `p[[1]]` and `p[[2]]`; <code>[DisjointUnionType]()[α, β]</code> has the elements of `α` on the left, with `"left"`, and those of `β` on the right, with `"right"`; and <code>[Option]()[α]</code> has `"none"` and the values <code>"some"[x]</code>. They are laid out as Lean's `Prod`, `Sum` and `Option`:

```wl
WeakHeadNormalForm[TypeTheoryTerm["pair"[2, 3][[1]]]]
```

<!-- => 2 -->

## List

<code>[List]()[α]</code> is the type of finite lists, built from `{}` by `Prepend[x][l]`, the operator form of [Prepend]() applied, as Lean builds `List` from `nil` and `cons x l`; `Prepend[l, x]` is the same list. [Join](), [Length](), [Map](), [Append]() and [Reverse]() are defined on them, each by recursion on its first list, and compute:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Reverse[Prepend[1][Prepend[2][{}]]]], TypeTheoryTerm[Prepend[2][Prepend[1][{}]]]]
```

<!-- => True -->

Their laws are theorems: `"joinEmptyRight"`, `"joinAssociativity"`, `"lengthJoin"`, `"lengthMap"`, `"mapJoin"`, `"mapComposition"`, `"reverseJoin"`, `"reverseReverse"` and `"lengthReverse"`. Each is proved by recursion on a list, and tactics prove such laws too: `"Induction"` splits a list into the empty list and a list with a first element, and `"Simplify"` unfolds a definition where its list is one of these, folding the recursive call back, before it rewrites with the induction hypothesis and the laws of arithmetic:

```wl
lengthJoin = TypeTheoryProof[ForAll[{Typed[a, {Naturals}], Typed[b, {Naturals}]}, Length[Join[a, b]] == Length[a] + Length[b]], {
    "Introduce"[a, b],
    "Induction"[a],
    "Simplify"[{Join, Length, "additionZeroLeft"}],
    "Introduce"[x, rest, ih],
    "Simplify"[{Join, Length, ih, "additionSuccessorLeft"}]
}]
```

<!-- => Proof complete -->

## Classical Logic

The prelude's three axioms are those of Lean's library. `"propositionalExtensionality"` makes equivalent propositions equal:

```wl
TypeTheoryType["propositionalExtensionality"["equivalentIntroduction"[Typed[h, True] |-> "andIntroduction"[h, h], Typed[h, True && True] |-> "andEliminationLeft"[h]]]]
```

<!-- => True == (True ∧ True) -->

`"quotientSoundness"` makes the classes of related elements equal. From it the prelude proves `"functionExtensionality"`, as Lean proves `funext`: functions that agree on every argument are equal:

```wl
TypeTheoryType["functionExtensionality"["additionZeroLeft"]]
```

<!-- => ((n∶ℕ) ↦ 0 + n) == ((n∶ℕ) ↦ n) -->

`"choice"` takes a proof that a type has an element, a proof of [Nonempty](), to an element of it. Being an axiom, it does not compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm["choice"["nonempty"[3]]]]
```

<!-- => choice[nonempty[3]] -->

A proof of an existential statement cannot be taken apart to give its witness as data. [ChosenWitness]() chooses one instead, an element of a [Subtype]() that holds a witness and its proof, and `"chosenWitnessProperty"` proves that the witness has the property:

```wl
TypeTheoryType[Typed[h, Exists[Typed[n, Naturals] |-> n + n == 6]] |-> "chosenWitnessProperty"[h]]
```

<!-- => ∀_h∶∃_n∶ℕ n + n == 6 ChosenWitness[h] + ChosenWitness[h] == 6 -->

From the three axioms the prelude proves the excluded middle, by Diaconescu's argument, as Lean does:

```wl
TypeTheoryType["excludedMiddle"]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

So every proposition is [True]() or [False](), by cases on the excluded middle and propositional extensionality:

```wl
TypeTheoryType[Function[{Typed[p, TypeUniverse[0]]},
    InductiveRecursor[Or][
        Function[{Typed[t, p || Not[p]]}, p == True || p == False],
        Function[{Typed[h, p]}, "orIntroductionLeft"["propositionalExtensionality"["equivalentIntroduction"[Typed[k, p] |-> "trueIntroduction", Typed[k, True] |-> h]]]],
        Function[{Typed[h, Not[p]]}, "orIntroductionRight"["propositionalExtensionality"["equivalentIntroduction"[h, Typed[k, False] |-> "falseElimination"[k]]]]],
        "excludedMiddle"[p]
    ]
]]
```

<!-- => ∀_p∶Prop (p == True ∨ p == False) -->

`"doubleNegationElimination"` is proved from the excluded middle too.

## The Constructive Environment

<code>[TypeTheoryEnvironment]()["Constructive"]</code> is the prelude without its axioms and the declarations that need them:

```wl
constructive = TypeTheoryEnvironment["Constructive"]
```

<!-- => TypeTheoryEnvironment summary box: 155 constants -->

It has no axioms:

```wl
Information[constructive, "Axioms"]
```

<!-- => {} -->

And no excluded middle:

```wl
KeyExistsQ[constructive, "excludedMiddle"]
```

<!-- => False -->

Whatever is proved in it uses no axiom. Other axioms can be assumed there with [TypeTheoryAxiom](), such as the excluded middle without choice:

```wl
excludedMiddle = TypeTheoryEnvironment[constructive, {TypeTheoryAxiom["excludedMiddle", ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]}]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->

Its one axiom:

```wl
Information[excludedMiddle, "Axioms"]
```

<!-- => {excludedMiddle} -->

## What the Prelude Does Not Have Yet

Lean's library is much larger than this prelude. The integers and the rationals are in environments of their own, <code>[TypeTheoryEnvironment]()["Integers"]</code> and <code>[TypeTheoryEnvironment]()["Rationals"]</code>. The kernel has what Lean's library needs of it, mutual and nested inductive types and quotients among it, so LeanLink imports that library itself: the tutorial *Mathlib in TypeTheory* works with Mathlib's natural numbers.

## Theorems

Every theorem of the prelude is a constant named by a string, as its constructors are, so no symbol of the paclet stands for it outside a term: `"equalityReflexivity"[2]` proves `2 == 2`, and `TypeTheoryTactic["Rewrite", "additionCommutativity"]` rewrites with a law. These are all of them, each with its statement, in the order the prelude declares them:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Theorems"]
```

<!-- => <|"falseElimination" -> ∀_{a∶Prop} False ⇒ a, "andEliminationLeft" -> ..., ...|>, 72 theorems -->

A theorem is applied as any constant is, its implicit arguments found by elaboration:

```wl
TypeTheoryType["additionCommutativity"[2, 3]]
```

<!-- => 2 + 3 == 3 + 2 -->
