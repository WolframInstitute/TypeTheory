---
Template: Symbol
Name: BooleanNot
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/BooleanNot
Keywords: [Boolean, negation, not, Booleans, prelude]
SeeAlso: [BooleanAnd, BooleanOr, BooleanTrue, BooleanFalse, Not]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[BooleanNot]()[*a*]</code> is the negation of the Boolean *a*.

## Details & Options

- [BooleanNot]() is a definition of the prelude, by cases on *a*: the negation of [BooleanFalse]() is [BooleanTrue](), and of [BooleanTrue]() is [BooleanFalse](), as with Lean's `Bool`.
- <code>[Not]()[*a*]</code> and `!a` stand for it when *a* is a Boolean, and for the proposition [Not]() when *a* is a proposition.
- It shows as `!a`.

## Basic Examples

The type of [BooleanNot]():

```wl
TypeTheoryCheck[TypeTheoryTerm[BooleanNot]]
```

<!-- => 𝔹 → 𝔹 -->

---

The negation of a Boolean variable:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[b, Booleans]}, Not[b]]]]
```

<!-- => 𝔹 → 𝔹 -->

## Scope

Negating twice gives back every Boolean, proved by cases:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[b, Booleans]},
    InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Not[Not[t]] == t], EqualityReflexivity[BooleanFalse], EqualityReflexivity[BooleanTrue], b]
]]]
```

<!-- => ∀_b∶𝔹 !!b == b -->
