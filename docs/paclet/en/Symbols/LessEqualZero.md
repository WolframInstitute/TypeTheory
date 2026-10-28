---
Template: Symbol
Name: LessEqualZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualZero
Keywords: [less, equal, zero, prelude, natural numbers]
SeeAlso: [LessEqualReflexivity, LessEqualStep, SuccessorNotLessEqualZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualZero]()[*n*]</code> proves <code>0 <= *n*</code>.

## Details & Options

- [LessEqualZero]() is a theorem of the prelude, proved by induction on *n*: <code>[LessEqualStep]()[*h*]</code> at each successor.

## Basic Examples

The statement of [LessEqualZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualZero]]
```

<!-- => ∀_n∶ℕ 0 ≤ n -->

---

`7 >= 0` is <code>[GreaterEqual]()[7, 0]</code>, which unfolds to `0 <= 7`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualZero[7]], TypeTheoryTerm[7 >= 0]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The tactic `"Apply"` finds *n* from the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, 0 <= x * y], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", LessEqualZero]
}]
```

<!-- => Proof complete -->

---

With [LessEqualSuccessor](), every successor is positive, since `0 < n + 1` unfolds to `0 + 1 <= n + 1`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[n, Naturals]}, LessEqualSuccessor[LessEqualZero[n]]]],
    TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, 0 < n + 1]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

A proof by induction builds it as the prelude does, with [LessEqualReflexivity]() at 0, which `"Constructor"` applies, and [LessEqualStep]() at each successor:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 <= n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Induction", n],
    TypeTheoryTactic["Constructor"],
    TypeTheoryTactic["Introduce", k, ih],
    TypeTheoryTactic["Apply", LessEqualStep],
    TypeTheoryTactic["Exact", ih]
}]
```

<!-- => Proof complete -->
