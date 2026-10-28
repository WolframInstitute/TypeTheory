---
Template: Symbol
Name: LessEqualAddition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualAddition
Keywords: [less, equal, addition, prelude, natural numbers]
SeeAlso: [LessEqualZero, LessEqualStep, Less]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualAddition]()[*n*, *m*]</code> proves <code>*n* <= *n* + *m*</code>.

## Details & Options

- [LessEqualAddition]() is a theorem of the prelude, proved by induction on *m*.
- <code>*n* < *m*</code> is <code>[Less]()[*n*, *m*]</code>, which unfolds to <code>*n* + 1 <= *m*</code>, so [LessEqualAddition]() also proves strict inequalities.

## Basic Examples

The statement of [LessEqualAddition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition]]
```

<!-- => ∀_n∶ℕ ∀_m∶ℕ n ≤ n + m -->

---

`3 < 6` unfolds to `4 <= 6`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition[4, 2]], TypeTheoryTerm[3 < 6]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The tactic `"Apply"` finds *n* and *m* from the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, x <= x + y * y], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", LessEqualAddition]
}]
```

<!-- => Proof complete -->

---

At `x + 1` it proves a strict inequality, since `x < x + 1 + y` unfolds to `x + 1 <= x + 1 + y`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals]}, LessEqualAddition[x + 1, y]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, x < x + 1 + y]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

With [AdditionCommutativity](), the number added can come first:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, y <= x + y], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", AdditionCommutativity[x, y]],
    TypeTheoryTactic["Exact", LessEqualAddition[y, x]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The number added must come second, since `y + x` is not `x + y` by computation, so `x <= y + x` is not an instance:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals]}, LessEqualAddition[x, y]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, x <= y + x]]
]
```

<!-- => Failure["TypeMismatch", ...] -->
