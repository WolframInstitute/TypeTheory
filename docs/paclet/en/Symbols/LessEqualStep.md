---
Template: Symbol
Name: LessEqualStep
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualStep
Keywords: [less, equal, step, prelude, natural numbers]
SeeAlso: [LessEqualReflexivity, LessEqualAddition, LessEqualTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualStep]()[*h*]</code> proves <code>*n* <= *m* + 1</code> from a proof *h* of <code>*n* <= *m*</code>.

## Details & Options

- [LessEqualStep]() is the second constructor of [LessEqual](), as Lean's `Nat.le.step`.
- *n* and *m* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [LessEqualStep]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualStep]]
```

<!-- => ∀_{n∶ℕ} ∀_{m∶ℕ} n ≤ m ⇒ n ≤ m + 1 -->

---

`3 <= 5`, two steps up from `3 <= 3`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualStep[LessEqualStep[LessEqualReflexivity]]], TypeTheoryTerm[3 <= 5]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The tactic `"Constructor"` applies it where [LessEqualReflexivity]() does not, and leaves the inequality one lower:

```wl
TypeTheoryProof[3 <= 5, {TypeTheoryTactic["Constructor"]}]
```

<!-- => Proof, 1 goal: ⊢ 3 ≤ 4 -->

---

For a variable, two steps prove `x <= x + 2`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals]}, LessEqualStep[LessEqualStep[LessEqualReflexivity]]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals]}, x <= x + 2]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

The tactic `"Decide"` proves an inequality of literals by computation, without building the steps:

```wl
TypeTheoryProof[3 <= 5, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

It adds 1 on the right as `m + 1`, and `1 + y` is not that by computation:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, LessEqualStep[h]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, x <= 1 + y]]]
]
```

<!-- => Failure["TypeMismatch", ...] -->
