---
Template: Symbol
Name: NaturalNumberEqualityDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NaturalNumberEqualityDecidable
Keywords: [decidable, equality, natural numbers, decision, prelude]
SeeAlso: [LessEqualDecidable, Decidable, Decide, Naturals]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[NaturalNumberEqualityDecidable]()[*m*, *n*]</code> decides <code>*m* == *n*</code> for natural numbers *m* and *n*.

## Details & Options

- [NaturalNumberEqualityDecidable]() is a definition of the prelude, by recursion on *m* and then on *n*, as Lean's `Nat.decEq`.
- It computes on literals: [Decide]() of it gives the Boolean of the equation.

## Basic Examples

The type of [NaturalNumberEqualityDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NaturalNumberEqualityDecidable]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ Decidable[m == n] -->

---

2 == 2 is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[NaturalNumberEqualityDecidable[2, 2]]]]
```

<!-- => true -->

## Properties and Relations

[DecideSoundness]() turns the decision into a proof:

```wl
TypeTheoryCheck[TypeTheoryTerm[DecideSoundness[NaturalNumberEqualityDecidable[3, 3], EqualityReflexivity["true"]]]]
```

<!-- => 3 == 3 -->
