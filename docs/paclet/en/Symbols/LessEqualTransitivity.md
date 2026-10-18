---
Template: Symbol
Name: LessEqualTransitivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualTransitivity
Keywords: [less, equal, transitivity, prelude, natural numbers]
SeeAlso: [LessEqualAntisymmetry, LessEqualReflexivity, EqualityTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualTransitivity]()[*h1*, *h2*]</code> proves <code>*a* <= *c*</code> from proofs *h1* of <code>*a* <= *b*</code> and *h2* of <code>*b* <= *c*</code>.

## Details & Options

- [LessEqualTransitivity]() is a theorem of the prelude, proved with the recursor of [LessEqual]() on *h2*.
- *a*, *b* and *c* are implicit arguments, found from the types of *h1* and *h2*.

## Basic Examples

The statement of [LessEqualTransitivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTransitivity]]
```

<!-- => ∀_{a∶ℕ} ∀_{b∶ℕ} ∀_{c∶ℕ} a ≤ b ⇒ b ≤ c ⇒ a ≤ c -->

---

From `0 <= 2` and `2 <= 5`, `0 <= 5`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTransitivity[LessEqualZero[2], LessEqualAddition[2, 3]]], TypeTheoryTerm[0 <= 5]]
```

<!-- => Success["TypeChecked", ...] -->
