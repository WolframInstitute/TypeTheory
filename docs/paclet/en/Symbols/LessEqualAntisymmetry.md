---
Template: Symbol
Name: LessEqualAntisymmetry
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualAntisymmetry
Keywords: [less, equal, antisymmetry, prelude, natural numbers]
SeeAlso: [LessEqualTransitivity, LessIrreflexivity, LessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualAntisymmetry]()[*h1*, *h2*]</code> proves <code>*a* == *b*</code> from proofs *h1* of <code>*a* <= *b*</code> and *h2* of <code>*b* <= *a*</code>.

## Details & Options

- [LessEqualAntisymmetry]() is a theorem of the prelude, proved with the recursor of [LessEqual](), [LessIrreflexivity]() and [FalseElimination]().
- *a* and *b* are implicit arguments, found from the types of *h1* and *h2*.

## Basic Examples

The statement of [LessEqualAntisymmetry]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAntisymmetry]]
```

<!-- => ∀_{a∶ℕ} ∀_{b∶ℕ} a ≤ b ⇒ b ≤ a ⇒ a == b -->

---

From `x <= 3` and `3 <= x`, `x == 3`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[h1, x <= 3], Typed[h2, 3 <= x]}, LessEqualAntisymmetry[h1, h2]]]]
```

<!-- => ∀_x∶ℕ x ≤ 3 ⇒ 3 ≤ x ⇒ x == 3 -->
