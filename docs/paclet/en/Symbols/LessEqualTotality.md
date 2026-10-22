---
Template: Symbol
Name: LessEqualTotality
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualTotality
Keywords: [order, totality, trichotomy, inequality, prelude, natural numbers]
SeeAlso: [LessEqualAntisymmetry, LessEqualDecidable, AdditionMonotonicity, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualTotality]()[*m*, *n*]</code> proves <code>[Or]()[*m* <= *n*, *n* < *m*]</code>.

## Details & Options

- [LessEqualTotality]() is a theorem of the prelude, proved by induction on *m* and cases on *n*.
- The tactic `"LinearArithmetic"` of [TypeTheoryTactic]() splits on it, and refutes the case it does not want.

## Basic Examples

The statement of [LessEqualTotality]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTotality]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ (m ≤ n ∨ n < m) -->

---

For 3 and 5:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTotality[3, 5]]]
```

<!-- => 3 ≤ 5 ∨ 5 < 3 -->
