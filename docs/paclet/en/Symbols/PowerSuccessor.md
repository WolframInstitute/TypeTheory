---
Template: Symbol
Name: PowerSuccessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PowerSuccessor
Keywords: [power, successor, prelude, natural numbers]
SeeAlso: [PowerZero, PowerAddition, Power]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PowerSuccessor]()[*m*, *n*]</code> proves <code>*m*^(*n* + 1) == *m*^*n* * *m*</code>.

## Details & Options

- [PowerSuccessor]() is a theorem of the prelude that holds by computation: it is how [Power]() is defined.

## Basic Examples

The statement of [PowerSuccessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerSuccessor]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m^(n + 1) == m^n m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerSuccessor[2, 3]]]
```

<!-- => 2^(3 + 1) == 2^3 × 2 -->
