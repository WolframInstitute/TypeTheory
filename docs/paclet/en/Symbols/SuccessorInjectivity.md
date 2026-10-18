---
Template: Symbol
Name: SuccessorInjectivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SuccessorInjectivity
Keywords: [successor, injectivity, prelude, natural numbers]
SeeAlso: [SuccessorNotZero, NaturalNumberPredecessor, EqualityCongruence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SuccessorInjectivity]()[*h*]</code> proves <code>*m* == *n*</code> from a proof *h* of <code>*m* + 1 == *n* + 1</code>.

## Details & Options

- [SuccessorInjectivity]() is a theorem of the prelude, proved by applying [NaturalNumberPredecessor]() to both sides with [EqualityCongruence]().
- *m* and *n* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [SuccessorInjectivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorInjectivity]]
```

<!-- => ∀_{m∶ℕ} ∀_{n∶ℕ} m + 1 == n + 1 ⇒ m == n -->

---

From `x + 1 == 5`, `x == 4`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x + 1 == 5]}, SuccessorInjectivity[h]]]]
```

<!-- => ∀_x∶ℕ x + 1 == 5 ⇒ x == 4 -->
