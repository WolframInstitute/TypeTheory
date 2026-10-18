---
Template: Symbol
Name: AdditionSuccessorLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionSuccessorLeft
Keywords: [addition, successor, left, prelude, natural numbers]
SeeAlso: [AdditionSuccessorRight, AdditionCommutativity, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionSuccessorLeft]()[*m*, *n*]</code> proves <code>*m* + 1 + *n* == *m* + *n* + 1</code>.

## Details & Options

- [AdditionSuccessorLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [AdditionSuccessorLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSuccessorLeft]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + 1 + n == m + n + 1 -->

---

For variables:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, AdditionSuccessorLeft[m, n]]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + 1 + n == m + n + 1 -->
