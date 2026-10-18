---
Template: Symbol
Name: AdditionCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionCommutativity
Keywords: [addition, commutativity, prelude, natural numbers]
SeeAlso: [AdditionAssociativity, MultiplicationCommutativity, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionCommutativity]()[*m*, *n*]</code> proves <code>*m* + *n* == *n* + *m*</code>.

## Details & Options

- [AdditionCommutativity]() is a theorem of the prelude, proved by induction on *n* from [AdditionZeroLeft]() and [AdditionSuccessorLeft]().

## Basic Examples

The statement of [AdditionCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionCommutativity]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + n == n + m -->

---

So `x + 1` and `1 + x` are equal:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals]}, AdditionCommutativity[x, 1]]]]
```

<!-- => ∀_x∶ℕ x + 1 == 1 + x -->
