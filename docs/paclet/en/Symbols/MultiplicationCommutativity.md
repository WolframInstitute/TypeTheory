---
Template: Symbol
Name: MultiplicationCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationCommutativity
Keywords: [multiplication, commutativity, prelude, natural numbers]
SeeAlso: [MultiplicationAssociativity, AdditionCommutativity, MultiplicationDistributivityRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationCommutativity]()[*m*, *n*]</code> proves <code>*m* * *n* == *n* * *m*</code>.

## Details & Options

- [MultiplicationCommutativity]() is a theorem of the prelude, proved by induction on *n* from [MultiplicationZeroLeft]() and [MultiplicationSuccessorLeft]().

## Basic Examples

The statement of [MultiplicationCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m n == n m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity[3, 4]]]
```

<!-- => 3 × 4 == 4 × 3 -->
