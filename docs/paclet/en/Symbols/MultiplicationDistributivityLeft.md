---
Template: Symbol
Name: MultiplicationDistributivityLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationDistributivityLeft
Keywords: [multiplication, distributivity, left, prelude, natural numbers]
SeeAlso: [MultiplicationDistributivityRight, MultiplicationAssociativity, AdditionAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationDistributivityLeft]()[*a*, *b*, *c*]</code> proves <code>*a* * (*b* + *c*) == *a* * *b* + *a* * *c*</code>.

## Details & Options

- [MultiplicationDistributivityLeft]() is a theorem of the prelude, proved by induction on *c* with [AdditionAssociativity]().

## Basic Examples

The statement of [MultiplicationDistributivityLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityLeft]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a (b + c) == a b + a c -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityLeft[2, 3, 4]]]
```

<!-- => 2 (3 + 4) == 2 × 3 + 2 × 4 -->
