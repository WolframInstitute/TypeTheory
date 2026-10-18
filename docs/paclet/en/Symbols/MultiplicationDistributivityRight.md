---
Template: Symbol
Name: MultiplicationDistributivityRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationDistributivityRight
Keywords: [multiplication, distributivity, right, prelude, natural numbers]
SeeAlso: [MultiplicationDistributivityLeft, MultiplicationCommutativity, MultiplicationSuccessorLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationDistributivityRight]()[*a*, *b*, *c*]</code> proves <code>(*a* + *b*) * *c* == *a* * *c* + *b* * *c*</code>.

## Details & Options

- [MultiplicationDistributivityRight]() is a theorem of the prelude, proved from [MultiplicationDistributivityLeft]() and [MultiplicationCommutativity]().

## Basic Examples

The statement of [MultiplicationDistributivityRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityRight]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ (a + b) c == a c + b c -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityRight[2, 3, 4]]]
```

<!-- => (2 + 3) 4 == 2 × 4 + 3 × 4 -->
