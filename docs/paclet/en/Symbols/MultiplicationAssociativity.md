---
Template: Symbol
Name: MultiplicationAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationAssociativity
Keywords: [multiplication, associativity, prelude, natural numbers]
SeeAlso: [MultiplicationCommutativity, AdditionAssociativity, PowerAddition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationAssociativity]()[*a*, *b*, *c*]</code> proves <code>*a* * *b* * *c* == *a* * (*b* * *c*)</code>.

## Details & Options

- [MultiplicationAssociativity]() is a theorem of the prelude, proved by induction on *c* with [MultiplicationDistributivityLeft]().
- `a * b * c` is read from the left, as `(a * b) * c`.

## Basic Examples

The statement of [MultiplicationAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationAssociativity]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ (a b) c == a (b c) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationAssociativity[2, 3, 4]]]
```

<!-- => (2 × 3) 4 == 2 (3 × 4) -->
