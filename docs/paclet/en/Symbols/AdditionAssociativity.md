---
Template: Symbol
Name: AdditionAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionAssociativity
Keywords: [addition, associativity, prelude, natural numbers]
SeeAlso: [AdditionCommutativity, MultiplicationAssociativity, AdditionSuccessorRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionAssociativity]()[*a*, *b*, *c*]</code> proves <code>*a* + *b* + *c* == *a* + (*b* + *c*)</code>.

## Details & Options

- [AdditionAssociativity]() is a theorem of the prelude, proved by induction on *c*.
- `a + b + c` is read from the left, as `(a + b) + c`.

## Basic Examples

The statement of [AdditionAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionAssociativity]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a + b + c == a + (b + c) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionAssociativity[1, 2, 3]]]
```

<!-- => 1 + 2 + 3 == 1 + (2 + 3) -->
