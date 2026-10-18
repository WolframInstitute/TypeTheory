---
Template: Symbol
Name: MultiplicationOneLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationOneLeft
Keywords: [multiplication, one, left, prelude, natural numbers]
SeeAlso: [MultiplicationOneRight, MultiplicationCommutativity, PowerOne]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationOneLeft]()[*n*]</code> proves <code>1 * *n* == *n*</code>.

## Details & Options

- [MultiplicationOneLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [MultiplicationOneLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationOneLeft]]
```

<!-- => ∀_n∶ℕ 1 n == n -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, MultiplicationOneLeft[n]]]]
```

<!-- => ∀_n∶ℕ 1 n == n -->
