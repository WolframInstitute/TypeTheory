---
Template: Symbol
Name: JoinAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/JoinAssociativity
Keywords: [list, join, append, associativity, prelude]
SeeAlso: [JoinEmptyRight, ReverseJoin, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[JoinAssociativity]()[*a*, *b*, *c*]</code> proves <code>[Join]()[[Join]()[*a*, *b*], *c*] == [Join]()[*a*, [Join]()[*b*, *c*]]</code>.

## Details & Options

- [JoinAssociativity]() is a theorem of the prelude, proved by recursion on *a*.

## Basic Examples

The statement of [JoinAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[JoinAssociativity]]
```

<!-- => ∀_{α ∶ Type u} ∀_a∶Lists[α] ∀_b∶Lists[α] ∀_c∶Lists[α] Join[Join[a, b], c] == Join[a, Join[b, c]] -->

---

For lists of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]], Typed[c, Lists[Naturals]]}, JoinAssociativity[a, b, c]]]]
```

<!-- => ∀_a∶Lists[ℕ] ∀_b∶Lists[ℕ] ∀_c∶Lists[ℕ] Join[Join[a, b], c] == Join[a, Join[b, c]] -->
