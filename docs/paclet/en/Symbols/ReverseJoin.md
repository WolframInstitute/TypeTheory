---
Template: Symbol
Name: ReverseJoin
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ReverseJoin
Keywords: [list, reverse, join, prelude]
SeeAlso: [ReverseReverse, JoinAssociativity, JoinEmptyRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ReverseJoin]()[*a*, *b*]</code> proves <code>[Reverse]()[[Join]()[*a*, *b*]] == [Join]()[[Reverse]()[*b*], [Reverse]()[*a*]]</code>.

## Details & Options

- [ReverseJoin]() is a theorem of the prelude, proved by recursion on *a*, from [JoinEmptyRight]() and [JoinAssociativity]().

## Basic Examples

The statement of [ReverseJoin]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ReverseJoin]]
```

<!-- => ∀_{α ∶ Type u} ∀_a∶Lists[α] ∀_b∶Lists[α] Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]] -->

---

For lists of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, ReverseJoin[a, b]]]]
```

<!-- => ∀_a∶Lists[ℕ] ∀_b∶Lists[ℕ] Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]] -->
