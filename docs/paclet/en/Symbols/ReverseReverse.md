---
Template: Symbol
Name: ReverseReverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ReverseReverse
Keywords: [list, reverse, involution, prelude]
SeeAlso: [ReverseJoin, LengthReverse, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ReverseReverse]()[*l*]</code> proves <code>[Reverse]()[[Reverse]()[*l*]] == *l*</code>.

## Details & Options

- [ReverseReverse]() is a theorem of the prelude, proved by recursion on *l*, from [ReverseJoin]().

## Basic Examples

The statement of [ReverseReverse]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ReverseReverse]]
```

<!-- => ∀_{α ∶ Type u} ∀_l∶Lists[α] Reverse[Reverse[l]] == l -->

---

For the list of 1 and 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[ReverseReverse[ListPrepend[1, ListPrepend[2, EmptyList]]]]]
```

<!-- => Reverse[Reverse[ListPrepend[1, ListPrepend[2, EmptyList]]]] == ListPrepend[1, ListPrepend[2, EmptyList]] -->
