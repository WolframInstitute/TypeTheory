---
Template: Symbol
Name: LengthReverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LengthReverse
Keywords: [list, length, reverse, prelude]
SeeAlso: [LengthJoin, ReverseReverse, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LengthReverse]()[*l*]</code> proves <code>[Length]()[[Reverse]()[*l*]] == [Length]()[*l*]</code>.

## Details & Options

- [LengthReverse]() is a theorem of the prelude, proved by recursion on *l*, from [LengthJoin]().

## Basic Examples

The statement of [LengthReverse]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LengthReverse]]
```

<!-- => ∀_{α ∶ Type u} ∀_l∶Lists[α] Length[Reverse[l]] == Length[l] -->

---

For the list of 1 and 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[LengthReverse[ListPrepend[1, ListPrepend[2, EmptyList]]]]]
```

<!-- => Length[Reverse[ListPrepend[1, ListPrepend[2, EmptyList]]]] == Length[ListPrepend[1, ListPrepend[2, EmptyList]]] -->
