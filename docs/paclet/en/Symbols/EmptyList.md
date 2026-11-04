---
Template: Symbol
Name: EmptyList
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EmptyList
Keywords: [list, empty list, nil, constructor, prelude]
SeeAlso: [List, ListPrepend, OptionNone]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[EmptyList]() is `{}`, the list with no elements, by the name it had.

## Details & Options

- The empty list is written `{}`, and a list `{a, b}`: `List` is the type of lists and its elements alike. Its constructors are the empty list and `Prepend`, as Lean's `List.nil` and `List.cons`, and `Prepend[l, x]` is the list *l* with *x* in front, as in the Wolfram Language.
- [EmptyList]() is read as `{}` where the environment declares no constant of that name.
- The type of the elements is an implicit argument, found from the expected type.

## Basic Examples

The empty list is `{}`:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[EmptyList, {NonNegativeIntegers}]], TypeTheoryTerm[Typed[{}, {NonNegativeIntegers}]]]
```

<!-- => True -->

---

A list ending in the empty list shows as its elements:

```wl
TypeTheoryTerm[Prepend[Prepend[{}, 2], 1]]
```

<!-- => {1, 2} -->
