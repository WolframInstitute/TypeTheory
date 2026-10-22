---
Template: Symbol
Name: EmptyList
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EmptyList
Keywords: [list, empty list, nil, constructor, prelude]
SeeAlso: [Lists, ListPrepend, OptionNone]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[EmptyList]() is the list of <code>[Lists]()[*α*]</code> with no elements.

## Details & Options

- [EmptyList]() is the first constructor of [Lists](), as Lean's `List.nil`.
- *α* is an implicit argument, found from the expected type.

## Basic Examples

The type of [EmptyList]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EmptyList]]
```

<!-- => ∀_{α ∶ Type u} Lists[α] -->

---

The empty list of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[EmptyList, Lists[Naturals]]]]
```

<!-- => Lists[ℕ] -->
