---
Template: Symbol
Name: OptionNone
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OptionNone
Keywords: [option, none, missing value, constructor, prelude]
SeeAlso: [Option, OptionSome, EmptyList]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[OptionNone]() is the missing value of <code>[Option]()[*α*]</code>.

## Details & Options

- [OptionNone]() is the first constructor of [Option]().
- *α* is an implicit argument, found from the expected type.

## Basic Examples

The type of [OptionNone]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionNone]]
```

<!-- => ∀_{α ∶ Type u} Option[α] -->

---

The missing natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[OptionNone, Option[Naturals]]]]
```

<!-- => Option[ℕ] -->
