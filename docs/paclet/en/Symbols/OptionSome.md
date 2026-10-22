---
Template: Symbol
Name: OptionSome
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OptionSome
Keywords: [option, some, value, constructor, prelude]
SeeAlso: [Option, OptionNone, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[OptionSome]()[*x*]</code> is the value *x* of <code>[Option]()[*α*]</code>.

## Details & Options

- [OptionSome]() is the second constructor of [Option]().
- *α* is an implicit argument, found from the type of *x*.

## Basic Examples

The statement of [OptionSome]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome]]
```

<!-- => ∀_{α ∶ Type u} α → Option[α] -->

---

3 as an optional natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome[3]]]
```

<!-- => Option[ℕ] -->
