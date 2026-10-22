---
Template: Symbol
Name: Option
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Option
Keywords: [option, optional value, maybe, prelude, inductive type]
SeeAlso: [OptionNone, OptionSome, DisjointUnion, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Option]()[*α*]</code> is the type of optional values of *α*: none, or some element of *α*.

## Details & Options

- [Option]() is an inductive type of the prelude, with the constructors [OptionNone]() and [OptionSome](), as Lean's `Option`.
- For *α* in `Type u`, <code>[Option]()[*α*]</code> is in `Type u` too.

## Basic Examples

The type of [Option]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Option]]
```

<!-- => Type u → Type u -->

---

Some natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome[3]]]
```

<!-- => Option[ℕ] -->
