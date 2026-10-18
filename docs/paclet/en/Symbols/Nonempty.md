---
Template: Symbol
Name: Nonempty
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Nonempty
Keywords: [nonempty, inhabited, element, choice, prelude, classical logic]
SeeAlso: [NonemptyIntroduction, Choice, Exists, Subtype]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Nonempty]()[*a*]</code> is the proposition that the type *a* has an element.

## Details & Options

- [Nonempty]() is an inductive proposition of the prelude, with the one constructor [NonemptyIntroduction]().
- A proof of <code>[Nonempty]()[*a*]</code> says that *a* has an element without giving one to compute with. [Choice]() takes such a proof to an element of *a*.
- *a* may be in any universe, a proposition among them.

## Basic Examples

The type of [Nonempty]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Nonempty]]
```

<!-- => Sort u → Prop -->

---

The natural numbers are not empty:

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction[0]], TypeTheoryTerm[Nonempty[NonNegativeIntegers]]]
```

<!-- => True -->
