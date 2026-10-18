---
Template: Symbol
Name: NonemptyIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NonemptyIntroduction
Keywords: [nonempty, introduction, element, prelude, classical logic]
SeeAlso: [Nonempty, Choice, ExistsIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[NonemptyIntroduction]()[*x*]</code> proves <code>[Nonempty]()[*a*]</code> from an element *x* of *a*.

## Details & Options

- [NonemptyIntroduction]() is the constructor of [Nonempty]().
- *a* is an implicit argument, found from the type of *x*.

## Basic Examples

The statement of [NonemptyIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction]]
```

<!-- => ∀_{α ∶ Sort u} α → Nonempty[α] -->

---

A natural number shows that there are natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction[3]]]
```

<!-- => Nonempty[ℕ] -->
