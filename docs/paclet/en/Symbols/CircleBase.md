---
Template: Symbol
Name: CircleBase
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CircleBase
Keywords: [circle, base point, higher inductive type, HoTT]
SeeAlso: [CircleLoop, CircleInduction, Circle]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

[CircleBase]() is the point of the circle, [Circle](), in the HoTT environment.

## Details & Options

- The circle is a higher inductive type, given by axioms: [CircleBase](), the path [CircleLoop]() and [CircleInduction]().
- [Circle]() is the built-in symbol of the circle, as [NonNegativeIntegers]() is that of the natural numbers; it shows as 𝕊¹.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The type of [CircleBase]() in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[CircleBase, hott]]
```

<!-- => 𝕊¹ -->
