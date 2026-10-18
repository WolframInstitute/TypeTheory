---
Template: Symbol
Name: CircleLoop
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CircleLoop
Keywords: [circle, loop, path, higher inductive type, HoTT]
SeeAlso: [CircleBase, CircleInduction, CircleInductionLoop]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

[CircleLoop]() is the path <code>[CircleBase]() == [CircleBase]()</code> that goes once around the circle.

## Details & Options

- It is an axiom, the path constructor of the circle. It is not reflexivity, and paths built from it, such as <code>[EqualityTransitivity]()[[CircleLoop](), [CircleLoop]()]</code>, go around more than once.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The type of [CircleLoop]() in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[CircleLoop, hott]]
```

<!-- => CircleBase == CircleBase -->

---

Going around twice is a path too:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[EqualityTransitivity[CircleLoop, CircleLoop], hott]]
```

<!-- => CircleBase == CircleBase -->
