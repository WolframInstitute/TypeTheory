---
Template: Symbol
Name: IntervalOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalOne
Keywords: [interval, endpoint, cubical type theory, path]
SeeAlso: [IntervalZero, IntervalReverse, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

[IntervalOne]() is the endpoint 1 of the interval of cubical type theory; `1` stands for it where an element of the interval is expected.

## Details & Options

- A path at [IntervalOne]() is its end, and a face that is [IntervalOne]() holds everywhere.
- It shows as `1`.
- It is a constant of the cubical rules, which [TypeTheoryCubical]() declares.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Where the face 1 holds, transport is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Booleans, 1, "true"], cubical]]
```

<!-- => true -->
