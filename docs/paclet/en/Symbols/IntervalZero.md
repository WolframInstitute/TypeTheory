---
Template: Symbol
Name: IntervalZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalZero
Keywords: [interval, endpoint, cubical type theory, path]
SeeAlso: [IntervalOne, IntervalReverse, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

[IntervalZero]() is the endpoint 0 of the interval of cubical type theory; `0` stands for it where an element of the interval is expected.

## Details & Options

- A path at [IntervalZero]() is its start: a function of the interval is its value there, and a path that is not a function computes to the start of its type.
- It shows as `0`.
- It is a constant of the cubical rules, which [TypeTheoryCubical]() declares.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path at 0 is its start:

```wl
WeakHeadNormalForm[TypeTheoryTerm[PathSymmetry[Function[{Typed[i, Interval]}, "true"]][0], cubical]]
```

<!-- => true -->
