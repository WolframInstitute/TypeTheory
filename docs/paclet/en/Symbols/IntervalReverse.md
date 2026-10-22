---
Template: Symbol
Name: IntervalReverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalReverse
Keywords: [interval, reversal, De Morgan algebra, cubical type theory, symmetry]
SeeAlso: [IntervalMeet, IntervalJoin, PathSymmetry]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IntervalReverse]()[*r*]</code> is ~*r*, the reversal of an element of the interval of cubical type theory, which exchanges 0 and 1; `1 - r` stands for it.

## Details & Options

- Reversal is an involution and turns meets into joins, as in a De Morgan algebra, but `Min[r, 1 - r]` is not 0.
- Read as a face, <code>[IntervalReverse]()[*i*]</code> holds where *i* is 0, which a system writes `i == 0`.
- It shows as `~r`. A path at `1 - i` is the path reversed, [PathSymmetry]().

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Reversing twice gives the path back:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[1 - (1 - i)]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[i]], cubical]
]
```

<!-- => True -->

## Possible Issues

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

An element and its reversal meet in no endpoint, but the interval is no Boolean algebra:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[Min[i, 1 - i]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[0]], cubical]
]
```

<!-- => False -->
