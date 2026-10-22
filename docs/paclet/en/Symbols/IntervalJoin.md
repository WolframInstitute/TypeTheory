---
Template: Symbol
Name: IntervalJoin
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalJoin
Keywords: [interval, join, De Morgan algebra, cubical type theory, connection]
SeeAlso: [IntervalMeet, IntervalReverse, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IntervalJoin]()[*r*, *s*]</code> is *r* ∨ *s*, the join of two elements of the interval of cubical type theory; <code>[Max]()[*r*, *s*]</code> stands for it.

## Details & Options

- The interval is a De Morgan algebra, and two of its elements are equal when their normal forms are: irredundant disjunctions of conjunctions of variables and reversed variables.
- Read as a face, <code>[IntervalJoin]()[*r*, *s*]</code> holds where either holds.
- It shows as `r ∨ s`.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The absorption law, `Max[i, Min[i, j]]` is `i`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[Max[i, Min[i, j]]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[i]], cubical]
]
```

<!-- => True -->
