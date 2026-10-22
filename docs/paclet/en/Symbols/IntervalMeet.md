---
Template: Symbol
Name: IntervalMeet
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalMeet
Keywords: [interval, meet, De Morgan algebra, cubical type theory, connection]
SeeAlso: [IntervalJoin, IntervalReverse, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IntervalMeet]()[*r*, *s*]</code> is *r* ∧ *s*, the meet of two elements of the interval of cubical type theory; <code>[Min]()[*r*, *s*]</code> stands for it.

## Details & Options

- The interval is a De Morgan algebra, and two of its elements are equal when their normal forms are: irredundant disjunctions of conjunctions of variables and reversed variables.
- Read as a face, <code>[IntervalMeet]()[*r*, *s*]</code> holds where both *r* and *s* hold.
- It shows as `r ∧ s`.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The absorption law, `Min[i, Max[i, j]]` is `i`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[Min[i, Max[i, j]]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[i]], cubical]
]
```

<!-- => True -->
