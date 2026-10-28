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

## Scope

[IntervalMeet]() is an operation on the interval, a function of two of its elements.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The type of [IntervalMeet]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntervalMeet, cubical]]
```

<!-- => Interval → Interval → Interval -->

## Applications

The meet gives a connection, the square that [PathInduction]() transports along: the function of `i` and `j` that is `p[Min[i, j]]` is a path from the constant path at `x` to `p`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type, a path over the line of paths from `x` to `p[i]`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]], Typed[i, Interval]}, Function[{Typed[j, Interval]}, p[Min[i, j]]]], cubical]]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_y∶A ∀_p∶x ≡ y Path[(i∶Interval) ↦ x ≡ p[i], (j∶Interval) ↦ x, p] -->

## Properties and Relations

Reversal turns a meet into a join, [IntervalJoin](): `1 - Min[i, j]` is `Max[1 - i, 1 - j]`, a De Morgan law.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path at `1 - Min[i, j]` is the path at `Max[1 - i, 1 - j]`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[1 - Min[i, j]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[Max[1 - i, 1 - j]]], cubical]
]
```

<!-- => True -->

## Possible Issues

The interval is a De Morgan algebra, not a Boolean algebra: the meet of an element and its reversal is not 0.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path at `Min[i, 1 - i]` is not the path at 0:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[Min[i, 1 - i]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[0]], cubical]
]
```

<!-- => False -->
