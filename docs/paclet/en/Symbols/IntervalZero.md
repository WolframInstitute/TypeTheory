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

## Scope

[IntervalZero]() is an element of the interval.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The type of [IntervalZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntervalZero, cubical]]
```

<!-- => Interval -->

---

A path that is not a function, such as a variable, computes to the start of its type at 0.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path `p` from `x` to `y`, at 0, is `x`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p[0]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, x], cubical]
]
```

<!-- => True -->

## Properties and Relations

Reversal takes 0 to 1, [IntervalOne](), so a path at the reversal of 0 is its end.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path `p` from `x` to `y`, at <code>[IntervalReverse]()[0]</code>, is `y`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p[IntervalReverse[0]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, y], cubical]
]
```

<!-- => True -->

## Possible Issues

`0` stands for [IntervalZero]() only where an element of the interval is expected. On its own it is a natural number, and the cubical environment has none.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A `0` on its own:

```wl
TypeTheoryCheck[TypeTheoryTerm[0, cubical]]
```

<!-- => Failure["ElaborationFailed", ...] -->
