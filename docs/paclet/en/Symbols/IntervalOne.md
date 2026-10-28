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

## Scope

[IntervalOne]() is an element of the interval.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The type of [IntervalOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntervalOne, cubical]]
```

<!-- => Interval -->

---

A path that is not a function, such as a variable, computes to the end of its type at 1.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path `p` from `x` to `y`, at 1, is `y`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p[1]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, y], cubical]
]
```

<!-- => True -->

## Applications

At 1, the path between two functions that [PathFunctionExtensionality]() gives is the second function.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Made from the paths <code>[NegationInvolution]()[*b*]</code> from `"not"["not"[b]]` to `b`, the path ends at the identity:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[PathFunctionExtensionality[Function[{Typed[b, Booleans]}, NegationInvolution[b]]][1], cubical],
    TypeTheoryTerm[Function[{Typed[b, Booleans]}, b], cubical]
]
```

<!-- => True -->

## Possible Issues

A face that is 1 holds everywhere, so the line of a transport over it must be constant, and a path of types need not be.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Transport along a path of types `p` over the face 1:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, Path[TypeUniverse[1], Booleans, Booleans]]}, CubicalTransport[p, 1, "true"]], cubical]]
```

<!-- => Failure["TransportNotConstant", ...] -->
