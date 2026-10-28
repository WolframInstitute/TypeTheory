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

## Scope

[IntervalJoin]() is an operation on the interval, a function of two of its elements.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The type of [IntervalJoin]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntervalJoin, cubical]]
```

<!-- => Interval → Interval → Interval -->

---

Read as a face, `Max[1 - i, i]` holds where `i` is 0 or 1, so a composition with one side over it is the end of that side at both ends of `i`. Here the side is a path `q` from `x` to `z`, and the composition moves a loop `p` at `x` to a loop at `z`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The composition, a function of `i`, is a path from `z` to `z`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[p, Path[A, x, x]], Typed[q, Path[A, x, z]]},
    Function[{Typed[i, Interval]}, CubicalComposition[A, Function[{j}, {Max[1 - i, i] -> q[j]}], p[i]]]
], cubical]]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_z∶A x ≡ x → x ≡ z → z ≡ z -->

## Applications

The join gives a connection: the function of `i` and `j` that is `p[Max[i, j]]` is a path from `p` to the constant path at `y`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type, a path over the line of paths from `p[i]` to `y`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]], Typed[i, Interval]}, Function[{Typed[j, Interval]}, p[Max[i, j]]]], cubical]]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_y∶A ∀_p∶x ≡ y Path[(i∶Interval) ↦ p[i] ≡ y, p, (j∶Interval) ↦ y] -->

## Possible Issues

The interval is a De Morgan algebra, not a Boolean algebra: the join of an element and its reversal is not 1.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path at `Max[i, 1 - i]` is not the path at 1:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[Max[i, 1 - i]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[1]], cubical]
]
```

<!-- => False -->
