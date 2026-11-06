---
Template: Symbol
Name: IntervalJoin
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalJoin
Keywords: [interval, join, maximum, De Morgan algebra, cubical type theory, connection, face, boundary]
SeeAlso: [IntervalMeet, IntervalReverse, IntervalZero, IntervalOne, CubicalComposition, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IntervalJoin]()[*r*, *s*]</code> is *r* ∨ *s*, the join of two elements of the interval of cubical type theory; <code>[Max]()[*r*, *s*]</code> stands for it.

## Details & Options

- The interval is a De Morgan algebra with [IntervalMeet](), [IntervalJoin]() and [IntervalReverse](). Two of its elements are equal when their normal forms are: irredundant joins of meets of variables and reversed variables, as [NormalForm]() writes them.
- The join is commutative, associative and idempotent, and absorbs a meet, as `Max[i, Min[i, j]]` is `i`. 0 is its unit and 1 its zero.
- It is not the join of a Boolean algebra: `Max[i, 1 - i]` is not 1.
- For a path `p` from `x` to `y`, the function of `i` and `j` that is `p[Max[i, j]]` is a connection: a square whose side at `i = 0` is `p` and whose side at `i = 1` is the constant path at `y`.
- Read as a face, <code>[IntervalJoin]()[*r*, *s*]</code> holds where either holds; a system may write it with [Or](), as `i == 0 || i == 1`, the face of both ends of `i`.
- It shows as `r ∨ s`.

## Basic Examples

[IntervalJoin]() is an operation on the interval, a function of two of its elements:

```wl
TypeTheoryType[IntervalJoin, "Cubical"]
```

<!-- => Interval → Interval → Interval -->

---

[Max]() stands for the join, which [NormalForm]() writes `∨`:

```wl
NormalForm[TypeTheoryTerm[{Typed[i, Interval], Typed[j, Interval]} |-> Max[i, j], "Cubical"]]
```

<!-- => (i ∶ Interval) (j ∶ Interval) ↦ (i ∨ j) -->

---

The join gives a connection: the function of `i` and `j` that is `p[Max[i, j]]` is a path, as `i` goes from 0 to 1, from `p` to the constant path at `y`, through the paths from `p[i]` to `y`:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]], Typed[i, Interval]} |-> Function[{Typed[j, Interval]}, p[Max[i, j]]], "Cubical"]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_y∶A ∀_p∶x ≡ y Path[(i ∶ Interval) ↦ p[i] ≡ y, p, (j ∶ Interval) ↦ y] -->

## Scope

The join absorbs a meet, `Max[i, Min[i, j]]` is `i`, so a path at one is the path at the other:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]} |-> p[Max[i, Min[i, j]]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]} |-> p[i], "Cubical"]
]
```

<!-- => True -->

---

1 is the zero of the join:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> Max[i, 1], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ 1 -->

---

Read as a face, a join holds where either part holds: in a system, [Or]() of two faces is their join:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[p, Path[A, x, x]], Typed[q, Path[A, x, z]], Typed[i, Interval]} |-> CubicalComposition[A, j |-> {i == 0 || i == 1 -> q[j]}, p[i]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[p, Path[A, x, x]], Typed[q, Path[A, x, z]], Typed[i, Interval]} |-> CubicalComposition[A, j |-> {Max[1 - i, i] -> q[j]}, p[i]], "Cubical"]
]
```

<!-- => True -->

---

The face `Max[1 - i, i]` holds where `i` is 0 or 1, so a composition with one side over it is the end of that side at both ends of `i`. With the side a path `q` from `x` to `z`, the composition moves a loop `p` at `x` to a loop at `z`:

```wl
TypeTheoryType[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[p, Path[A, x, x]], Typed[q, Path[A, x, z]]},
    Function[{Typed[i, Interval]}, CubicalComposition[A, j |-> {Max[1 - i, i] -> q[j]}, p[i]]]
], "Cubical"]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_z∶A x ≡ x → x ≡ z → z ≡ z -->

## Properties and Relations

Reversal turns a join into a meet, [IntervalMeet](), a De Morgan law:

```wl
NormalForm[TypeTheoryTerm[{Typed[i, Interval], Typed[j, Interval]} |-> 1 - Max[i, j], "Cubical"]]
```

<!-- => (i ∶ Interval) (j ∶ Interval) ↦ (~i ∧ ~j) -->

## Possible Issues

The interval is a De Morgan algebra, not a Boolean algebra: the join of an element and its reversal is not 1, so a path at `Max[i, 1 - i]` is not the path at 1:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[Max[i, 1 - i]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[1], "Cubical"]
]
```

<!-- => False -->
