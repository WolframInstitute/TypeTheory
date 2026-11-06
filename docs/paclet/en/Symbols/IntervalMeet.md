---
Template: Symbol
Name: IntervalMeet
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalMeet
Keywords: [interval, meet, minimum, De Morgan algebra, cubical type theory, connection, face, path induction, transport filler]
SeeAlso: [IntervalJoin, IntervalReverse, IntervalZero, IntervalOne, CubicalTransport, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IntervalMeet]()[*r*, *s*]</code> is *r* ∧ *s*, the meet of two elements of the interval of cubical type theory; <code>[Min]()[*r*, *s*]</code> stands for it.

## Details & Options

- The interval is a De Morgan algebra with [IntervalMeet](), [IntervalJoin]() and [IntervalReverse](). Two of its elements are equal when their normal forms are: irredundant joins of meets of variables and reversed variables, as [NormalForm]() writes them.
- The meet is commutative, associative and idempotent, absorbs a join, as `Min[i, Max[i, j]]` is `i`, and distributes over joins. 0 is its zero and 1 its unit.
- It is not the meet of a Boolean algebra: `Min[i, 1 - i]` is not 0.
- For a path `p` from `x` to `y`, the function of `i` and `j` that is `p[Min[i, j]]` is a connection: a square whose side at `i = 0` is the constant path at `x` and whose side at `i = 1` is `p`. `"pathInduction"` transports along it.
- Read as a face, <code>[IntervalMeet]()[*r*, *s*]</code> holds where both *r* and *s* hold; a system may write it with [And](), as `i == 1 && j == 1`. A meet that asks a variable to be both 0 and 1, such as `Min[i, 1 - i]`, holds nowhere.
- It shows as `r ∧ s`.

## Basic Examples

[IntervalMeet]() is an operation on the interval, a function of two of its elements:

```wl
TypeTheoryType[IntervalMeet, "Cubical"]
```

<!-- => Interval → Interval → Interval -->

---

[Min]() stands for the meet, which [NormalForm]() writes `∧`:

```wl
NormalForm[TypeTheoryTerm[{Typed[i, Interval], Typed[j, Interval]} |-> Min[i, j], "Cubical"]]
```

<!-- => (i ∶ Interval) (j ∶ Interval) ↦ (i ∧ j) -->

---

The meet gives a connection: the function of `i` and `j` that is `p[Min[i, j]]` is a path, as `i` goes from 0 to 1, from the constant path at `x` to `p`, through the paths from `x` to `p[i]`:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], x, y, Typed[p, Path[A, x, y]], Typed[i, Interval]} |-> Function[{Typed[j, Interval]}, p[Min[i, j]]], "Cubical"]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_y∶A ∀_p∶x ≡ y Path[(i ∶ Interval) ↦ x ≡ p[i], (j ∶ Interval) ↦ x, p] -->

## Scope

The meet absorbs a join, `Min[i, Max[i, j]]` is `i`, so a path at one is the path at the other:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]} |-> p[Min[i, Max[i, j]]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]} |-> p[i], "Cubical"]
]
```

<!-- => True -->

---

The meet is idempotent:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> Min[i, i], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ i -->

---

The meet is commutative: `Min[j, i]` has the normal form `i ∧ j`:

```wl
NormalForm[TypeTheoryTerm[{Typed[i, Interval], Typed[j, Interval]} |-> Min[j, i], "Cubical"]]
```

<!-- => (i ∶ Interval) (j ∶ Interval) ↦ (i ∧ j) -->

---

The meet distributes over the join, into a join of meets:

```wl
NormalForm[TypeTheoryTerm[{Typed[i, Interval], Typed[j, Interval], Typed[k, Interval]} |-> Min[i, Max[j, k]], "Cubical"]]
```

<!-- => (i ∶ Interval) (j ∶ Interval) (k ∶ Interval) ↦ ((i ∧ j) ∨ (i ∧ k)) -->

---

0 is the zero of the meet:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> Min[i, 0], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ 0 -->

---

Read as a face, a meet holds where both its parts hold: in a system, [And]() of two faces is their meet:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, z, Typed[q, Path[A, x, z]], Typed[i, Interval], Typed[k, Interval]} |-> CubicalComposition[A, j |-> {i == 1 && k == 1 -> q[j]}, x], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, z, Typed[q, Path[A, x, z]], Typed[i, Interval], Typed[k, Interval]} |-> CubicalComposition[A, j |-> {Min[i, k] -> q[j]}, x], "Cubical"]
]
```

<!-- => True -->

## Applications

Path induction transports along the connection of a path, `p[i ∧ j]`:

```wl
TypeTheoryEnvironment["Cubical"]["pathInduction"]
```

<!-- => definition pathInduction : ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_P∶∀_y∶A x ≡ y → Type v P[x, (i ∶ Interval) ↦ x] → ∀_{y ∶ A} ∀_p∶x ≡ y P[y, p] := {A ∶ Type u} {x ∶ A} (P ∶ ∀_y∶A x ≡ y → Type v) (d ∶ P[x, (i ∶ Interval) ↦ x]) {y ∶ A} (p ∶ x ≡ y) ↦ CubicalTransport[(i ∶ Interval) ↦ P[p[i], (j ∶ Interval) ↦ p[i ∧ j]], 0, d] -->

---

The transport filler: the line `k ↦ P[Min[i, k]]` runs along a path of types `P` from its start to `P[i]`, and is constant where `i` is 0, so transport along it over that face is a path over `P` from `a` to its transport:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[P, Path[TypeUniverse[1], A, B]], Typed[a, A]} |->
        Function[{Typed[i, Interval]}, CubicalTransport[k |-> P[Min[i, k]], 1 - i, a]],
    "Cubical"
]
```

<!-- => ∀_{A ∶ Type} ∀_{B ∶ Type} ∀_P∶A ≡ B ∀_a∶A Path[(i ∶ Interval) ↦ P[i ∧ 1], a, CubicalTransport[P, 0, a]] -->

## Properties and Relations

Reversal turns a meet into a join, [IntervalJoin](): `1 - Min[i, j]` is `Max[1 - i, 1 - j]`, a De Morgan law, so a path at one is the path at the other:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]} |-> p[1 - Min[i, j]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]} |-> p[Max[1 - i, 1 - j]], "Cubical"]
]
```

<!-- => True -->

## Possible Issues

The interval is a De Morgan algebra, not a Boolean algebra: the meet of an element and its reversal is not 0, so a path at `Min[i, 1 - i]` is not the path at 0:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[Min[i, 1 - i]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[0], "Cubical"]
]
```

<!-- => False -->

---

As a face, though, `Min[i, 1 - i]` holds nowhere, as 0 does: a transport over it asks nothing of its line, here a path of types `P`, and the function of `i` is a path between the transports over 0 at its ends:

```wl
TypeTheoryType[{Typed[P, Path[TypeUniverse[1], Booleans, Booleans]], Typed[i, Interval]} |-> CubicalTransport[P, Min[i, 1 - i], "true"], "Cubical"]
```

<!-- => ∀_P∶𝔹 ≡ 𝔹 CubicalTransport[P, 0, true] ≡ CubicalTransport[P, 0, true] -->

---

The face `Min[i, j]` holds where `i` and `j` are 1, and there the line `k ↦ P[Min[i, k]]` is `P` itself, not constant:

```wl
TypeTheoryType[{Typed[P, Path[TypeUniverse[1], Booleans, Booleans]], Typed[i, Interval], Typed[j, Interval]} |-> CubicalTransport[k |-> P[Min[i, k]], Min[i, j], "true"], "Cubical"]
```

<!-- => Failure["TransportNotConstant", ...] -->
