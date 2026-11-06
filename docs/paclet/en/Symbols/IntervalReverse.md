---
Template: Symbol
Name: IntervalReverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalReverse
Keywords: [interval, reversal, negation, De Morgan algebra, cubical type theory, symmetry, inverse path, face]
SeeAlso: [IntervalMeet, IntervalJoin, IntervalZero, IntervalOne, CubicalTransport, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IntervalReverse]()[*r*]</code> is ~*r*, the reversal of an element of the interval of cubical type theory, which exchanges 0 and 1; `1 - r` stands for it.

## Details & Options

- A path at `1 - i` is the path reversed: `"pathSymmetry"` takes a path `p` from `x` to `y` to the function of `i` that is `p[1 - i]`, a path from `y` to `x`.
- Reversal is an involution, takes 0 to 1 and 1 to 0, and turns meets into joins and joins into meets, as in a De Morgan algebra; but `Min[r, 1 - r]` is not 0 and `Max[r, 1 - r]` is not 1.
- `1 - r` stands for <code>[IntervalReverse]()[*r*]</code> where *r* is written as an element of the interval: a variable of the interval, or [Min](), [Max]() or a reversal of them. `1 - 0` is a subtraction of numbers; <code>[IntervalReverse]()[0]</code> is the reversal of 0.
- Read as a face, <code>[IntervalReverse]()[*i*]</code> holds where *i* is 0, which a system may write `i == 0`.
- It shows as `~r`.

## Basic Examples

[IntervalReverse]() is an operation on the interval:

```wl
TypeTheoryType[IntervalReverse, "Cubical"]
```

<!-- => Interval → Interval -->

---

A path reversed, the function of `i` that is `p[1 - i]`, goes from `y` to `x`:

```wl
TypeTheoryType[{x, y, Typed[p, Path[Booleans, x, y]]} |-> (Typed[i, Interval] |-> p[1 - i]), "Cubical"]
```

<!-- => ∀_x∶𝔹 ∀_y∶𝔹 x ≡ y → y ≡ x -->

---

The reversal of paths of the cubical environment, `"pathSymmetry"`:

```wl
TypeTheoryEnvironment["Cubical"]["pathSymmetry"]
```

<!-- => definition pathSymmetry : ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_{y ∶ A} x ≡ y → y ≡ x := {A ∶ Type u} {x ∶ A} {y ∶ A} (p ∶ x ≡ y) (i ∶ Interval) ↦ p[~i] -->

## Scope

`1 - i` stands for the reversal, which [NormalForm]() writes `~i`:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> 1 - i, "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ ~i -->

---

The path between functions that `"pathFunctionExtensionality"` makes from `"negationInvolution"` goes from double negation to the identity; reversed, it starts at the identity:

```wl
NormalForm[TypeTheoryTerm["pathSymmetry"["pathFunctionExtensionality"[b |-> "negationInvolution"[b]]][0], "Cubical"]]
```

<!-- => (x ∶ 𝔹) ↦ x -->

---

Transport along the path of types that univalence makes from negation, reversed, applies the inverse of negation, which is negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["pathSymmetry"["equivalenceToPath"["negationEquivalence"]], 0, "true"], "Cubical"]]
```

<!-- => false -->

---

Read as a face, `1 - i` holds where `i` is 0. There the line `k ↦ P[Min[i, k]]` is constant, so transport over `1 - i` is allowed, and is a path over the path of types `P` from `"true"` to its transport:

```wl
TypeTheoryType[Typed[P, Path[TypeUniverse[1], Booleans, Booleans]] |-> Function[{Typed[i, Interval]}, CubicalTransport[k |-> P[Min[i, k]], 1 - i, "true"]], "Cubical"]
```

<!-- => ∀_P∶𝔹 ≡ 𝔹 Path[(i ∶ Interval) ↦ P[i ∧ 1], true, CubicalTransport[P, 0, true]] -->

---

In a system, the face `i == 0` is `1 - i`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{Typed[P, Path[TypeUniverse[1], Booleans, Booleans]], Typed[i, Interval]} |-> CubicalTransport[k |-> P[Min[i, k]], i == 0, "true"], "Cubical"],
    TypeTheoryTerm[{Typed[P, Path[TypeUniverse[1], Booleans, Booleans]], Typed[i, Interval]} |-> CubicalTransport[k |-> P[Min[i, k]], 1 - i, "true"], "Cubical"]
]
```

<!-- => True -->

## Properties and Relations

Reversal is an involution, so a path at `1 - (1 - i)` is the path at `i`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[1 - (1 - i)], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[i], "Cubical"]
]
```

<!-- => True -->

---

So a path reversed twice is the path itself:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{x, y, Typed[p, Path[Booleans, x, y]]} |-> "pathSymmetry"["pathSymmetry"[p]], "Cubical"],
    TypeTheoryTerm[{x, y, Typed[p, Path[Booleans, x, y]]} |-> p, "Cubical"]
]
```

<!-- => True -->

---

Reversal turns a meet into a join, a De Morgan law:

```wl
NormalForm[TypeTheoryTerm[{Typed[i, Interval], Typed[j, Interval]} |-> 1 - Min[i, 1 - j], "Cubical"]]
```

<!-- => (i ∶ Interval) (j ∶ Interval) ↦ (~i ∨ j) -->

---

Reversal exchanges the endpoints: the reversal of 0 is 1:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IntervalReverse[0], "Cubical"]]
```

<!-- => 1 -->

## Possible Issues

An element and its reversal meet in no endpoint, but the interval is no Boolean algebra: a path at `Min[i, 1 - i]` is not the path at 0:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[Min[i, 1 - i]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, Typed[p, Path[A, x, x]], Typed[i, Interval]} |-> p[0], "Cubical"]
]
```

<!-- => False -->

---

`1 - 0` is not read as the reversal of 0 but as a subtraction of numbers, which the cubical environment does not have; <code>[IntervalReverse]()[0]</code> is the reversal:

```wl
TypeTheoryType[{x, y, Typed[p, Path[Booleans, x, y]]} |-> p[1 - 0], "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

Read as a face, `i` holds where `i` is 1, and there the line `k ↦ P[Min[i, k]]` is `P` itself, not constant:

```wl
TypeTheoryType[Typed[P, Path[TypeUniverse[1], Booleans, Booleans]] |-> Function[{Typed[i, Interval]}, CubicalTransport[k |-> P[Min[i, k]], i, "true"]], "Cubical"]
```

<!-- => Failure["TransportNotConstant", ...] -->
