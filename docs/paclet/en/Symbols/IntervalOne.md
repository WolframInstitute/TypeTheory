---
Template: Symbol
Name: IntervalOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalOne
Keywords: [interval, endpoint, one, end of a path, face, greatest element, cubical type theory, path]
SeeAlso: [IntervalZero, IntervalReverse, IntervalMeet, IntervalJoin, CubicalTransport, CubicalComposition, GlueType, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

[IntervalOne]() is the endpoint 1 of the interval of cubical type theory; `1` stands for it where an element of the interval is expected.

## Details & Options

- A path is a function of the interval, and its value at [IntervalOne]() is its end. A path that is not a function, such as a variable `p` of the type `Path[A, x, y]`, computes to the end of its type there: `p[1]` is `y`.
- `1` stands for [IntervalOne]() where an element of the interval is expected: as the argument of a path, of [Min]() or [Max](), or as a face. On its own `1` is a natural number, which the cubical environment does not have.
- [IntervalOne]() is the greatest element of the interval: `Max[i, 1]` is 1 and `Min[i, 1]` is `i`. Its reversal, <code>[IntervalReverse]()[1]</code>, is [IntervalZero]().
- Read as a face, [IntervalOne]() holds everywhere: a transport over it is its element, and its line must be constant; a composition with a side over it is that side at 1; a Glue type over it is its glued type, an element of it is its term, and [GlueElimination]() is the equivalence applied. A system may write it [True]().
- A transport ends in its line at 1, *A*[1].
- It shows as `1`. It is a constant of the cubical rules, which [TypeTheoryCubical]() declares; terms that use it name <code>[TypeTheoryEnvironment]()["Cubical"]</code>.

## Basic Examples

[IntervalOne]() is an element of the interval:

```wl
TypeTheoryType[IntervalOne, "Cubical"]
```

<!-- => Interval -->

---

The end of a path is its value at 1: the path between functions that `"pathFunctionExtensionality"` makes from the paths <code>"negationInvolution"[*b*]</code>, from `"not"["not"[b]]` to `b`, ends at the identity:

```wl
NormalForm[TypeTheoryTerm["pathFunctionExtensionality"[b |-> "negationInvolution"[b]][1], "Cubical"]]
```

<!-- => (x ∶ 𝔹) ↦ x -->

---

A path that is not a function, a variable `p` from `x` to `y`, is `y` at 1:

```wl
NormalForm[TypeTheoryTerm[{x, y, Typed[p, Path[Booleans, x, y]]} |-> p[1], "Cubical"]]
```

<!-- => (x ∶ 𝔹) (y ∶ 𝔹) (p ∶ x ≡ y) ↦ y -->

## Scope

The same holds in any type: a path `p` from `x` to `y`, at 1, is `y`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, y, Typed[p, Path[A, x, y]]} |-> p[1], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, y, Typed[p, Path[A, x, y]]} |-> y, "Cubical"]
]
```

<!-- => True -->

---

Over the face 1, which holds everywhere, a transport is its element, even in a type `A` that has no rule of transport of its own:

```wl
NormalForm[TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], a} |-> CubicalTransport[A, 1, a], "Cubical"]]
```

<!-- => {A ∶ Type} (a ∶ A) ↦ a -->

---

Over the face 1 a composition is its side at 1: composing `x` along a path `q` from `x` to `z` gives `z`:

```wl
NormalForm[TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], x, z, Typed[q, Path[A, x, z]]} |-> CubicalComposition[A, j |-> {1 -> q[j]}, x], "Cubical"]]
```

<!-- => {A ∶ Type} (x ∶ A) (z ∶ A) (q ∶ x ≡ z) ↦ z -->

---

Over the face 1 a Glue type is its glued type:

```wl
WeakHeadNormalForm[TypeTheoryTerm[GlueType[Booleans, {1 -> {Booleans, "negationEquivalence"}}], "Cubical"]]
```

<!-- => 𝔹 -->

## Properties and Relations

1 is the greatest element of the interval: its join with any `i` is 1:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> Max[i, 1], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ 1 -->

---

Its meet with any `i` is `i`:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> Min[i, 1], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ i -->

---

Reversal takes 1 to 0, [IntervalZero]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[IntervalReverse[1], "Cubical"]]
```

<!-- => 0 -->

## Possible Issues

A face that is 1 holds everywhere, so the line of a transport over it must be constant, and a path of types `p` need not be:

```wl
TypeTheoryType[Typed[p, Path[TypeUniverse[1], Booleans, Booleans]] |-> CubicalTransport[p, 1, "true"], "Cubical"]
```

<!-- => Failure["TransportNotConstant", ...] -->

---

`1` stands for [IntervalOne]() only where an element of the interval is expected; on its own it is a natural number, and the cubical environment has none:

```wl
TypeTheoryType[1, "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->
