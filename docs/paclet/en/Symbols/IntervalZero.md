---
Template: Symbol
Name: IntervalZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntervalZero
Keywords: [interval, endpoint, zero, start of a path, face, least element, cubical type theory, path]
SeeAlso: [IntervalOne, IntervalReverse, IntervalMeet, IntervalJoin, CubicalTransport, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

[IntervalZero]() is the endpoint 0 of the interval of cubical type theory; `0` stands for it where an element of the interval is expected.

## Details & Options

- A path is a function of the interval, and its value at [IntervalZero]() is its start. A path that is not a function, such as a variable `p` of the type `Path[A, x, y]`, computes to the start of its type there: `p[0]` is `x`.
- `0` stands for [IntervalZero]() where an element of the interval is expected: as the argument of a path, of [Min]() or [Max](), or as a face. On its own `0` is a natural number, which the cubical environment does not have.
- [IntervalZero]() is the least element of the interval: `Min[i, 0]` is 0 and `Max[i, 0]` is `i`. Its reversal, <code>[IntervalReverse]()[0]</code>, is [IntervalOne]().
- Read as a face, [IntervalZero]() holds nowhere: a transport over it asks nothing of its line, and a side of a composition over it is never used. A system may write it [False](), and shows it so.
- A function of the interval is a path whose start is its value at 0, and a transport carries an element of its line at 0, *A*[0], to *A*[1].
- It shows as `0`. It is a constant of the cubical rules, which [TypeTheoryCubical]() declares; terms that use it name <code>[TypeTheoryEnvironment]()["Cubical"]</code>.

## Basic Examples

[IntervalZero]() is an element of the interval:

```wl
TypeTheoryType[IntervalZero, "Cubical"]
```

<!-- => Interval -->

---

The start of a path is its value at 0: the path between functions that `"pathFunctionExtensionality"` makes from `"negationInvolution"` starts at double negation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm["pathFunctionExtensionality"[Typed[b, Booleans] |-> "negationInvolution"[b]][0], "Cubical"],
    TypeTheoryTerm[Typed[b, Booleans] |-> "not"["not"[b]], "Cubical"]
]
```

<!-- => True -->

---

A path that is not a function, a variable `p` from `x` to `y`, is `x` at 0:

```wl
NormalForm[TypeTheoryTerm[{Typed[x, Booleans], Typed[y, Booleans], Typed[p, Path[Booleans, x, y]]} |-> p[0], "Cubical"]]
```

<!-- => (x ∶ 𝔹) (y ∶ 𝔹) (p ∶ x ≡ y) ↦ x -->

## Scope

The same holds in any type: a path `p` from `x` to `y`, at 0, is `x`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]} |-> p[0], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]} |-> x, "Cubical"]
]
```

<!-- => True -->

---

At 0, the path of types that univalence makes from negation is the Booleans, the type glued where `i == 0` holds:

```wl
WeakHeadNormalForm[TypeTheoryTerm["equivalenceToPath"["negationEquivalence"][0], "Cubical"]]
```

<!-- => 𝔹 -->

---

Over the face 0, which holds nowhere, a transport may go along any line, here a path of types `P`:

```wl
TypeTheoryType[Typed[P, Path[TypeUniverse[1], Booleans, Booleans]] |-> CubicalTransport[P, 0, "true"], "Cubical"]
```

<!-- => ∀_P∶𝔹 ≡ 𝔹 P[1] -->

## Properties and Relations

0 is the least element of the interval: its meet with any `i` is 0:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> Min[i, 0], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ 0 -->

---

Its join with any `i` is `i`:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> Max[i, 0], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ i -->

---

Reversal takes 0 to 1, [IntervalOne](), so a path `p` from `x` to `y`, at <code>[IntervalReverse]()[0]</code>, is `y`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]} |-> p[IntervalReverse[0]], "Cubical"],
    TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]} |-> y, "Cubical"]
]
```

<!-- => True -->

## Possible Issues

`0` stands for [IntervalZero]() only where an element of the interval is expected; on its own it is a natural number, and the cubical environment has none:

```wl
TypeTheoryType[0, "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A function of the interval is a path from its value at 0, so the constant function at `"true"` is no path from `"false"`:

```wl
TypeTheoryType[Typed[Typed[i, Interval] |-> "true", Path[Booleans, "false", "true"]], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->
