---
Template: Symbol
Name: CubicalComposition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CubicalComposition
Keywords: [composition, open box, lid, system, face, side, cubical type theory, hcomp, concatenation, path transitivity, square]
SeeAlso: [CubicalTransport, IntervalJoin, IntervalReverse, GlueType, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[CubicalComposition]()[*A*, [Function]()[{*i*}, {*face* -> *u*, ...}], *a*]</code> composes in the type *A*: it gives the lid of the open box whose base is *a* and whose sides are the lines *u* over the faces.

## Details & Options

- The sides are a system: a function of the interval whose body is a list of rules *face* -> *u*. A face is an element of the interval read as the condition that it is 1; a system writes them `i == 0`, `i == 1`, [And]() and [Or]() of faces, [True]() and [False](), or an element of the interval. The faces may not mention the variable of the sides.
- Each side is checked where its face holds, with the face put into it, its type and its context; any two sides agree where both faces hold, and each is *a* at `i = 0`.
- Where a face holds, the composition is the side at `i = 1`. In a function type it composes the values, and in a path type the points, with the path's endpoints as two more sides.
- Composition in a universe or in an inductive type has no rule, and does not compute where no face holds; so transport along a concatenation of paths of types does not compute either.
- The concatenation of paths, `"pathTransitivity"`, is a composition: the lid of the square with the base `p`, the side `x` where `i == 0` and the side `q` where `i == 1`.
- [CubicalComposition]() must be given all three arguments.

## Basic Examples

The concatenation of a path `p` from `x` to `y` and a path `q` from `y` to `z`: the composition with the base `p[i]`, the side `x` where `i == 0` and the side `q[j]` where `i == 1` is, as a function of `i`, a path from `x` to `z`:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]]} |->
        Function[{Typed[i, Interval]}, CubicalComposition[A, j |-> {i == 0 -> x, i == 1 -> q[j]}, p[i]]],
    "Cubical"
]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_y∶A ∀_z∶A x ≡ y → y ≡ z → x ≡ z -->

---

Where a face holds, the composition is its side at 1: composing `x` along a path `q` from `x` to `z`, over the face 1, gives `z`:

```wl
NormalForm[TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[q, Path[A, x, z]]} |-> CubicalComposition[A, j |-> {1 -> q[j]}, x], "Cubical"]]
```

<!-- => {A ∶ Type} (x ∶ A) (z ∶ A) (q ∶ x ≡ z) ↦ z -->

---

The concatenation of paths of the cubical environment, `"pathTransitivity"`:

```wl
TypeTheoryEnvironment["Cubical"]["pathTransitivity"]
```

<!-- => definition pathTransitivity : ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_{y ∶ A} ∀_{z ∶ A} x ≡ y → y ≡ z → x ≡ z := {A ∶ Type u} {x ∶ A} {y ∶ A} {z ∶ A} (p ∶ x ≡ y) (q ∶ y ≡ z) (i ∶ Interval) ↦ CubicalComposition[A, (j ∶ Interval) ↦ {i == 0 → x, i == 1 → q[j]}, p[i]] -->

## Scope

With the side `p[j]` where `i == 0` and the constant side `x` where `i == 1`, over the base `x`, the composition reverses `p`, without the reversal of the interval:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]} |->
        Function[{Typed[i, Interval]}, CubicalComposition[A, j |-> {i == 0 -> p[j], i == 1 -> x}, x]],
    "Cubical"
]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_y∶A x ≡ y → y ≡ x -->

---

A side may lie over a face that holds at both ends of `i`, `i == 0 || i == 1`: along a path `q` from `x` to `z`, the composition moves a loop `p` at `x` to a loop at `z`:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[p, Path[A, x, x]], Typed[q, Path[A, x, z]]} |->
        Function[{Typed[i, Interval]}, CubicalComposition[A, j |-> {i == 0 || i == 1 -> q[j]}, p[i]]],
    "Cubical"
]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_z∶A x ≡ x → x ≡ z → z ≡ z -->

---

In a function type, a composition composes the values: applied to `b`, it is the composition of the values at `b`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[
        {Typed[f, TypeSpecifier[{Booleans} -> Booleans]], Typed[g, TypeSpecifier[{Booleans} -> Booleans]], Typed[h, Path[TypeSpecifier[{Booleans} -> Booleans], f, g]], Typed[i, Interval], Typed[b, Booleans]} |->
            CubicalComposition[TypeSpecifier[{Booleans} -> Booleans], j |-> {i == 0 -> h[j]}, f][b],
        "Cubical"
    ],
    TypeTheoryTerm[
        {Typed[f, TypeSpecifier[{Booleans} -> Booleans]], Typed[g, TypeSpecifier[{Booleans} -> Booleans]], Typed[h, Path[TypeSpecifier[{Booleans} -> Booleans], f, g]], Typed[i, Interval], Typed[b, Booleans]} |->
            CubicalComposition[Booleans, j |-> {i == 0 -> h[j][b]}, f[b]],
        "Cubical"
    ]
]
```

<!-- => True -->

---

In a path type, it composes the points, with the endpoints of the paths as two more sides, where `j == 0` and `j == 1`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[
        {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, x, y]], Typed[r, Path[Path[A, x, y], p, q]], Typed[i, Interval], Typed[j, Interval]} |->
            CubicalComposition[Path[A, x, y], k |-> {i == 0 -> r[k]}, p][j],
        "Cubical"
    ],
    TypeTheoryTerm[
        {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, x, y]], Typed[r, Path[Path[A, x, y], p, q]], Typed[i, Interval], Typed[j, Interval]} |->
            CubicalComposition[A, k |-> {i == 0 -> r[k][j], j == 0 -> x, j == 1 -> y}, p[j]],
        "Cubical"
    ]
]
```

<!-- => True -->

## Applications

Composition fills squares: with the sides `x` where `i == 0`, `q[Min[j, k]]` where `i == 1` and `p[i]` where `j == 0`, the composition is a path, as `j` goes from 0 to 1, from `p` to the concatenation of `p` and `q`, through the paths from `x` to `q[j]`; at `j = 1` the face `j == 0` is [False]():

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]]} |->
        Function[{Typed[j, Interval], Typed[i, Interval]}, CubicalComposition[A, k |-> {i == 0 -> x, i == 1 -> q[Min[j, k]], j == 0 -> p[i]}, p[i]]],
    "Cubical"
]
```

<!-- => ∀_{A ∶ Type} ∀_x∶A ∀_y∶A ∀_z∶A ∀_p∶x ≡ y ∀_q∶y ≡ z Path[(j ∶ Interval) ↦ x ≡ q[j], p, (i ∶ Interval) ↦ CubicalComposition[A, (k ∶ Interval) ↦ {i == 0 → x, i == 1 → q[1 ∧ k], False → p[i]}, p[i]]] -->

## Properties and Relations

A path concatenated with its reversal is a loop at its start, here at double negation:

```wl
TypeTheoryType["pathTransitivity"["pathFunctionExtensionality"[Typed[b, Booleans] |-> "negationInvolution"[b]], "pathSymmetry"["pathFunctionExtensionality"[Typed[b, Booleans] |-> "negationInvolution"[b]]]], "Cubical"]
```

<!-- => ((b ∶ 𝔹) ↦ !!b) ≡ ((b ∶ 𝔹) ↦ !!b) -->

## Possible Issues

A side must be the base at 0, where its face holds; the side `y` where `i == 0` is not `p[0]`, which is `x`:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]} |-> Function[{Typed[i, Interval]}, CubicalComposition[A, j |-> {i == 0 -> y}, p[i]]],
    "Cubical"
]
```

<!-- => Failure["CapMismatch", ...] -->

---

Two sides must agree where both their faces hold; two paths `q` and `r` from `x` to `z` over the same face need not:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[q, Path[A, x, z]], Typed[r, Path[A, x, z]]} |-> CubicalComposition[A, j |-> {1 -> q[j], 1 -> r[j]}, x],
    "Cubical"
]
```

<!-- => Failure["SystemDisagreement", ...] -->

---

A face may not mention the variable of the sides:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[q, Path[A, x, z]]} |-> CubicalComposition[A, j |-> {j == 1 -> q[j]}, x], "Cubical"]
```

<!-- => Failure["FaceOfTube", ...] -->

---

The sides are a function of the interval whose body is the system, not the system alone:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[z, A], Typed[q, Path[A, x, z]]} |-> CubicalComposition[A, {1 -> x}, x], "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

Composition in an inductive type has no rule: where no face holds it does not compute, even when the base and the side are the same Boolean:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Typed[i, Interval] |-> CubicalComposition[Booleans, j |-> {i == 0 -> "true"}, "true"], "Cubical"],
    TypeTheoryTerm[Typed[i, Interval] |-> "true", "Cubical"]
]
```

<!-- => False -->

---

Nor has composition in a universe, so transport along the concatenation of two paths of types stops, though negation twice is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["pathTransitivity"["equivalenceToPath"["negationEquivalence"], "equivalenceToPath"["negationEquivalence"]], 0, "true"], "Cubical"]]
```

<!-- => CubicalTransport[(i ∶ Interval) ↦ pathTransitivity[Type, 𝔹, 𝔹, 𝔹, equivalenceToPath[negationEquivalence], equivalenceToPath[negationEquivalence], i], 0, true] -->
