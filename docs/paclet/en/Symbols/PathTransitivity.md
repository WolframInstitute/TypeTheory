---
Template: Symbol
Name: PathTransitivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PathTransitivity
Keywords: [path, transitivity, concatenation, composition, cubical type theory]
SeeAlso: [PathSymmetry, CubicalComposition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[PathTransitivity]()[*p*, *q*]</code> is the path *p* followed by *q*: at *i* the composition of the box with base *p*[*i*] and sides the constant `x` at `i == 0` and *q* at `i == 1`.

## Details & Options

- Its endpoints are those of *p* at 0 and *q* at 1, by computation.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathTransitivity, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_{y ∶ A} ∀_{z ∶ A} x ≡ y → y ≡ z → x ≡ z -->

## Scope

At 1, the concatenation of `p` and `q` is the end of `q`, by computation.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

For a path `p` from `x` to `y` and a path `q` from `y` to `z`, the concatenation at 1 is `z`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]]}, PathTransitivity[p, q][1]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]]}, z], cubical]
]
```

<!-- => True -->

## Applications

In a proof, applying [PathTransitivity]() leaves a goal for each path, and one for the point between them, which both mention.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Four negations of `b` come back to `b` in two steps:

```wl
proof = TypeTheoryProof[ForAll[{Typed[b, Booleans]}, Path[Booleans, "not"["not"["not"["not"[b]]]], b]], cubical, {
    TypeTheoryTactic["Introduce", b],
    TypeTheoryTactic["Apply", PathTransitivity]
}]
```

<!-- => Proof, 3 goals: b ∶ 𝔹 ⊢ !!!!b ≡ ?m; b ∶ 𝔹 ⊢ ?m ≡ b; b ∶ 𝔹 ⊢ 𝔹 -->

<code>[NegationInvolution]()["not"["not"[b]]]</code> takes off two negations, and so makes the point between them `"not"["not"[b]]`:

```wl
proof = TypeTheoryTactic["Exact", NegationInvolution["not"["not"[b]]]][proof]
```

<!-- => Proof, 1 goal: b ∶ 𝔹 ⊢ !!b ≡ b -->

<code>[NegationInvolution]()[b]</code> takes off the other two:

```wl
TypeTheoryTactic["Exact", NegationInvolution[b]][proof]
```

<!-- => Proof complete -->

## Properties and Relations

[PathTransitivity]() is a composition, [CubicalComposition](), whose sides are the constant `x` where `i == 0` and `q` where `i == 1`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its definition:

```wl
cubical[PathTransitivity]
```

<!-- => definition PathTransitivity : ∀_{A∶Type u} ∀_{x∶A} ∀_{y∶A} ∀_{z∶A} x≡y→y≡z→x≡z := {A∶Type u} {x∶A} {y∶A} {z∶A} (p∶x≡y) (q∶y≡z) (i∶Interval)↦CubicalComposition[A,(j∶Interval)↦{i == 0->x,i == 1->q[j]},p[i]] -->

## Possible Issues

The constant path is a unit of concatenation only up to a path: the composition, in a type that is a variable, does not compute.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path `p` followed by the constant path at its end is not `p` by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, PathTransitivity[p, Function[{Typed[i, Interval]}, y]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p], cubical]
]
```

<!-- => False -->
