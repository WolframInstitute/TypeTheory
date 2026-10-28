---
Template: Symbol
Name: PathCongruence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PathCongruence
Keywords: [path, congruence, function, cubical type theory]
SeeAlso: [PathSymmetry, PathFunctionExtensionality]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[PathCongruence]()[*f*, *p*]</code> is the path from *f*[*x*] to *f*[*y*] that a function *f* gives from a path *p* from *x* to *y*: the function of *i* that is *f*[*p*[*i*]].

## Details & Options

- It is a function of the interval, with no composition.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathCongruence, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_f∶A → B ∀_{x ∶ A} ∀_{y ∶ A} x ≡ y → f[x] ≡ f[y] -->

## Scope

An instance: negation along the path <code>[NegationInvolution]()["true"]</code> from `"not"["not"["true"]]` to `"true"`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type, a path between the negations of the two ends:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathCongruence["not", NegationInvolution["true"]], cubical]]
```

<!-- => !!!true ≡ !true -->

## Applications

In a proof, <code>[TypeTheoryTactic]()["Apply", [PathCongruence]()[*f*]]</code> leaves a path between the arguments of *f* to give.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Applied with `"not"`, it turns a path between two negations into a path between what they negate:

```wl
proof = TypeTheoryProof[ForAll[{Typed[b, Booleans]}, Path[Booleans, "not"["not"["not"[b]]], "not"[b]]], cubical, {
    TypeTheoryTactic["Introduce", b],
    TypeTheoryTactic["Apply", PathCongruence["not"]]
}]
```

<!-- => Proof, 1 goal: b ∶ 𝔹 ⊢ !!b ≡ b -->

[NegationInvolution]() gives that path:

```wl
TypeTheoryTactic["Exact", NegationInvolution[b]][proof]
```

<!-- => Proof complete -->

## Properties and Relations

[PathCongruence]() commutes with [PathSymmetry]() by computation: both sides are the function of `i` that is `f[p[1 - i]]`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The congruence of a reversed path is the reversed congruence:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[f, TypeSpecifier[{A} -> B]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, PathCongruence[f, PathSymmetry[p]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[f, TypeSpecifier[{A} -> B]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, PathSymmetry[PathCongruence[f, p]]], cubical]
]
```

<!-- => True -->

## Possible Issues

[PathCongruence]() is a definition of the cubical environment only. The HoTT environment has [EqualityCongruence]() instead.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

[PathCongruence]() is not one of its constants:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathCongruence, hott]]
```

<!-- => Failure["ElaborationFailed", ...] -->
