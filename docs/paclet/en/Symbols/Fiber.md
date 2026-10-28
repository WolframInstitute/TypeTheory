---
Template: Symbol
Name: Fiber
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Fiber
Keywords: [fiber, equivalence, cubical type theory]
SeeAlso: [IsContractible, IsEquivalence, Equivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[Fiber]()[*f*, *y*]</code> is the type of the elements *x* with a path from *f*[*x*] to *y*: <code>[DependentSum]()[*A*, [Function]()[{*x*}, Path[*B*, *f*[*x*], *y*]]]</code>.

## Details & Options

- An equivalence is a function whose fibers are contractible, [IsContractible]().
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its definition:

```wl
cubical[Fiber]
```

<!-- => definition Fiber : ∀_{A∶Type u} ∀_{B∶Type u} (A→B)→B→Type u := {A∶Type u} {B∶Type u} (f∶A→B) (y∶B)↦Σ_x∶A f[x]≡y -->

## Scope

The fiber of negation over `"true"` is a dependent sum: an element `x` of the Booleans with a path from `"not"[x]` to `"true"`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The fiber, unfolded:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Fiber["not", "true"], cubical]]
```

<!-- => Σ_x∶𝔹 !x ≡ true -->

## Applications

`"false"` is in the fiber of negation over `"true"`: `"not"["false"]` computes to `"true"`, so the constant path at `"true"` goes from one to the other.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A proof that gives the pair, a [DependentPair]():

```wl
TypeTheoryProof[Fiber["not", "true"], cubical, {TypeTheoryTactic["Exact", DependentPair["false", Function[{Typed[i, Interval]}, "true"]]]}]
```

<!-- => Proof complete -->

## Properties and Relations

The fibers of an equivalence are contractible, [IsContractible](), so each has a center. For [NegationEquivalence]() over `"true"`, it is `"not"["true"]`, with the path <code>[NegationInvolution]()["true"]</code> from its negation to `"true"`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The center of the fiber of [NegationEquivalence]() over `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NegationEquivalence[[2]]["true"][[1]], cubical]]
```

<!-- => 〈!true, NegationInvolution[true]〉 -->

## Possible Issues

[Fiber]() is a definition of the cubical environment only. In the HoTT environment an equivalence is a function with a left and a right inverse, and there are no fibers.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

[Fiber]() is not one of its constants:

```wl
TypeTheoryCheck[TypeTheoryTerm[Fiber, hott]]
```

<!-- => Failure["ElaborationFailed", ...] -->
