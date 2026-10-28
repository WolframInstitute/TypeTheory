---
Template: Symbol
Name: IsContractible
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsContractible
Keywords: [contractible, center, equivalence, cubical type theory]
SeeAlso: [Fiber, IsEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IsContractible]()[*X*]</code> is the type of an element *c* of *X*, its center, with a path from *c* to every element.

## Details & Options

- The kernel writes the same type for the fibers of the equivalences of Glue types, and transport in a Glue type uses their centers.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its definition:

```wl
cubical[IsContractible]
```

<!-- => definition IsContractible : Type u → Type u := (A ∶ Type u) ↦ Σ_c∶A ∀_z∶A c ≡ z -->

## Scope

What [IsContractible]() says of the Booleans: an element `c` with a path from `c` to every Boolean.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The statement, unfolded:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsContractible[Booleans], cubical]]
```

<!-- => Σ_c∶𝔹 ∀_z∶𝔹 c ≡ z -->

## Applications

The fibers of an equivalence are contractible: [IdentityEquivalence]() proves it for the fiber of the identity of the Booleans over `"true"`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The proof:

```wl
TypeTheoryProof[IsContractible[Fiber[Function[{Typed[x, Booleans]}, x], "true"]], cubical, {TypeTheoryTactic["Exact", IdentityEquivalence[Booleans][[2]]["true"]]}]
```

<!-- => Proof complete -->

The center of that fiber is `"true"` with the constant path:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IdentityEquivalence[Booleans][[2]]["true"][[1]], cubical]]
```

<!-- => 〈true, (j∶Interval) ↦ true〉 -->

## Properties and Relations

In the cubical environment, [IsEquivalence]() asks every fiber of a function to be contractible.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

What it says of negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsEquivalence["not"], cubical]]
```

<!-- => ∀_y∶𝔹 IsContractible[Fiber[not, y]] -->

## Possible Issues

A term without an environment is in the prelude, which has no [IsContractible]().

The contractibility of the Booleans, in the prelude:

```wl
TypeTheoryCheck[TypeTheoryTerm[IsContractible[Booleans]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
