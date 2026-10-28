---
Template: Symbol
Name: IsomorphismEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsomorphismEquivalence
Keywords: [isomorphism, equivalence, cubical type theory, Glue type]
SeeAlso: [Equivalence, NegationEquivalence, EquivalenceToPath]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IsomorphismEquivalence]()[*f*, *g*, *s*, *t*]</code> is the equivalence that a function *f* with an inverse *g* gives, *s* and *t* the paths from *f*[*g*[*b*]] to *b* and from *g*[*f*[*a*]] to *a*.

## Details & Options

- The center of the fiber over *y* is {*g*[*y*], *s*[*y*]}; the square that joins any element of the fiber to it is built from compositions, as in the cubical library of Agda.
- Its function is *f*: along [EquivalenceToPath]() of it, transport applies *f*.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Negation, the isomorphism of the Booleans with themselves that is its own inverse:

```wl
cubical[NegationEquivalence]
```

<!-- => definition NegationEquivalence : Equivalence[𝔹, 𝔹] := IsomorphismEquivalence[not, not, NegationInvolution, NegationInvolution] -->

## Scope

[IsomorphismEquivalence]() takes a function, its inverse, and the two paths that make them inverse.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The type of [IsomorphismEquivalence]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IsomorphismEquivalence, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} ∀_f∶A → B ∀_g∶B → A (∀_b∶B f[g[b]] ≡ b) → (∀_a∶A g[f[a]] ≡ a) → Equivalence[A, B] -->

## Applications

In a proof of an equivalence, applying [IsomorphismEquivalence]() to a function and its inverse leaves the two paths to give.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Negation, with negation as its inverse:

```wl
proof = TypeTheoryProof[Equivalence[Booleans, Booleans], cubical, {TypeTheoryTactic["Apply", IsomorphismEquivalence["not", "not"]]}]
```

<!-- => Proof, 2 goals: ⊢ ∀_b∶𝔹 !!b ≡ b; ⊢ ∀_a∶𝔹 !!a ≡ a -->

[NegationInvolution]() gives the first path:

```wl
proof = TypeTheoryTactic["Exact", NegationInvolution][proof]
```

<!-- => Proof, 1 goal: ⊢ ∀_a∶𝔹 !!a ≡ a -->

And the second:

```wl
TypeTheoryTactic["Exact", NegationInvolution][proof]
```

<!-- => Proof complete -->

---

Univalence computes on the equivalence of an isomorphism: transport along its path, [EquivalenceToPath](), applies the function.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Transport along the path of negation takes `"false"` to `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[IsomorphismEquivalence["not", "not", NegationInvolution, NegationInvolution]], 0, "false"], cubical]]
```

<!-- => true -->

## Possible Issues

[IsomorphismEquivalence]() is a definition of the cubical environment only. In the HoTT environment an equivalence is made with [EquivalenceIntroduction]() and [EquivalenceProof]().

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

[IsomorphismEquivalence]() is not one of its constants:

```wl
TypeTheoryCheck[TypeTheoryTerm[IsomorphismEquivalence, hott]]
```

<!-- => Failure["ElaborationFailed", ...] -->
