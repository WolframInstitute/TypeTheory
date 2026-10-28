---
Template: Symbol
Name: EquivalenceProof
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalenceProof
Keywords: [equivalence, proof, inverse, HoTT]
SeeAlso: [IsEquivalence, EquivalenceIntroduction, NegationEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[EquivalenceProof]()[*g*, *retraction*, *h*, *section*]</code> proves <code>[IsEquivalence]()[*f*]</code> from a function *g* with <code>*g*[*f*[*x*]] == *x*</code> for every *x*, and a function *h* with <code>*f*[*h*[*y*]] == *y*</code> for every *y*.

## Details & Options

- [EquivalenceProof]() is the constructor of [IsEquivalence](); *f* and its types are implicit.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [EquivalenceProof]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalenceProof, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_{f ∶ A → B} ∀_g∶B → A (∀_x∶A g[f[x]] == x) → ∀_h∶B → A (∀_y∶B f[h[y]] == y) → IsEquivalence[f] -->

## Scope

The identity of the Booleans is an equivalence, its own inverse on both sides, in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The function *f* is found from the paths:

```wl
TypeTheoryCheck[TypeTheoryTerm[
    EquivalenceProof[Function[{Typed[x, Booleans]}, x], Function[{Typed[x, Booleans]}, EqualityReflexivity[x]], Function[{Typed[x, Booleans]}, x], Function[{Typed[x, Booleans]}, EqualityReflexivity[x]]],
    hott
]]
```

<!-- => IsEquivalence[(x ∶ 𝔹) ↦ x] -->

## Applications

With [EquivalenceIntroduction](), it makes an equivalence, in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The identity of the Booleans as an equivalence:

```wl
TypeOf[TypeTheoryTerm[EquivalenceIntroduction[
    Function[{Typed[x, Booleans]}, x],
    EquivalenceProof[Function[{Typed[x, Booleans]}, x], Function[{Typed[x, Booleans]}, EqualityReflexivity[x]], Function[{Typed[x, Booleans]}, x], Function[{Typed[x, Booleans]}, EqualityReflexivity[x]]]
], hott]]
```

<!-- => Equivalence[𝔹, 𝔹] -->

## Properties and Relations

The fields of a proof are its four arguments: the fourth is the path that makes the third a right inverse, in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The fourth field:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[f, TypeSpecifier[{Booleans} -> Booleans]], Typed[e, IsEquivalence[f]]}, e[[4]]], hott]]
```

<!-- => ∀_f∶𝔹 → 𝔹 ∀_e∶IsEquivalence[f] ∀_y∶𝔹 f[e〚3〛[y]] == y -->

## Possible Issues

The cubical environment has an [IsEquivalence]() of its own, contractible fibers, and no [EquivalenceProof]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalenceProof, TypeTheoryEnvironment["Cubical"]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
