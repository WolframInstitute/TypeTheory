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
