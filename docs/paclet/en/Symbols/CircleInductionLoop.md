---
Template: Symbol
Name: CircleInductionLoop
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CircleInductionLoop
Keywords: [circle, loop, computation rule, higher inductive type, HoTT]
SeeAlso: [CircleInduction, DependentCongruence, CircleInductionBase]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[CircleInductionLoop]()[*P*, *b*, *l*]</code> proves that circle induction gives the path *l* on the loop: <code>[DependentCongruence]()[[CircleInduction]()[*P*, *b*, *l*, #] &, [CircleLoop]()] == *l*</code>.

## Details & Options

- [CircleInductionLoop]() is an axiom: on paths, a higher inductive type computes only up to a path.
- Its statement type-checks only because [CircleInductionBase]() computes: the two sides are paths between `CircleInduction[P, b, l, CircleBase]` and *b*.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [CircleInductionLoop]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[CircleInductionLoop, hott]]
```

<!-- => ∀_P∶𝕊¹ → Type u ∀_b∶P[CircleBase] ∀_l∶Transport[P, CircleLoop, b] == b DependentCongruence[(x∶𝕊¹) ↦ CircleInduction[P, b, l, x], CircleLoop] == l -->
