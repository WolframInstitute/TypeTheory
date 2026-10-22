---
Template: Symbol
Name: EquivalenceToPath
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalenceToPath
Keywords: [univalence, Glue type, equivalence, path, cubical type theory]
SeeAlso: [GlueType, CubicalTransport, IsomorphismEquivalence, EquivalenceToEquality]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[EquivalenceToPath]()[*e*]</code> is the path of types from *A* to *B* that an equivalence *e* from *A* to *B* gives: the function of *i* that is the Glue type over *B* with *A* glued along *e* where `i == 0` and *B* along the identity where `i == 1`.

## Details & Options

- This is univalence, which computes: transport along <code>[EquivalenceToPath]()[*e*]</code> applies the function of *e*, where the axiom of the HoTT environment, [EquivalenceToEquality](), stops.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalenceToPath, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} Equivalence[A, B] → A ≡ B -->

---

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Transport along the path of negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "true"], cubical]]
```

<!-- => false -->

## Possible Issues

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Composition in a universe has no rule, so transport along a concatenation of paths of univalence stops:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[PathTransitivity[EquivalenceToPath[NegationEquivalence], EquivalenceToPath[NegationEquivalence]], 0, "true"], cubical]]
```

<!-- => CubicalTransport[(i∶Interval)↦PathTransitivity[Type,𝔹,𝔹,𝔹,EquivalenceToPath[NegationEquivalence],EquivalenceToPath[NegationEquivalence],i],0,true] -->
