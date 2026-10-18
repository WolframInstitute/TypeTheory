---
Template: Symbol
Name: Univalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Univalence
Keywords: [univalence, axiom, equivalence, HoTT, homotopy type theory]
SeeAlso: [EqualityToEquivalence, EquivalenceToEquality, UnivalenceComputation, UniverseNotSet]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[Univalence]()[*A*, *B*]</code> proves that [EqualityToEquivalence]() is an equivalence for the types *A* and *B*: equal types are equivalent types, in as many ways as they are equivalent.

## Details & Options

- [Univalence]() is an axiom of the HoTT environment, which follows rules without Prop, so that no two proofs of an equality are made equal.
- Its right inverse is [EquivalenceToEquality](), and [UnivalenceComputation]() is the path that inverse gives.
- Univalence contradicts the rules of the prelude, where a proposition's proofs are all equal; see the tutorial *Homotopy Type Theory*.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The statement of [Univalence]() in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[Univalence, hott]]
```

<!-- => ∀_A∶Type u ∀_B∶Type u IsEquivalence[(p∶A == B) ↦ EqualityToEquivalence[p]] -->

---

The axioms of the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
Information[hott, "Axioms"]
```

<!-- => {Univalence, Circle, CircleBase, CircleLoop, CircleInduction, CircleInductionLoop} -->
