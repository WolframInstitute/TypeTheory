---
Template: Symbol
Name: UnivalenceComputation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/UnivalenceComputation
Keywords: [univalence, computation rule, transport, HoTT]
SeeAlso: [EquivalenceToEquality, EqualityToEquivalence, Univalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[UnivalenceComputation]()[*e*]</code> proves <code>[EqualityToEquivalence]()[[EquivalenceToEquality]()[*e*]] == *e*</code>: carrying along the path of an equivalence is that equivalence.

## Details & Options

- [UnivalenceComputation]() is a theorem of the HoTT environment, read off the axiom [Univalence](). Without Prop, a theorem may state any type, and like any theorem it is never unfolded.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The statement of [UnivalenceComputation]() in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[UnivalenceComputation, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} ∀_e∶Equivalence[A, B] EqualityToEquivalence[EquivalenceToEquality[e]] == e -->
