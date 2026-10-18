---
Template: Symbol
Name: NegationEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NegationEquivalence
Keywords: [negation, Booleans, equivalence, HoTT]
SeeAlso: [Equivalence, EquivalenceToEquality, UniverseNotSet, BooleanNot]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

[NegationEquivalence]() is [BooleanNot]() as an equivalence from the Booleans to themselves, its own inverse.

## Details & Options

- [NegationEquivalence]() is a definition; its paths are proved by cases on a Boolean.
- Through univalence it gives a path <code>[Booleans]() == [Booleans]()</code> that is not reflexivity, which is how [UniverseNotSet]() is proved.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The type of [NegationEquivalence]() in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[NegationEquivalence, hott]]
```

<!-- => Equivalence[𝔹, 𝔹] -->

---

Its function is negation:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
WeakHeadNormalForm[TypeTheoryTerm[NegationEquivalence[[1]][False], hott]]
```

<!-- => true -->
