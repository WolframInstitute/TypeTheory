---
Template: Symbol
Name: NegationEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NegationEquivalence
Keywords: [negation, Booleans, equivalence, HoTT]
SeeAlso: [Equivalence, EquivalenceToEquality, UniverseNotSet, Not]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

[NegationEquivalence]() is the negation of Booleans, `"not"`, as an equivalence from the Booleans to themselves, its own inverse.

## Details & Options

- [NegationEquivalence]() is a definition; its paths are proved by cases on a Boolean.
- Through univalence it gives a path <code>[Booleans]() == [Booleans]()</code> that is not reflexivity, which is how [UniverseNotSet]() is proved.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.
- <code>[TypeTheoryEnvironment]()["Cubical"]</code> has its own, made by [IsomorphismEquivalence](), and transport along <code>[EquivalenceToPath]()[[NegationEquivalence]()]</code> takes `"true"` to `"false"` by computation.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [NegationEquivalence]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[NegationEquivalence, hott]]
```

<!-- => Equivalence[𝔹, 𝔹] -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Its function is negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NegationEquivalence[[1]][False], hott]]
```

<!-- => true -->
