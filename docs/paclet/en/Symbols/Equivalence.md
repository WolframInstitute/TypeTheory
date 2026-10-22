---
Template: Symbol
Name: Equivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Equivalence
Keywords: [equivalence, types, HoTT, univalence]
SeeAlso: [EquivalenceIntroduction, IsEquivalence, EquivalenceToEquality, IdentityEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[Equivalence]()[*A*, *B*]</code> is the type of equivalences from *A* to *B*: a function with a proof that it is an equivalence.

## Details & Options

- [Equivalence]() is a structure with the one constructor [EquivalenceIntroduction](); `e[[1]]` is the function of an equivalence *e* and `e[[2]]` the proof.
- Univalence identifies the equivalences from *A* to *B* with the paths <code>*A* == *B*</code>.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.
- In <code>[TypeTheoryEnvironment]()["Cubical"]</code>, [Equivalence]() is a definition: the dependent sum of a function and the proof that its fibers are contractible, along which [EquivalenceToPath]() builds univalence.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [Equivalence]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[Equivalence, hott]]
```

<!-- => Type u → Type v → Type (max u v) -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Negation is an equivalence of the Booleans:

```wl
TypeOf[TypeTheoryTerm[NegationEquivalence, hott]]
```

<!-- => Equivalence[𝔹, 𝔹] -->
