---
Template: Symbol
Name: EquivalenceIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalenceIntroduction
Keywords: [equivalence, constructor, HoTT]
SeeAlso: [Equivalence, EquivalenceProof]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[EquivalenceIntroduction]()[*f*, *e*]</code> is the equivalence given by the function *f* and the proof *e* of <code>[IsEquivalence]()[*f*]</code>.

## Details & Options

- [EquivalenceIntroduction]() is the constructor of [Equivalence]().
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [EquivalenceIntroduction]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalenceIntroduction, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_f∶A → B IsEquivalence[f] → Equivalence[A, B] -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The function of an equivalence computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NegationEquivalence[[1]][True], hott]]
```

<!-- => false -->
