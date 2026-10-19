---
Template: Symbol
Name: EquivalenceToEquality
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalenceToEquality
Keywords: [univalence, ua, equivalence, path, HoTT]
SeeAlso: [Univalence, UnivalenceComputation, EqualityToEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[EquivalenceToEquality]()[*e*]</code> is the path <code>*A* == *B*</code> that univalence gives for the equivalence *e* from *A* to *B*.

## Details & Options

- [EquivalenceToEquality]() is the right inverse that [Univalence]() provides; the HoTT book writes it `ua`.
- It does not compute: univalence is an axiom here, so a path it gives is stuck.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [EquivalenceToEquality]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalenceToEquality, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} Equivalence[A, B] → A == B -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Negation gives a path from the Booleans to themselves:

```wl
TypeOf[TypeTheoryTerm[EquivalenceToEquality[NegationEquivalence], hott]]
```

<!-- => 𝔹 == 𝔹 -->
