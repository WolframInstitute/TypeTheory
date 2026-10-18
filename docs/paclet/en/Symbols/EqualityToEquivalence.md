---
Template: Symbol
Name: EqualityToEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EqualityToEquivalence
Keywords: [path, equivalence, univalence, idtoeqv, HoTT]
SeeAlso: [Univalence, EquivalenceToEquality, IdentityEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[EqualityToEquivalence]()[*p*]</code> is the equivalence that a path *p* : <code>*A* == *B*</code> between types gives.

## Details & Options

- [EqualityToEquivalence]() is a definition by path induction: reflexivity gives [IdentityEquivalence](). The HoTT book writes it `idtoeqv`.
- [Univalence]() is the axiom that it is an equivalence.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The type of [EqualityToEquivalence]() in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[EqualityToEquivalence, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} A == B → Equivalence[A, B] -->

---

Reflexivity gives the identity, by computation:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
DefinitionallyEqualQ[TypeTheoryTerm[EqualityToEquivalence[EqualityReflexivity[Booleans]], hott], TypeTheoryTerm[IdentityEquivalence[Booleans], hott]]
```

<!-- => True -->
