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

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [EqualityToEquivalence]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityToEquivalence, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} A == B → Equivalence[A, B] -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Reflexivity gives the identity, by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[EqualityToEquivalence[EqualityReflexivity[Booleans]], hott], TypeTheoryTerm[IdentityEquivalence[Booleans], hott]]
```

<!-- => True -->
