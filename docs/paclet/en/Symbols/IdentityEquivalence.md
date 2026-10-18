---
Template: Symbol
Name: IdentityEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IdentityEquivalence
Keywords: [identity, equivalence, HoTT]
SeeAlso: [EqualityToEquivalence, Equivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[IdentityEquivalence]()[*A*]</code> is the identity function of the type *A* as an equivalence.

## Details & Options

- [IdentityEquivalence]() is a definition; it is what [EqualityToEquivalence]() gives for reflexivity.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The type of [IdentityEquivalence]() in the HoTT environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
TypeTheoryCheck[TypeTheoryTerm[IdentityEquivalence, hott]]
```

<!-- => ∀_A∶Type u Equivalence[A, A] -->

---

Its function is the identity:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
WeakHeadNormalForm[TypeTheoryTerm[IdentityEquivalence[Booleans][[1]][True], hott]]
```

<!-- => true -->
