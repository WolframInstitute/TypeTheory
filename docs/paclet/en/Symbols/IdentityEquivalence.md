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

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [IdentityEquivalence]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[IdentityEquivalence, hott]]
```

<!-- => ∀_A∶Type u Equivalence[A, A] -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Its function is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IdentityEquivalence[Booleans][[1]][True], hott]]
```

<!-- => true -->
