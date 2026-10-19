---
Template: Symbol
Name: IsSet
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsSet
Keywords: [set, uniqueness of identity proofs, HoTT]
SeeAlso: [UniverseNotSet, Equal]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[IsSet]()[*A*]</code> is the type of proofs that any two paths between the same elements of *A* are equal.

## Details & Options

- [IsSet]() is a definition. The types of the prelude's rules are all sets, since their proofs of an equality are all equal; in the HoTT environment some types are not, by [UniverseNotSet]().
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [IsSet]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[IsSet, hott]]
```

<!-- => Type u → Type u -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

What it says of the Booleans:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsSet[Booleans], hott]]
```

<!-- => ∀_x∶𝔹 ∀_y∶𝔹 ∀_p∶x == y ∀_q∶x == y p == q -->
