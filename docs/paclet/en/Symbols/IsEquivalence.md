---
Template: Symbol
Name: IsEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsEquivalence
Keywords: [equivalence, bi-invertible, HoTT, univalence]
SeeAlso: [EquivalenceProof, Equivalence, Univalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[IsEquivalence]()[*f*]</code> is the type of proofs that the function *f* is an equivalence: a left inverse and a right inverse, each with its path.

## Details & Options

- [IsEquivalence]() is an inductive type with the one constructor [EquivalenceProof](); `e[[1]]` to `e[[4]]` are the left inverse, its path, the right inverse and its path.
- This bi-invertible definition is the one under which being an equivalence is a proposition, as univalence requires.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [IsEquivalence]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[IsEquivalence, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} (A → B) → Type (max u v) -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Being an equivalence is a type:

```wl
TypeOf[TypeTheoryTerm[IsEquivalence["not"], hott]]
```

<!-- => Type -->
