---
Template: Symbol
Name: EqualityTransitivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EqualityTransitivity
Keywords: [equality, transitivity, theorem, prelude]
SeeAlso: [EqualityReflexivity, EqualitySymmetry, EqualityCongruence, EqualitySubstitution, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[EqualityTransitivity]()[*h1*, *h2*]</code> proves <code>*x* == *z*</code> from proofs *h1* of <code>*x* == *y*</code> and *h2* of <code>*y* == *z*</code>.

## Details & Options

- [EqualityTransitivity]() is a theorem of the prelude, <code>[TypeTheoryEnvironment]()["Prelude"]</code>, proved with the recursor of [Equal]().
- The type of *x*, *y* and *z*, its universe level, and *x*, *y* and *z* themselves are implicit arguments.

## Basic Examples

The type of [EqualityTransitivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityTransitivity, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{x ∶ α} ∀_{y ∶ α} ∀_{z ∶ α} x == y ⇒ y == z ⇒ x == z -->

---

Chain two equations:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[z, NonNegativeIntegers]}, Implies[x == y, Implies[y == z, x == z]]], TypeTheoryEnvironment["Prelude"], {
    TypeTheoryTactic["Introduce", x, y, z, h1, h2],
    TypeTheoryTactic["Exact", EqualityTransitivity[h1, h2]]
}];
proof["Term"]
```

<!-- => (x ∶ ℕ) (y ∶ ℕ) (z ∶ ℕ) (h1 ∶ x == y) (h2 ∶ y == z) ↦ EqualityTransitivity[h1, h2] -->
