---
Template: Symbol
Name: EqualitySymmetry
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EqualitySymmetry
Keywords: [equality, symmetry, theorem, prelude]
SeeAlso: [EqualityReflexivity, EqualityTransitivity, EqualityCongruence, EqualitySubstitution]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[EqualitySymmetry]()[*h*]</code> proves <code>*y* == *x*</code> from a proof *h* of <code>*x* == *y*</code>.

## Details & Options

- [EqualitySymmetry]() is a theorem of the prelude, <code>[TypeTheoryEnvironment]()["Prelude"]</code>, proved with the recursor of [Equal]().
- The type of *x* and *y*, its universe level, *x* and *y* are implicit arguments, found from the type of *h*.

## Basic Examples

The type of [EqualitySymmetry]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualitySymmetry, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{x ∶ α} ∀_{y ∶ α} x == y ⇒ y == x -->

---

Turn an equation around:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x + 0 == x]}, EqualitySymmetry[h]], TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_x∶ℕ x + 0 == x ⇒ x == x + 0 -->
