---
Template: Symbol
Name: EqualityCongruence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EqualityCongruence
Keywords: [equality, congruence, function application, theorem, prelude, induction]
SeeAlso: [EqualityReflexivity, EqualitySymmetry, EqualityTransitivity, EqualitySubstitution, TypeTheoryProof]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[EqualityCongruence]()[*f*, *h*]</code> proves <code>*f*[*x*] == *f*[*y*]</code> from a proof *h* of <code>*x* == *y*</code>.

## Details & Options

- [EqualityCongruence]() is a theorem of the prelude, proved with the recursor of [Equal]().
- The types of *x* and of <code>*f*[*x*]</code>, their universe levels, and *x* and *y* are implicit arguments.

## Basic Examples

The type of [EqualityCongruence]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityCongruence]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{β ∶ Sort v} ∀_{x ∶ α} ∀_{y ∶ α} ∀_f∶α→β x == y ⇒ f[x] == f[y] -->

---

Equal numbers have equal successors:

```wl
TypeTheoryCheck[TypeTheoryTerm[
    Function[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[h, x == y]}, EqualityCongruence[NaturalNumberSuccessor, h]]
]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x == y ⇒ x + 1 == y + 1 -->

## Applications

The step of a proof by induction that `0 + n == n`:

```wl
TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Induction", n],
    TypeTheoryTactic["Reflexivity"],
    TypeTheoryTactic["Introduce", k, ih],
    TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]]
}]
```

<!-- => Proof complete -->
