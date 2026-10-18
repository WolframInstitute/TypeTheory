---
Template: Symbol
Name: EquivalentSymmetry
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentSymmetry
Keywords: [equivalent, symmetry, prelude, logic]
SeeAlso: [EquivalentReflexivity, EquivalentTransitivity, EqualitySymmetry]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentSymmetry]()[*h*]</code> proves <code>[Equivalent]()[*b*, *a*]</code> from a proof *h* of <code>[Equivalent]()[*a*, *b*]</code>.

## Details & Options

- [EquivalentSymmetry]() is a theorem of the prelude, proved by swapping the fields of *h*.
- *a* and *b* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [EquivalentSymmetry]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentSymmetry]]
```

<!-- => ∀_{a∶Prop} ∀_{b∶Prop} (a ⧦ b) ⇒ (b ⧦ a) -->

---

Turn an equivalence around:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, Equivalent[p, q]]}, EquivalentSymmetry[h]]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop (p ⧦ q) ⇒ (q ⧦ p) -->
