---
Template: Symbol
Name: EquivalentTransitivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentTransitivity
Keywords: [equivalent, transitivity, prelude, logic]
SeeAlso: [EquivalentReflexivity, EquivalentSymmetry, EqualityTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentTransitivity]()[*h1*, *h2*]</code> proves <code>[Equivalent]()[*a*, *c*]</code> from proofs *h1* of <code>[Equivalent]()[*a*, *b*]</code> and *h2* of <code>[Equivalent]()[*b*, *c*]</code>.

## Details & Options

- [EquivalentTransitivity]() is a theorem of the prelude, proved by composing the implications.
- *a*, *b* and *c* are implicit arguments, found from the types of *h1* and *h2*.

## Basic Examples

The statement of [EquivalentTransitivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentTransitivity]]
```

<!-- => ∀_{a∶Prop} ∀_{b∶Prop} ∀_{c∶Prop} (a ⧦ b) ⇒ (b ⧦ c) ⇒ (a ⧦ c) -->

---

Chain two equivalences:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[r, TypeUniverse[0]], Typed[h1, Equivalent[p, q]], Typed[h2, Equivalent[q, r]]}, EquivalentTransitivity[h1, h2]]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop ∀_r∶Prop (p ⧦ q) ⇒ (q ⧦ r) ⇒ (p ⧦ r) -->
