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

## Scope

`"Apply"` turns the goal around:

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Equivalent[p, q], Equivalent[q, p]]], {
    TypeTheoryTactic["Introduce", p, q, h],
    TypeTheoryTactic["Apply", EquivalentSymmetry]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, q ∶ Prop, h ∶ p ⧦ q ⊢ p ⧦ q -->

The hypothesis is the new goal:

```wl
TypeTheoryTactic["Exact", h][proof]
```

<!-- => Proof complete -->

## Applications

Two propositions equivalent to the same third are equivalent to each other, with [EquivalentTransitivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[
    {Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[r, TypeUniverse[0]], Typed[h1, Equivalent[p, r]], Typed[h2, Equivalent[q, r]]},
    EquivalentTransitivity[h1, EquivalentSymmetry[h2]]
]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop ∀_r∶Prop (p ⧦ r) ⇒ (q ⧦ r) ⇒ (p ⧦ q) -->

## Properties and Relations

It swaps the two implications: the first field of the result is the second of *h*:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentSymmetry[h][[1]]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ 1 == 1 ⇒ True -->
