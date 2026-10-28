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

## Scope

`"Apply"` leaves a goal for each equivalence, and one for the proposition between them, which both mention:

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[r, TypeUniverse[0]]}, Implies[Equivalent[p, q], Implies[Equivalent[q, r], Equivalent[p, r]]]], {
    TypeTheoryTactic["Introduce", p, q, r, h1, h2],
    TypeTheoryTactic["Apply", EquivalentTransitivity]
}]
```

<!-- => Proof, 3 goals: p ∶ Prop, q ∶ Prop, r ∶ Prop, h1 ∶ p ⧦ q, h2 ∶ q ⧦ r ⊢ p ⧦ ?m; the same hypotheses ⊢ ?m ⧦ r; the same hypotheses ⊢ Prop -->

`h1` solves the first goal, and makes the proposition between them `q`:

```wl
proof = TypeTheoryTactic["Exact", h1][proof]
```

<!-- => Proof, 1 goal: p ∶ Prop, q ∶ Prop, r ∶ Prop, h1 ∶ p ⧦ q, h2 ∶ q ⧦ r ⊢ q ⧦ r -->

The last goal is the other hypothesis:

```wl
TypeTheoryTactic["Exact", h2][proof]
```

<!-- => Proof complete -->

---

Nested, it chains any number of equivalences:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[
    {Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[r, TypeUniverse[0]], Typed[s, TypeUniverse[0]], Typed[h1, Equivalent[p, q]], Typed[h2, Equivalent[q, r]], Typed[h3, Equivalent[r, s]]},
    EquivalentTransitivity[h1, EquivalentTransitivity[h2, h3]]
]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop ∀_r∶Prop ∀_s∶Prop (p ⧦ q) ⇒ (q ⧦ r) ⇒ (r ⧦ s) ⇒ (p ⧦ s) -->

## Properties and Relations

The first field of the result composes the forward implications, from *p* to *r*:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[
    {Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[r, TypeUniverse[0]], Typed[h1, Equivalent[p, q]], Typed[h2, Equivalent[q, r]]},
    EquivalentTransitivity[h1, h2][[1]]
]]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop ∀_r∶Prop (p ⧦ q) ⇒ (q ⧦ r) ⇒ p ⇒ r -->

## Possible Issues

The middle propositions must match: here `h2` has `q` on the right, so [EquivalentSymmetry]() has to turn it around first:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[
    {Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[r, TypeUniverse[0]], Typed[h1, Equivalent[p, q]], Typed[h2, Equivalent[r, q]]},
    EquivalentTransitivity[h1, h2]
]]]
```

<!-- => Failure["TypeMismatch", ...] -->
