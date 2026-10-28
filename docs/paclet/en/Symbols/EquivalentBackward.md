---
Template: Symbol
Name: EquivalentBackward
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentBackward
Keywords: [equivalent, backward, prelude, logic]
SeeAlso: [EquivalentForward, EquivalentIntroduction, EquivalentSymmetry]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentBackward]()[*h*]</code> proves <code>[Implies]()[*b*, *a*]</code> from a proof *h* of <code>[Equivalent]()[*a*, *b*]</code>.

## Details & Options

- [EquivalentBackward]() is a theorem of the prelude, the second field of the proof: `h[[2]]`.
- *a* and *b* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [EquivalentBackward]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentBackward]]
```

<!-- => ∀_{a∶Prop} ∀_{b∶Prop} (a ⧦ b) ⇒ b ⇒ a -->

---

From a proof of <code>[Equivalent]()[[True](), 1 == 1]</code>, a proof of [True]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentBackward[h][EqualityReflexivity[1]]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ True -->

## Scope

With `"Apply"`, <code>[EquivalentBackward]()[*h*]</code> turns a goal *a* into the goal *b*:

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Equivalent[p, q], Implies[q, p]]], {
    TypeTheoryTactic["Introduce", p, q, h, hq],
    TypeTheoryTactic["Apply", EquivalentBackward[h]]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, q ∶ Prop, h ∶ p ⧦ q, hq ∶ q ⊢ q -->

The hypothesis `hq` proves it:

```wl
TypeTheoryTactic["Exact", hq][proof]
```

<!-- => Proof complete -->

## Properties and Relations

<code>[EquivalentBackward]()[*h*]</code> proves what the second field `h[[2]]` proves:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, h[[2]]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ 1 == 1 ⇒ True -->

---

It is [EquivalentForward]() of the equivalence turned around by [EquivalentSymmetry]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentForward[EquivalentSymmetry[h]]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ 1 == 1 ⇒ True -->

## Possible Issues

[EquivalentBackward]() goes from *b* to *a*, so it does not take a proof of *a*:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentBackward[h][TrueIntroduction]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
