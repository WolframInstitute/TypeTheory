---
Template: Symbol
Name: EquivalentForward
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentForward
Keywords: [equivalent, forward, prelude, logic]
SeeAlso: [EquivalentBackward, EquivalentIntroduction, EquivalentSymmetry]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentForward]()[*h*]</code> proves <code>[Implies]()[*a*, *b*]</code> from a proof *h* of <code>[Equivalent]()[*a*, *b*]</code>.

## Details & Options

- [EquivalentForward]() is a theorem of the prelude, the first field of the proof: `h[[1]]`.
- *a* and *b* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [EquivalentForward]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentForward]]
```

<!-- => ∀_{a∶Prop} ∀_{b∶Prop} (a ⧦ b) ⇒ a ⇒ b -->

---

From a proof of <code>[Equivalent]()[[True](), 1 == 1]</code>, a proof of `1 == 1`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentForward[h][TrueIntroduction]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ 1 == 1 -->

## Scope

With `"Apply"`, <code>[EquivalentForward]()[*h*]</code> turns a goal *b* into the goal *a*:

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Equivalent[p, q], Implies[p, q]]], {
    TypeTheoryTactic["Introduce", p, q, h, hp],
    TypeTheoryTactic["Apply", EquivalentForward[h]]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, q ∶ Prop, h ∶ p ⧦ q, hp ∶ p ⊢ p -->

`"Assumption"` closes it with the hypothesis `hp`:

```wl
TypeTheoryTactic["Assumption"][proof]
```

<!-- => Proof complete -->

## Applications

Equivalent propositions fail together: a proof `ha` of *a* would give one of *b*, which `nb` refutes:

```wl
TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], Implies[Not[b], Not[a]]]], {
    TypeTheoryTactic["Introduce", a, b, h, nb, ha],
    TypeTheoryTactic["Exact", nb[EquivalentForward[h][ha]]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

<code>[EquivalentForward]()[*h*]</code> proves what the first field `h[[1]]` proves:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, h[[1]]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ True ⇒ 1 == 1 -->

## Possible Issues

[EquivalentForward]() goes from *a* to *b*, so it does not take a proof of *b*:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentForward[h][EqualityReflexivity[1]]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
