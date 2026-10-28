---
Template: Symbol
Name: EquivalentIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentIntroduction
Keywords: [equivalent, introduction, prelude, logic]
SeeAlso: [EquivalentForward, EquivalentBackward, EquivalentReflexivity, AndIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentIntroduction]()[*f*, *g*]</code> proves <code>[Equivalent]()[*a*, *b*]</code> from a proof *f* of <code>[Implies]()[*a*, *b*]</code> and a proof *g* of <code>[Implies]()[*b*, *a*]</code>.

## Details & Options

- [Equivalent]() is an inductive proposition of the prelude with two parameters, *a* and *b*, and [EquivalentIntroduction]() is its one constructor; its fields are the two implications.
- *a* and *b* are implicit arguments, found from the types of *f* and *g*.
- A proof `h` of <code>[Equivalent]()[*a*, *b*]</code> is a structure: `h[[1]]` proves <code>[Implies]()[*a*, *b*]</code> and `h[[2]]` proves <code>[Implies]()[*b*, *a*]</code>.

## Basic Examples

The statement of [EquivalentIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentIntroduction]]
```

<!-- => ∀_{a∶Prop} ∀_{b∶Prop} (a ⇒ b) ⇒ (b ⇒ a) ⇒ (a ⧦ b) -->

---

*p* is equivalent to *p* and *p*:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]]}, EquivalentIntroduction[Function[{Typed[h, p && p]}, AndEliminationLeft[h]], Function[{Typed[h, p]}, AndIntroduction[h, h]]]]]]
```

<!-- => ∀_p∶Prop (p ∧ p ⧦ p) -->

## Scope

`"Apply"` leaves a goal for each implication:

```wl
TypeTheoryProof[Equivalent[True, 1 + 1 == 2], {TypeTheoryTactic["Apply", EquivalentIntroduction]}]
```

<!-- => Proof, 2 goals: ⊢ True ⇒ 1 + 1 == 2; ⊢ 1 + 1 == 2 ⇒ True -->

---

[EquivalentIntroduction]() is the one constructor of [Equivalent](), so `"Constructor"` applies it, and each implication is then proved in turn:

```wl
TypeTheoryProof[Equivalent[True, 1 + 1 == 2], {
    TypeTheoryTactic["Constructor"],
    TypeTheoryTactic["Introduce", h],
    TypeTheoryTactic["Reflexivity"],
    TypeTheoryTactic["Introduce", h],
    TypeTheoryTactic["Exact", TrueIntroduction]
}]
```

<!-- => Proof complete -->

## Applications

With [PropositionalExtensionality](), an equivalence makes two propositions equal, here `p && True` and `p`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]]},
    PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[h, p && True]}, AndEliminationLeft[h]], Function[{Typed[h, p]}, AndIntroduction[h, TrueIntroduction]]]]
]]]
```

<!-- => ∀_p∶Prop (p ∧ True) == p -->

## Possible Issues

The second implication must go back the other way, so two in the same direction do not make an equivalence:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentIntroduction[Function[{Typed[h, True]}, EqualityReflexivity[1]], Function[{Typed[h, True]}, EqualityReflexivity[1]]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
