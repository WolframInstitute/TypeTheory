---
Template: Symbol
Name: PropositionalExtensionality
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PropositionalExtensionality
Keywords: [propositional extensionality, axiom, equivalence, equality, prelude, classical logic]
SeeAlso: [Equivalent, EquivalentIntroduction, FunctionExtensionality, Choice, ExcludedMiddle]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PropositionalExtensionality]()[*h*]</code> proves <code>*a* == *b*</code> from a proof *h* of <code>[Equivalent]()[*a*, *b*]</code>.

## Details & Options

- [PropositionalExtensionality]() is one of the three axioms of the prelude. With it, a proposition is determined by when it holds, and equivalent propositions replace each other anywhere, by [EqualitySubstitution]().
- *a* and *b* are implicit arguments, found from the type of *h*.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, does not have it.

## Basic Examples

The statement of [PropositionalExtensionality]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PropositionalExtensionality]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} (a ⧦ b) ⇒ a == b -->

---

[True]() is the same proposition as [True]() and [True]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[h, True]}, AndIntroduction[h, h]], Function[{Typed[h, True && True]}, AndEliminationLeft[h]]]]]]
```

<!-- => True == (True ∧ True) -->

## Scope

A proposition that holds is [True]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p]}, PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[k, p]}, TrueIntroduction], Function[{Typed[k, True]}, h]]]]]]
```

<!-- => ∀_p∶Prop p ⇒ p == True -->

## Applications

`"Apply"` turns an equation of propositions into an equivalence:

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, (p && q) == (q && p)], {
    TypeTheoryTactic["Introduce", p, q],
    TypeTheoryTactic["Apply", PropositionalExtensionality]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, q ∶ Prop ⊢ p ∧ q ⧦ q ∧ p -->

Each direction swaps the parts of the conjunction:

```wl
TypeTheoryTactic["Exact", EquivalentIntroduction[Function[{Typed[h, p && q]}, AndIntroduction[h[[2]], h[[1]]]], Function[{Typed[h, q && p]}, AndIntroduction[h[[2]], h[[1]]]]]][proof]
```

<!-- => Proof complete -->

---

Equivalent propositions replace each other in any statement *P*, with [EqualitySubstitution]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[
    {Typed[P, TypeSpecifier[{TypeUniverse[0]} -> TypeUniverse[0]]], Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, Equivalent[p, q]], Typed[k, P[p]]},
    EqualitySubstitution[PropositionalExtensionality[h], k]
]]]
```

<!-- => ∀_P∶Prop → Prop ∀_p∶Prop ∀_q∶Prop (p ⧦ q) ⇒ P[p] ⇒ P[q] -->

## Properties and Relations

The converse, from `a == b` to `a ⧦ b`, needs no axiom: it holds in the constructive environment, by [EqualitySubstitution]() and [EquivalentReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[
    Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[e, a == b]}, Typed[EqualitySubstitution[e, EquivalentReflexivity[a]], Equivalent[a, b]]],
    TypeTheoryEnvironment["Constructive"]
]]
```

<!-- => ∀_a∶Prop ∀_b∶Prop a == b ⇒ (a ⧦ b) -->
