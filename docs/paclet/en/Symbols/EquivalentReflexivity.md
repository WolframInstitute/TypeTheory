---
Template: Symbol
Name: EquivalentReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentReflexivity
Keywords: [equivalent, reflexivity, prelude, logic]
SeeAlso: [EquivalentSymmetry, EquivalentTransitivity, EquivalentIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentReflexivity]()[*a*]</code> proves <code>[Equivalent]()[*a*, *a*]</code>.

## Details & Options

- [EquivalentReflexivity]() is a theorem of the prelude; its argument *a* is explicit, as for [EqualityReflexivity]().

## Basic Examples

The statement of [EquivalentReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentReflexivity]]
```

<!-- => ∀_a∶Prop (a ⧦ a) -->

---

Every proposition is equivalent to itself:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentReflexivity[1 + 1 == 2]]]
```

<!-- => 1 + 1 == 2 ⧦ 1 + 1 == 2 -->

## Scope

Computation counts: `2 + 2 == 4` computes to `4 == 4`, so [EquivalentReflexivity]() proves the two equivalent:

```wl
TypeTheoryProof[Equivalent[2 + 2 == 4, 4 == 4], {TypeTheoryTactic["Exact", EquivalentReflexivity[4 == 4]]}]
```

<!-- => Proof complete -->

---

`"Apply"` finds the argument from the goal:

```wl
TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Equivalent[p && True, p && True]], {
    TypeTheoryTactic["Introduce", p],
    TypeTheoryTactic["Apply", EquivalentReflexivity]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Equal propositions are equivalent, the converse of [PropositionalExtensionality](): `"Rewrite"` makes the two sides the same:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a == b, Equivalent[a, b]]], {
    TypeTheoryTactic["Introduce", a, b, e],
    TypeTheoryTactic["Rewrite", e]
}]
```

<!-- => Proof, 1 goal: a ∶ Prop, b ∶ Prop, e ∶ a == b ⊢ b ⧦ b -->

[EquivalentReflexivity]() proves what is left:

```wl
TypeTheoryTactic["Exact", EquivalentReflexivity[b]][proof]
```

<!-- => Proof complete -->

## Possible Issues

Its argument is explicit, so `"Exact"` needs it applied, where `"Apply"` finds it:

```wl
TypeTheoryProof[Equivalent[True, True], {TypeTheoryTactic["Exact", EquivalentReflexivity]}]
```

<!-- => Failure["TypeMismatch", ...] -->
