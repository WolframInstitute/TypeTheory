---
Template: Symbol
Name: AndEliminationRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AndEliminationRight
Keywords: [And, conjunction, elimination, theorem, prelude, logic]
SeeAlso: [AndEliminationLeft, AndIntroduction, TypeTheoryProof]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[AndEliminationRight]()[*h*]</code> proves *b* from a proof *h* of <code>[And]()[*a*, *b*]</code>.

## Details & Options

- [AndEliminationRight]() is a theorem of the prelude, proved with the recursor of [And]().
- *a* and *b* are implicit arguments, found from the type of *h*.
- <code>[AndEliminationRight]()[*h*]</code> proves what the field `h[[2]]` proves.

## Basic Examples

The type of [AndEliminationRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AndEliminationRight]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} (a ∧ b) ⇒ b -->

---

Use it on a hypothesis:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, And[True, 1 == 1]]}, AndEliminationRight[h]]]]
```

<!-- => (True ∧ 1 == 1) ⇒ 1 == 1 -->

## Scope

Conjunctions group to the right, so the last part of `a && b && c` takes [AndEliminationRight]() twice:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, True && 1 == 1 && 2 == 2]}, AndEliminationRight[AndEliminationRight[h]]]]]
```

<!-- => (True ∧ 1 == 1 ∧ 2 == 2) ⇒ 2 == 2 -->

---

Applied to a goal, `"Apply"` cannot tell the left side of the conjunction, so it leaves it to be found:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[And[a, b], b]], {
    TypeTheoryTactic["Introduce", a, b, h],
    TypeTheoryTactic["Apply", AndEliminationRight]
}]
```

<!-- => Proof, 2 goals: a ∶ Prop, b ∶ Prop, h ∶ a ∧ b ⊢ ?m ∧ b; the same hypotheses ⊢ Prop -->

The hypothesis `h` solves both goals:

```wl
TypeTheoryTactic["Exact", h][proof]
```

<!-- => Proof complete -->

## Applications

From *a* and *b*, prove *b* or *c*: `"Apply"` chooses the left side of the disjunction, and [AndEliminationRight]() proves it:

```wl
TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[c, TypeUniverse[0]]}, Implies[And[a, b], Or[b, c]]], {
    TypeTheoryTactic["Introduce", a, b, c, h],
    TypeTheoryTactic["Apply", OrIntroductionLeft],
    TypeTheoryTactic["Exact", AndEliminationRight[h]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

With [AndEliminationLeft]() it takes a conjunction apart, and [AndIntroduction]() puts the parts back together:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[h, a && b]}, AndIntroduction[AndEliminationLeft[h], AndEliminationRight[h]]]]]
```

<!-- => ∀_a∶Prop ∀_b∶Prop (a ∧ b) ⇒ (a ∧ b) -->
