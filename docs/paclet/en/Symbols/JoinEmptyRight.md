---
Template: Symbol
Name: JoinEmptyRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/JoinEmptyRight
Keywords: [list, join, append, empty list, identity, prelude]
SeeAlso: [JoinAssociativity, Lists, EmptyList]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[JoinEmptyRight]()[*l*]</code> proves <code>[Join]()[*l*, [EmptyList]()] == *l*</code>.

## Details & Options

- [JoinEmptyRight]() is a theorem of the prelude, proved by recursion on *l*.

## Basic Examples

The statement of [JoinEmptyRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[JoinEmptyRight]]
```

<!-- => ∀_{α ∶ Type u} ∀_l∶Lists[α] Join[l, {}] == l -->

---

For lists of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[l, Lists[Naturals]]}, JoinEmptyRight[l]]]]
```

<!-- => ∀_l∶Lists[ℕ] Join[l, {}] == l -->

## Scope

The tactic `"Rewrite"` removes an empty list joined on the right:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Join[Join[l, EmptyList], l] == Join[l, l]], {
	TypeTheoryTactic["Introduce", l],
	TypeTheoryTactic["Rewrite", JoinEmptyRight]
}]
```

<!-- => Proof complete -->
