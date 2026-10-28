---
Template: Symbol
Name: LengthMap
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LengthMap
Keywords: [list, length, map, prelude]
SeeAlso: [MapJoin, MapComposition, LengthJoin]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LengthMap]()[*f*, *l*]</code> proves <code>[Length]()[[Map]()[*f*, *l*]] == [Length]()[*l*]</code>.

## Details & Options

- [LengthMap]() is a theorem of the prelude, proved by recursion on *l*.

## Basic Examples

The statement of [LengthMap]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LengthMap]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} ∀_f∶α → β ∀_l∶Lists[α] Length[f /@ l] == Length[l] -->

---

For adding 1 to each natural number of a list:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[l, Lists[Naturals]]}, LengthMap[Function[{Typed[n, Naturals]}, n + 1], l]]]]
```

<!-- => ∀_l∶Lists[ℕ] Length[((n ∶ ℕ) ↦ n + 1) /@ l] == Length[l] -->

## Scope

`"Rewrite"` with an instance replaces the length of the mapped list, here of a map from numbers to Booleans:

```wl
TypeTheoryProof[ForAll[{Typed[f, TypeSpecifier[{Naturals} -> Booleans]], Typed[l, Lists[Naturals]]}, Length[Map[f, l]] + 1 == Length[l] + 1], {
    TypeTheoryTactic["Introduce", f, l],
    TypeTheoryTactic["Rewrite", LengthMap[f, l]]
}]
```

<!-- => Proof complete -->

## Applications

With [LengthJoin](), `"Simplify"` finds the length of a map over a join:

```wl
TypeTheoryProof[ForAll[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, Length[Map[Function[{Typed[n, Naturals]}, 2 n], Join[a, b]]] == Length[a] + Length[b]], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Simplify", {LengthMap, LengthJoin}]
}]
```

<!-- => Proof complete -->

## Properties and Relations

On a list written out the length computes: a map over a list of two elements has length 2:

```wl
TypeTheoryProof[Length[Map[Function[{Typed[n, Naturals]}, n + 1], ListPrepend[1, ListPrepend[2, EmptyList]]]] == 2, {TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Proof complete -->
