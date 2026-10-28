---
Template: Symbol
Name: MapJoin
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MapJoin
Keywords: [list, map, join, prelude]
SeeAlso: [LengthMap, MapComposition, JoinAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MapJoin]()[*f*, *a*, *b*]</code> proves <code>[Map]()[*f*, [Join]()[*a*, *b*]] == [Join]()[[Map]()[*f*, *a*], [Map]()[*f*, *b*]]</code>.

## Details & Options

- [MapJoin]() is a theorem of the prelude, proved by recursion on *a*.

## Basic Examples

The statement of [MapJoin]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MapJoin]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} ∀_f∶α → β ∀_a∶Lists[α] ∀_b∶Lists[α] f /@ Join[a, b] == Join[f /@ a, f /@ b] -->

---

For adding 1 to each natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, MapJoin[Function[{Typed[n, Naturals]}, n + 1], a, b]]]]
```

<!-- => ∀_a∶Lists[ℕ] ∀_b∶Lists[ℕ] ((n ∶ ℕ) ↦ n + 1) /@ Join[a, b] == Join[((n ∶ ℕ) ↦ n + 1) /@ a, ((n ∶ ℕ) ↦ n + 1) /@ b] -->

## Scope

[Map]() and [Join]() compute by recursion on their first list, so with the first list written out both sides compute, whatever the second:

```wl
TypeTheoryProof[ForAll[{Typed[b, Lists[Naturals]]},
    Map[Function[{Typed[n, Naturals]}, n + 1], Join[ListPrepend[1, EmptyList], b]] == Join[Map[Function[{Typed[n, Naturals]}, n + 1], ListPrepend[1, EmptyList]], Map[Function[{Typed[n, Naturals]}, n + 1], b]]
], {
    TypeTheoryTactic["Introduce", b],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

## Applications

`"Simplify"` distributes a map over several joins:

```wl
TypeTheoryProof[ForAll[
    {Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]], Typed[c, Lists[Naturals]]},
    Map[f, Join[a, Join[b, c]]] == Join[Map[f, a], Join[Map[f, b], Map[f, c]]]
], {
    TypeTheoryTactic["Introduce", f, a, b, c],
    TypeTheoryTactic["Simplify", {MapJoin}]
}]
```

<!-- => Proof complete -->

---

[Append]() joins a list of one element, so [MapJoin]() maps over it too:

```wl
TypeTheoryProof[ForAll[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[l, Lists[Naturals]], Typed[x, Naturals]}, Map[f, Append[l, x]] == Append[Map[f, l], f[x]]], {
    TypeTheoryTactic["Introduce", f, l, x],
    TypeTheoryTactic["Exact", MapJoin[f, l, ListPrepend[x, EmptyList]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

With the first list a variable, neither side computes, so the law takes the theorem:

```wl
TypeTheoryProof[ForAll[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, Map[f, Join[a, b]] == Join[Map[f, a], Map[f, b]]], {
    TypeTheoryTactic["Introduce", f, a, b],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
