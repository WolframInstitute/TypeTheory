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

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} ∀_f∶α → β ∀_a∶{α} ∀_b∶{α} f /@ Join[a, b] == Join[f /@ a, f /@ b] -->

---

For adding 1 to each natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, {Naturals}], Typed[b, {Naturals}]}, MapJoin[Function[{Typed[n, Naturals]}, n + 1], a, b]]]]
```

<!-- => ∀_a∶{ℕ} ∀_b∶{ℕ} ((n ∶ ℕ) ↦ n + 1) /@ Join[a, b] == Join[((n ∶ ℕ) ↦ n + 1) /@ a, ((n ∶ ℕ) ↦ n + 1) /@ b] -->

## Scope

[Map]() and [Join]() compute by recursion on their first list, so with the first list written out both sides compute, whatever the second:

```wl
TypeTheoryProof[ForAll[{Typed[b, {Naturals}]},
    Map[Function[{Typed[n, Naturals]}, n + 1], Join[Prepend[{}, 1], b]] == Join[Map[Function[{Typed[n, Naturals]}, n + 1], Prepend[{}, 1]], Map[Function[{Typed[n, Naturals]}, n + 1], b]]
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
    {Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[a, {Naturals}], Typed[b, {Naturals}], Typed[c, {Naturals}]},
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
TypeTheoryProof[ForAll[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[l, {Naturals}], Typed[x, Naturals]}, Map[f, Append[l, x]] == Append[Map[f, l], f[x]]], {
    TypeTheoryTactic["Introduce", f, l, x],
    TypeTheoryTactic["Exact", MapJoin[f, l, Prepend[{}, x]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

With the first list a variable, neither side computes, so the law takes the theorem:

```wl
TypeTheoryProof[ForAll[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[a, {Naturals}], Typed[b, {Naturals}]}, Map[f, Join[a, b]] == Join[Map[f, a], Map[f, b]]], {
    TypeTheoryTactic["Introduce", f, a, b],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
