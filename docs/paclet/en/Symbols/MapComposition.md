---
Template: Symbol
Name: MapComposition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MapComposition
Keywords: [list, map, composition, functor, prelude]
SeeAlso: [MapJoin, LengthMap, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MapComposition]()[*f*, *g*, *l*]</code> proves <code>[Map]()[*f*, [Map]()[*g*, *l*]] == [Map]()[[Composition]()[*f*, *g*], *l*]</code>.

## Details & Options

- [MapComposition]() is a theorem of the prelude, proved by recursion on *l*.

## Basic Examples

The statement of [MapComposition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MapComposition]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} ∀_{γ ∶ Type w} ∀_f∶β → γ ∀_g∶α → β ∀_l∶Lists[α] f /@ g /@ l == (f @* g) /@ l -->

---

Doubling, then adding 1:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[l, Lists[Naturals]]}, MapComposition[Function[{Typed[n, Naturals]}, n + 1], Function[{Typed[n, Naturals]}, 2 * n], l]]]]
```

<!-- => ∀_l∶Lists[ℕ] ((n ∶ ℕ) ↦ n + 1) /@ ((n ∶ ℕ) ↦ 2 n) /@ l == (((n ∶ ℕ) ↦ n + 1) @* ((n ∶ ℕ) ↦ 2 n)) /@ l -->

## Scope

Two maps fuse into one: the composition of doubling and adding 1 computes to `2 n + 1`, so the instance proves the fused form:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Map[Function[{Typed[n, Naturals]}, n + 1], Map[Function[{Typed[n, Naturals]}, 2 * n], l]] == Map[Function[{Typed[n, Naturals]}, 2 * n + 1], l]], {
    TypeTheoryTactic["Introduce", l],
    TypeTheoryTactic["Exact", MapComposition[Function[{Typed[n, Naturals]}, n + 1], Function[{Typed[n, Naturals]}, 2 * n], l]]
}]
```

<!-- => Proof complete -->

## Applications

`"Simplify"` fuses any number of maps, here three:

```wl
TypeTheoryProof[ForAll[
    {Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[g, TypeSpecifier[{Naturals} -> Naturals]], Typed[h, TypeSpecifier[{Naturals} -> Naturals]], Typed[l, Lists[Naturals]]},
    Map[f, Map[g, Map[h, l]]] == Map[Composition[f, Composition[g, h]], l]
], {
    TypeTheoryTactic["Introduce", f, g, h, l],
    TypeTheoryTactic["Simplify", {MapComposition}]
}]
```

<!-- => Proof complete -->

## Properties and Relations

On a list written out both sides compute, so `"Reflexivity"` proves the instance:

```wl
TypeTheoryProof[
    Map[Function[{Typed[n, Naturals]}, n + 1], Map[Function[{Typed[n, Naturals]}, 2 * n], ListPrepend[1, ListPrepend[2, EmptyList]]]] == Map[Composition[Function[{Typed[n, Naturals]}, n + 1], Function[{Typed[n, Naturals]}, 2 * n]], ListPrepend[1, ListPrepend[2, EmptyList]]],
    {TypeTheoryTactic["Reflexivity"]}
]
```

<!-- => Proof complete -->

## Possible Issues

<code>[Composition]()[*f*, *g*]</code> applies *g* first, as the inner map does: doubling and then adding 1 takes 1 and 2 to 3 and 5:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Map[Composition[Function[{Typed[n, Naturals]}, n + 1], Function[{Typed[n, Naturals]}, 2 * n]], ListPrepend[1, ListPrepend[2, EmptyList]]]],
    TypeTheoryTerm[ListPrepend[3, ListPrepend[5, EmptyList]]]
]
```

<!-- => True -->
