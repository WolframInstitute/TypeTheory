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
