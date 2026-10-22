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
