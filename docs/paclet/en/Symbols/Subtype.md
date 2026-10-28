---
Template: Symbol
Name: Subtype
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Subtype
Keywords: [subtype, property, element, structure, prelude, classical logic]
SeeAlso: [SubtypeIntroduction, ChosenWitness, Exists, Nonempty]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Subtype]()[*P*]</code> is the type of the elements *x* of a type that come with a proof of <code>*P*[*x*]</code>.

## Details & Options

- [Subtype]() is an inductive type of the prelude, with the one constructor [SubtypeIntroduction](). The type of the elements is an implicit argument, found from the type of *P*.
- An element `s` of <code>[Subtype]()[*P*]</code> is a structure: `s[[1]]` is the element and `s[[2]]` the proof of its property.
- For elements in `Sort u`, <code>[Subtype]()[*P*]</code> is in `Sort (max 1 u)`: it is a type of data even when its elements are proofs.
- <code>[Subtype]()[[Function]()[{[Typed]()[*x*, *A*]}, *p*]]</code> displays as `{x ∶ A // p}`, as Lean writes `{ x // p }`.

## Basic Examples

The type of [Subtype]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Subtype]]
```

<!-- => ∀_{α ∶ Sort u} (α → Prop) → Sort (max 1 u) -->

---

The second field of an element proves the property of the first:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[s, Subtype[Function[{Typed[n, Naturals]}, 2 <= n]]]}, s[[2]]]]]
```

<!-- => ∀_s∶{n∶ℕ // 2 ≤ n} 2 ≤ s〚1〛 -->

## Scope

The first field of an element computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[SubtypeIntroduction[4, LessEqualStep[LessEqualStep[LessEqualReflexivity]]], Subtype[Function[{Typed[n, Naturals]}, 2 <= n]]][[1]]]]
```

<!-- => 4 -->
