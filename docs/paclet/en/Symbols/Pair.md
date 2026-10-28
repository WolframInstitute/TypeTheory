---
Template: Symbol
Name: Pair
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Pair
Keywords: [pair, constructor, product, prelude]
SeeAlso: [CartesianProductType, LeftInjection, OptionSome]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Pair]()[*x*, *y*]</code> is the pair of *x* and *y*, an element of <code>[CartesianProductType]()[*α*, *β*]</code>.

## Details & Options

- [Pair]() is the constructor of [CartesianProductType]().
- *α* and *β* are implicit arguments, found from the types of *x* and *y*.
- <code>[Pair]()[*x*, *y*]</code> displays as (*x*, *y*), and <code>[Pair]()[*x*, [Pair]()[*y*, *z*]]</code> as (*x*, *y*, *z*), as Lean writes them.

## Basic Examples

The statement of [Pair]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Pair]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} α → β → α × β -->

---

A pair of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Pair[2, 3]]]
```

<!-- => ℕ × ℕ -->

## Properties and Relations

Its fields are *x* and *y*:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Pair[2, 3][[2]]]]
```

<!-- => 3 -->
