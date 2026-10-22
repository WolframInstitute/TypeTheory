---
Template: Symbol
Name: Pair
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Pair
Keywords: [pair, constructor, product, prelude]
SeeAlso: [CartesianProduct, LeftInjection, OptionSome]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Pair]()[*x*, *y*]</code> is the pair of *x* and *y*, an element of <code>[CartesianProduct]()[*α*, *β*]</code>.

## Details & Options

- [Pair]() is the constructor of [CartesianProduct]().
- *α* and *β* are implicit arguments, found from the types of *x* and *y*.

## Basic Examples

The statement of [Pair]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Pair]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} α → β → CartesianProduct[α, β] -->

---

A pair of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Pair[2, 3]]]
```

<!-- => CartesianProduct[ℕ, ℕ] -->

## Properties and Relations

Its fields are *x* and *y*:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Pair[2, 3][[2]]]]
```

<!-- => 3 -->
