---
Template: Symbol
Name: CartesianProductType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CartesianProductType
Keywords: [pair, product, Cartesian product, structure, prelude, inductive type]
SeeAlso: [Pair, DisjointUnionType, Option, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[CartesianProductType]()[*α*, *β*]</code> is the type of pairs of an element of *α* and an element of *β*.

## Details & Options

- [CartesianProductType]() is an inductive type of the prelude, with the one constructor [Pair](), as Lean's `Prod`.
- It is a structure: a pair `p` has the fields `p[[1]]` and `p[[2]]`.
- For *α* in `Type u` and *β* in `Type v`, <code>[CartesianProductType]()[*α*, *β*]</code> is in `Type (max u v)`.

## Basic Examples

The type of [CartesianProductType]():

```wl
TypeTheoryCheck[TypeTheoryTerm[CartesianProductType]]
```

<!-- => Type u → Type v → Type (max u v) -->

---

A pair of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Pair[2, 3]]]
```

<!-- => CartesianProductType[ℕ, ℕ] -->

## Scope

The fields of a pair compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Pair[2, 3][[2]]]]
```

<!-- => 3 -->

---

A function takes the second field of any pair:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, CartesianProductType[Naturals, Booleans]]}, p[[2]]]]]
```

<!-- => CartesianProductType[ℕ, 𝔹] → 𝔹 -->
