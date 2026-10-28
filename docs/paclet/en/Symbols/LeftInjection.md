---
Template: Symbol
Name: LeftInjection
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LeftInjection
Keywords: [disjoint union, sum, injection, constructor, prelude]
SeeAlso: [DisjointUnion, RightInjection, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LeftInjection]()[*x*]</code> is *x* on the left side of <code>[DisjointUnion]()[*α*, *β*]</code>.

## Details & Options

- [LeftInjection]() is the first constructor of [DisjointUnion]().
- *α* is found from the type of *x*; *β* is found from the expected type.

## Basic Examples

The statement of [LeftInjection]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LeftInjection]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} α → DisjointUnion[α, β] -->

---

2 on the left:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[LeftInjection[2], DisjointUnion[Naturals, Booleans]]]]
```

<!-- => DisjointUnion[ℕ, 𝔹] -->

## Scope

[Typed]() gives the type with its other side, here in a function:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, Typed[LeftInjection[n], DisjointUnion[Naturals, Booleans]]]]]
```

<!-- => ℕ → DisjointUnion[ℕ, 𝔹] -->

## Applications

The recursor of [DisjointUnion]() takes a function for each side, and applies the left one to the element of a [LeftInjection]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[DisjointUnion][
    Function[{Typed[t, DisjointUnion[Naturals, Booleans]]}, Naturals],
    Function[{Typed[n, Naturals]}, n + 1],
    Function[{Typed[b, Booleans]}, 0],
    LeftInjection[2]
]]]
```

<!-- => 3 -->

## Possible Issues

Without an expected type, the right side is unknown:

```wl
TypeTheoryCheck[TypeTheoryTerm[LeftInjection[2]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->
