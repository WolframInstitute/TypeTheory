---
Template: Symbol
Name: RightInjection
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RightInjection
Keywords: [disjoint union, sum, injection, constructor, prelude]
SeeAlso: [DisjointUnion, LeftInjection, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[RightInjection]()[*y*]</code> is *y* on the right side of <code>[DisjointUnion]()[*α*, *β*]</code>.

## Details & Options

- [RightInjection]() is the second constructor of [DisjointUnion]().
- *β* is found from the type of *y*; *α* is found from the expected type.

## Basic Examples

The statement of [RightInjection]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RightInjection]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} β → DisjointUnion[α, β] -->

---

The Boolean `"true"` on the right:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[RightInjection["true"], DisjointUnion[Naturals, Booleans]]]]
```

<!-- => DisjointUnion[ℕ, 𝔹] -->

## Applications

The recursor of [DisjointUnion]() takes a function for each side, and applies the right one to the element of a [RightInjection]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[DisjointUnion][
    Function[{Typed[t, DisjointUnion[Naturals, Booleans]]}, Naturals],
    Function[{Typed[n, Naturals]}, n + 1],
    Function[{Typed[b, Booleans]}, 0],
    RightInjection["true"]
]]]
```

<!-- => 0 -->

---

With [LeftInjection](), it swaps the sides of a disjoint union:

```wl
swap = TypeTheoryTerm[Function[{Typed[s, DisjointUnion[Naturals, Booleans]]}, InductiveRecursor[DisjointUnion][
    Function[{Typed[t, DisjointUnion[Naturals, Booleans]]}, DisjointUnion[Booleans, Naturals]],
    Function[{Typed[n, Naturals]}, RightInjection[n]],
    Function[{Typed[b, Booleans]}, LeftInjection[b]],
    s
]]]
```

<!-- => (s ∶ DisjointUnion[ℕ, 𝔹]) ↦ DisjointUnion_rec[(t ∶ DisjointUnion[ℕ, 𝔹]) ↦ DisjointUnion[𝔹, ℕ], (n ∶ ℕ) ↦ RightInjection[n], (b ∶ 𝔹) ↦ LeftInjection[b], s] -->

Its type:

```wl
TypeTheoryCheck[swap]
```

<!-- => DisjointUnion[ℕ, 𝔹] → DisjointUnion[𝔹, ℕ] -->

The swap moves `"true"` from the right side to the left:

```wl
WeakHeadNormalForm[TypeTheoryTerm[swap[RightInjection["true"]]]]
```

<!-- => LeftInjection[true] -->

## Possible Issues

Without an expected type, the left side is unknown:

```wl
TypeTheoryCheck[TypeTheoryTerm[RightInjection["true"]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->
