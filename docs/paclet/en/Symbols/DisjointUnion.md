---
Template: Symbol
Name: DisjointUnion
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DisjointUnion
Keywords: [disjoint union, sum, coproduct, prelude, inductive type]
SeeAlso: [LeftInjection, RightInjection, CartesianProduct, Option]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DisjointUnion]()[*α*, *β*]</code> is the type of the elements of *α* and of *β*, each tagged with its side.

## Details & Options

- [DisjointUnion]() is an inductive type of the prelude, with the constructors [LeftInjection]() and [RightInjection](), as Lean's `Sum`.
- For *α* in `Type u` and *β* in `Type v`, <code>[DisjointUnion]()[*α*, *β*]</code> is in `Type (max u v)`.

## Basic Examples

The type of [DisjointUnion]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DisjointUnion]]
```

<!-- => Type u → Type v → Type (max u v) -->

---

A natural number on the left of a disjoint union with the Booleans:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[LeftInjection[2], DisjointUnion[Naturals, Booleans]]]]
```

<!-- => DisjointUnion[ℕ, 𝔹] -->

## Scope

A disjoint union of two types in `Type` is in `Type`:

```wl
TypeOf[TypeTheoryTerm[DisjointUnion[Naturals, Booleans]]]
```

<!-- => Type -->

## Applications

A function defined by cases on the side, with the recursor of [DisjointUnion](): a number stays as it is, and a Boolean gives 0:

```wl
sides = TypeTheoryEnvironment[{TypeTheoryDefinition[SideNumber, Function[{Typed[s, DisjointUnion[Naturals, Booleans]]},
    InductiveRecursor[DisjointUnion][Function[{Typed[t, DisjointUnion[Naturals, Booleans]]}, Naturals], Function[{Typed[n, Naturals]}, n], Function[{Typed[b, Booleans]}, 0], s]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

On the left side:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SideNumber[LeftInjection[5]], sides]]
```

<!-- => 5 -->

On the right side:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SideNumber[RightInjection["true"]], sides]]
```

<!-- => 0 -->

## Properties and Relations

Every element is on one side: `"Cases"` gives a goal for each, which [OrIntroductionLeft]() and [OrIntroductionRight]() prove:

```wl
TypeTheoryProof[ForAll[{Typed[s, DisjointUnion[Naturals, Booleans]]}, Or[Exists[{Typed[n, Naturals]}, s == LeftInjection[n]], Exists[{Typed[b, Booleans]}, s == RightInjection[b]]]], {
    TypeTheoryTactic["Introduce", s],
    TypeTheoryTactic["Cases", s],
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Exact", OrIntroductionLeft[ExistsIntroduction[n, EqualityReflexivity[LeftInjection[n]]]]],
    TypeTheoryTactic["Introduce", b],
    TypeTheoryTactic["Exact", OrIntroductionRight[ExistsIntroduction[b, EqualityReflexivity[RightInjection[b]]]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The sides are types: propositions such as [True]() and [False]() are not in `Type u`, and [Or]() is their disjunction:

```wl
TypeTheoryCheck[TypeTheoryTerm[DisjointUnion[True, False]]]
```

<!-- => Failure["TypeMismatch", ...] -->
