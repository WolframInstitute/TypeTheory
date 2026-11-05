---
Template: Symbol
Name: DisjointUnionType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DisjointUnionType
Keywords: [disjoint union, sum, coproduct, prelude, inductive type]
SeeAlso: [CartesianProductType, Option]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DisjointUnionType]()[*α*, *β*]</code> is the type of the elements of *α* and of *β*, each tagged with its side.

## Details & Options

- [DisjointUnionType]() is an inductive type of the prelude, with the constructors `"left"` and `"right"`, as Lean's `Sum`.
- For *α* in `Type u` and *β* in `Type v`, <code>[DisjointUnionType]()[*α*, *β*]</code> is in `Type (max u v)`.
- <code>[DisjointUnionType]()[*α*, *β*]</code> displays as *α* ⊕ *β*, as Lean writes `Sum`; × binds tighter than ⊕, so *α* × *β* ⊕ *γ* is a sum of a product.

## Basic Examples

The type of [DisjointUnionType]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DisjointUnionType]]
```

<!-- => Type u → Type v → Type (max u v) -->

---

A natural number on the left of a disjoint union with the Booleans:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed["left"[2], DisjointUnionType[Naturals, Booleans]]]]
```

<!-- => ℕ ⊕ 𝔹 -->

## Scope

A disjoint union of two types in `Type` is in `Type`:

```wl
TypeOf[TypeTheoryTerm[DisjointUnionType[Naturals, Booleans]]]
```

<!-- => Type -->

## Applications

A function defined by cases on the side, with the recursor of [DisjointUnionType](): a number stays as it is, and a Boolean gives 0:

```wl
sides = TypeTheoryEnvironment[{TypeTheoryDefinition[SideNumber, Function[{Typed[s, DisjointUnionType[Naturals, Booleans]]},
    InductiveRecursor[DisjointUnionType][Typed[t, DisjointUnionType[Naturals, Booleans]] |-> Naturals, Typed[n, Naturals] |-> n, Typed[b, Booleans] |-> 0, s]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

On the left side:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SideNumber["left"[5]], sides]]
```

<!-- => 5 -->

On the right side:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SideNumber["right"["true"]], sides]]
```

<!-- => 0 -->

## Properties and Relations

Every element is on one side: `"Cases"` gives a goal for each, which `"orIntroductionLeft"` and `"orIntroductionRight"` prove:

```wl
TypeTheoryProof[ForAll[{Typed[s, DisjointUnionType[Naturals, Booleans]]}, Or[Exists[{Typed[n, Naturals]}, s == "left"[n]], Exists[{Typed[b, Booleans]}, s == "right"[b]]]], {
    TypeTheoryTactic["Introduce", s],
    TypeTheoryTactic["Cases", s],
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Exact", "orIntroductionLeft"["existsIntroduction"[n, "equalityReflexivity"["left"[n]]]]],
    TypeTheoryTactic["Introduce", b],
    TypeTheoryTactic["Exact", "orIntroductionRight"["existsIntroduction"[b, "equalityReflexivity"["right"[b]]]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The sides are types: propositions such as [True]() and [False]() are not in `Type u`, and [Or]() is their disjunction:

```wl
TypeTheoryCheck[TypeTheoryTerm[DisjointUnionType[True, False]]]
```

<!-- => Failure["TypeMismatch", ...] -->
