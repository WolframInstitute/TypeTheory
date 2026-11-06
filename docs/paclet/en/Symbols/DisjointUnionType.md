---
Template: Symbol
Name: DisjointUnionType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DisjointUnionType
Keywords: [disjoint union, sum, sum type, Alternatives, |, coproduct, tagged union, either, case analysis, prelude, inductive type, Sum]
SeeAlso: [CartesianProductType, Option, InductiveRecursor, Or, Alternatives]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, TheWolframLanguage]
---

## Usage

<code>[DisjointUnionType]()[*α*, *β*]</code> is the type of the elements of *α* and of *β*, each tagged with its side.

<code>*α* | *β*</code> is <code>[DisjointUnionType]()[*α*, *β*]</code>, as the pattern `_α | _β` matches either.

## Details & Options

- [DisjointUnionType]() is an inductive type of the prelude, with the constructors `"left"` and `"right"`, as Lean's `Sum`: <code>"left"[*x*]</code> for *x* in *α*, and <code>"right"[*y*]</code> for *y* in *β*.
- Each constructor takes both types implicitly, and its value gives only one of them, so an element needs the type it is expected to have, given by [Typed]() or by where it is used.
- Its recursor, <code>[InductiveRecursor]()[[DisjointUnionType]()]</code>, takes a function for each side: a function on a disjoint union is defined by cases on the side, and `"Cases"` splits a proof the same way.
- The sides are told apart: `"left"[x]` is never `"right"[y]`, which the recursor into Prop proves. `"Decide"` does not decide such equations, since the prelude has no instance of [Decidable]() for them.
- For *α* in `Type u` and *β* in `Type v`, <code>[DisjointUnionType]()[*α*, *β*]</code> is in `Type (max u v)`. For propositions, [Or]() is the disjunction.
- <code>[DisjointUnionType]()[*α*, *β*]</code> is written and displays as <code>*α* | *β*</code>, as [Alternatives]() writes the pattern of either; <code>*α* | *β* | *γ*</code> is <code>*α* | (*β* | *γ*)</code>. × binds tighter than |, so <code>*α* × *β* | *γ*</code> is a sum of a product.
- Where a sum is expected, a value of either side is a value of the sum, injected with `"left"` or `"right"` by its type; a string, or a symbol that names nothing, is a value of the first side that takes it.

## Basic Examples

The type of [DisjointUnionType]():

```wl
TypeTheoryType[DisjointUnionType]
```

<!-- => Type u → Type v → Type (max u v) -->

---

A natural number on the left of a disjoint union with the Booleans:

```wl
TypeTheoryType[Typed["left"[2], DisjointUnionType[Naturals, Booleans]]]
```

<!-- => ℕ | 𝔹 -->

---

A list of numbers and Booleans, each on its side:

```wl
TypeTheoryType[Typed[{"left"[1], "right"["true"]}, {DisjointUnionType[Naturals, Booleans]}]]
```

<!-- => {ℕ | 𝔹} -->

---

Written as alternatives, where the sum is expected, each element is injected on the side its type gives:

```wl
TypeTheoryType[Typed[{1, "true", 7}, {Naturals | Booleans}]]
```

<!-- => {ℕ | 𝔹} -->

## Scope

A disjoint union of two types in `Type` is in `Type`:

```wl
TypeTheoryType[DisjointUnionType[Naturals, Booleans]]
```

<!-- => Type -->

---

`"left"` takes both types implicitly:

```wl
TypeTheoryType["left"]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} α → (α | β) -->

---

The recursor, with a case for each side:

```wl
TypeTheoryType[InductiveRecursor[DisjointUnionType]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} ∀_m∶(α | β) → Sort w (∀_x∶α m[left[x]]) → (∀_y∶β m[right[y]]) → ∀_t∶α | β m[t] -->

---

A sum of a product shows no parentheses, since × binds tighter:

```wl
TypeTheoryTerm[DisjointUnionType[CartesianProductType[Naturals, Naturals], Booleans]]
```

<!-- => ℕ × ℕ | 𝔹 -->

---

A product of a sum does:

```wl
TypeTheoryTerm[CartesianProductType[Naturals, DisjointUnionType[Naturals, Booleans]]]
```

<!-- => ℕ × (ℕ | 𝔹) -->

## Applications

A function defined by cases on the side, with the recursor of [DisjointUnionType](): a number stays as it is, and a Boolean counts as 0 or 1:

```wl
counts = TypeTheoryEnvironment[{TypeTheoryDefinition[AsNumber, Typed[
    Typed[s, DisjointUnionType[Naturals, Booleans]] |-> InductiveRecursor[DisjointUnionType][
        Typed[t, DisjointUnionType[Naturals, Booleans]] |-> Naturals,
        Typed[n, Naturals] |-> n,
        Typed[b, Booleans] |-> InductiveRecursor[Booleans][Typed[c, Booleans] |-> Naturals, 0, 1, b],
        s
    ],
    TypeSpecifier[{DisjointUnionType[Naturals, Booleans]} -> Naturals]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 251 constants -->

On the left side:

```wl
WeakHeadNormalForm[TypeTheoryTerm[AsNumber["left"[5]], counts]]
```

<!-- => 5 -->

On the right side:

```wl
WeakHeadNormalForm[TypeTheoryTerm[AsNumber["right"["true"]], counts]]
```

<!-- => 1 -->

Over a mixed list:

```wl
NormalForm[TypeTheoryTerm[Map[AsNumber, {"left"[3], "right"["true"], "left"[4]}], counts]]
```

<!-- => {3, 1, 4} -->

## Properties and Relations

Every element is on one side: `"Cases"` gives a goal for each, which `"orIntroductionLeft"` and `"orIntroductionRight"` prove:

```wl
TypeTheoryProof[ForAll[{Typed[s, DisjointUnionType[Naturals, Booleans]]}, Or[Exists[{Typed[n, Naturals]}, s == "left"[n]], Exists[{Typed[b, Booleans]}, s == "right"[b]]]], {
    "Introduce"[s],
    "Cases"[s],
    "Introduce"[n],
    "Exact"["orIntroductionLeft"["existsIntroduction"[n, "equalityReflexivity"["left"[n]]]]],
    "Introduce"[b],
    "Exact"["orIntroductionRight"["existsIntroduction"[b, "equalityReflexivity"["right"[b]]]]]
}]
```

<!-- => Proof complete -->

---

No element is on both sides: the recursor of [Equal]() carries a proof of [True]() along the equation to the proposition that is [True]() on the left and [False]() on the right:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals], Typed[b, Booleans]}, Not[Typed["left"[n], DisjointUnionType[Naturals, Booleans]] == "right"[b]]], {
    "Introduce"[n, b, h],
    "Exact"[InductiveRecursor[Equal][
        {Typed[y, DisjointUnionType[Naturals, Booleans]], Typed[t, "left"[n] == y]} |-> InductiveRecursor[DisjointUnionType][
            Typed[q, DisjointUnionType[Naturals, Booleans]] |-> TypeUniverse[0], Typed[k, Naturals] |-> True, Typed[c, Booleans] |-> False, y
        ],
        "trueIntroduction",
        h
    ]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The sides are types: propositions such as [True]() and [False]() are not in `Type u`, and [Or]() is their disjunction:

```wl
TypeTheoryType[DisjointUnionType[True, False]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

On its own, `"left"[2]` does not say the type of the right side:

```wl
TypeTheoryType["left"[2]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

---

`"Decide"` does not decide an equation of disjoint unions, which the prelude has no decision for:

```wl
TypeTheoryProof[Not[Typed["left"[1], DisjointUnionType[Naturals, Booleans]] == "right"["true"]], {"Decide"}]
```

<!-- => Failure["NotDecidable", ...] -->
