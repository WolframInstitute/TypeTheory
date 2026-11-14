---
Template: Symbol
Name: CartesianProductType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CartesianProductType
Keywords: [pair, product, Cartesian product, tuple, structure, projection, field, eta, prelude, inductive type, Prod]
SeeAlso: [DisjointUnionType, Option, List, DependentSum, Subtype, InductiveRecursor]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[CartesianProductType]()[*α*, *β*]</code> is the type of pairs of an element of *α* and an element of *β*.

## Details & Options

- [CartesianProductType]() is an inductive type of the prelude, with the one constructor `"pair"`. `"pair"` takes the types of its fields implicitly, from the fields.
- It is a structure: a pair `p` has the parts `p["first"]` and `p["second"]`, also written by their indices, `p[[1]]` and `p[[2]]`. They compute on a pair: `"pair"[a, b]["first"]` is `a`. A pair is its parts: `p` and `"pair"[p["first"], p["second"]]` are equal by computation, the eta rule of a structure.
- The parts of any structure are named by the binders of its constructor, as those of `"pair"` are `first` and `second`; a name is how a part is written and shown, and the term is the part by its index.
- Its recursor, <code>[InductiveRecursor]()[[CartesianProductType]()]</code>, takes a function of the two fields.
- For *α* in `Type u` and *β* in `Type v`, <code>[CartesianProductType]()[*α*, *β*]</code> is in `Type (max u v)`. The fields are data: for propositions, [And]() is the conjunction, a structure too.
- <code>[CartesianProductType]()[*α*, *β*]</code> displays as *α* × *β*, and a product nested to the right, <code>[CartesianProductType]()[*α*, [CartesianProductType]()[*β*, *γ*]]</code>, as *α* × *β* × *γ*. A pair displays as `(a, b)`, and a pair nested to the right as `(a, b, c)`.

## Basic Examples

The type of [CartesianProductType]():

```wl
TypeTheoryType[CartesianProductType]
```

<!-- => Type u → Type v → Type (max u v) -->

---

A pair of natural numbers:

```wl
TypeTheoryType["pair"[2, 3]]
```

<!-- => ℕ × ℕ -->

---

A pair nested to the right is a triple, here of a number, a Boolean and a number:

```wl
TypeTheoryTerm["pair"[1, "pair"["true", 3]]]
```

<!-- => (1, true, 3) -->

Its type:

```wl
TypeTheoryType["pair"[1, "pair"["true", 3]]]
```

<!-- => ℕ × 𝔹 × ℕ -->

## Scope

The fields of a pair compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm["pair"[2, 3]["second"]]]
```

<!-- => 3 -->

---

The middle of a triple is the first field of its second:

```wl
WeakHeadNormalForm[TypeTheoryTerm["pair"[1, "pair"["true", 3]]["second"]["first"]]]
```

<!-- => true -->

---

A function takes the second field of any pair:

```wl
TypeTheoryType[Typed[p, CartesianProductType[Naturals, Booleans]] |-> p["second"]]
```

<!-- => ℕ × 𝔹 → 𝔹 -->

---

Swapping the fields, applied to a pair:

```wl
NormalForm[TypeTheoryTerm[(Typed[p, CartesianProductType[Naturals, Booleans]] |-> "pair"[p["second"], p["first"]])["pair"[2, "true"]]]]
```

<!-- => (true, 2) -->

---

Each number of a list with its square:

```wl
NormalForm[TypeTheoryTerm[Map[n |-> "pair"[n, n * n], {1, 2, 3}]]]
```

<!-- => {(1, 1), (2, 4), (3, 9)} -->

---

The recursor applies a function of two arguments to the fields:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[CartesianProductType][Naturals &, {x, y} |-> x * y, "pair"[6, 7]]]]
```

<!-- => 42 -->

---

A pair of a number and a type is in the universe of its larger field:

```wl
TypeTheoryType[CartesianProductType[Naturals, TypeUniverse[1]]]
```

<!-- => Type 1 -->

## Applications

The Fibonacci numbers, by a recursion that carries two consecutive numbers in a pair:

```wl
fibonacci = TypeTheoryEnvironment[{TypeTheoryDefinition[Fibonacci,
    n |-> InductiveRecursor[Naturals][CartesianProductType[Naturals, Naturals] &, "pair"[0, 1], {k, r} |-> "pair"[r["second"], r["first"] + r["second"]], n]["first"]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The first eight:

```wl
NormalForm[TypeTheoryTerm[Map[Fibonacci, {1, 2, 3, 4, 5, 6, 7, 8}], fibonacci]]
```

<!-- => {1, 1, 2, 3, 5, 8, 13, 21} -->

The tenth is 55, by computation:

```wl
TypeTheoryProof[Fibonacci[10] == 55, fibonacci, {"Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

A pair is its fields, by computation:

```wl
TypeTheoryProof[ForAll[{Typed[p, CartesianProductType[Naturals, Naturals]]}, p == "pair"[p["first"], p["second"]]], {"Introduce"[p], "Reflexivity"}]
```

<!-- => Proof complete -->

---

Equal pairs have equal first fields, by congruence with the first field:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals], Typed[d, Naturals], Typed[h, "pair"[a, b] == "pair"[c, d]]}, a == c], {
    "Introduce"[a, b, c, d, h],
    "Exact"["equalityCongruence"[Typed[q, CartesianProductType[Naturals, Naturals]] |-> q["first"], h]]
}]
```

<!-- => Proof complete -->

---

A theorem about numbers applies to the fields of a pair:

```wl
TypeTheoryProof[ForAll[{Typed[p, CartesianProductType[Naturals, Naturals]]}, p["first"] + p["second"] == p["second"] + p["first"]], {"Introduce"[p], "Exact"["additionCommutativity"[p["first"], p["second"]]]}]
```

<!-- => Proof complete -->

---

For propositions, a proof of a conjunction has two parts as a pair does, `"left"` and `"right"`:

```wl
TypeTheoryType[Typed[h, 2 == 2 && 3 == 3] |-> h["right"]]
```

<!-- => (2 == 2 ∧ 3 == 3) ⇒ 3 == 3 -->

---

A product nested to the left shows its parentheses:

```wl
TypeTheoryTerm[CartesianProductType[CartesianProductType[Naturals, Booleans], Naturals]]
```

<!-- => (ℕ × 𝔹) × ℕ -->

## Possible Issues

The fields are types: propositions such as [True]() and [False]() are not in `Type u`, and [And]() is their conjunction:

```wl
TypeTheoryType[CartesianProductType[True, False]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A pair has two parts:

```wl
TypeTheoryType["pair"[2, 3][[3]]]
```

<!-- => Failure["ProjectionIndex", ...] -->

---

A part of a part is written as two, `p["second"]["first"]` or `p[[2]][[1]]`, not `p[[2, 1]]`:

```wl
TypeTheoryType["pair"[1, "pair"["true", 3]][[2, 1]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

In a pair, [True]() could be the proposition or the Boolean:

```wl
TypeTheoryType["pair"[1, True]]
```

<!-- => Failure["Ambiguous", ...] -->

[Typed]() says which:

```wl
TypeTheoryType[Typed["pair"[1, True], CartesianProductType[Naturals, Booleans]]]
```

<!-- => ℕ × 𝔹 -->
