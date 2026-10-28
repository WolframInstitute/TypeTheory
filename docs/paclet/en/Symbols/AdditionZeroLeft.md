---
Template: Symbol
Name: AdditionZeroLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionZeroLeft
Keywords: [addition, zero, left, prelude, natural numbers]
SeeAlso: [AdditionZeroRight, AdditionCommutativity, AdditionSuccessorLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionZeroLeft]()[*n*]</code> proves <code>0 + *n* == *n*</code>.

## Details & Options

- [AdditionZeroLeft]() is a theorem of the prelude, proved by induction on *n* with the recursor of [NonNegativeIntegers](): `0 + n` does not compute to *n* while *n* is a variable.

## Basic Examples

The statement of [AdditionZeroLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroLeft]]
```

<!-- => ∀_n∶ℕ 0 + n == n -->

---

An instance, at a successor:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, AdditionZeroLeft[n + 1]]]]
```

<!-- => ∀_n∶ℕ 0 + (n + 1) == n + 1 -->

## Scope

The tactic `"Rewrite"` removes `0 +` from a goal, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n + n == n + n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Rewrite", AdditionZeroLeft[n]]
}]
```

<!-- => Proof complete -->

---

The tactic `"Simplify"` rewrites with it wherever it applies:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, 0 + a + (0 + b) == a + b], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Simplify", {AdditionZeroLeft}]
}]
```

<!-- => Proof complete -->

## Properties and Relations

[MultiplicationOneRight]() is proved with it, since `n * 1` computes to `0 + n`:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n * 1 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Exact", AdditionZeroLeft[n]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The tactic `"Reflexivity"` does not prove `0 + n == n` for a variable *n*, since addition recurses on its second argument:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
