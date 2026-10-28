---
Template: Symbol
Name: SubtractionZeroLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionZeroLeft
Keywords: [subtraction, zero, left, prelude, natural numbers]
SeeAlso: [SubtractionZeroRight, SubtractionSelf, Subtract]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionZeroLeft]()[*n*]</code> proves <code>0 - *n* == 0</code>: subtraction of natural numbers stops at `0`.

## Details & Options

- [SubtractionZeroLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [SubtractionZeroLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionZeroLeft]]
```

<!-- => ∀_n∶ℕ 0 - n == 0 -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, SubtractionZeroLeft[n]]]]
```

<!-- => ∀_n∶ℕ 0 - n == 0 -->

## Scope

The tactic `"Rewrite"` replaces `0 - n` by 0, and [AdditionZeroLeft]() finishes the proof:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 - n + 5 == 5], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Rewrite", SubtractionZeroLeft[n]],
    TypeTheoryTactic["Apply", AdditionZeroLeft]
}]
```

<!-- => Proof complete -->

## Properties and Relations

On literals, subtraction computes, and stops at 0 when the second number is the larger:

```wl
WeakHeadNormalForm[TypeTheoryTerm[3 - 5]]
```

<!-- => 0 -->

## Possible Issues

The tactic `"Reflexivity"` does not prove `0 - n == 0` for a variable *n*, since subtraction recurses on its second argument:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 - n == 0], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
