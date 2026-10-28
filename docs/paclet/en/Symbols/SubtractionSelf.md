---
Template: Symbol
Name: SubtractionSelf
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionSelf
Keywords: [subtraction, self, prelude, natural numbers]
SeeAlso: [SubtractionSuccessor, SubtractionZeroLeft, AdditionSubtractionCancellation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionSelf]()[*n*]</code> proves <code>*n* - *n* == 0</code>.

## Details & Options

- [SubtractionSelf]() is a theorem of the prelude, proved by induction on *n* with [SubtractionSuccessor]().

## Basic Examples

The statement of [SubtractionSelf]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionSelf]]
```

<!-- => ∀_n∶ℕ n - n == 0 -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, SubtractionSelf[n]]]]
```

<!-- => ∀_n∶ℕ n - n == 0 -->

## Scope

The tactic `"Rewrite"` replaces `n - n` by 0, and [AdditionZeroLeft]() finishes the proof:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n - n + n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Rewrite", SubtractionSelf[n]],
    TypeTheoryTactic["Rewrite", AdditionZeroLeft[n]]
}]
```

<!-- => Proof complete -->

---

The tactic `"Apply"` finds *n* from the goal, here a sum:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, (x + y) - (x + y) == 0], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", SubtractionSelf]
}]
```

<!-- => Proof complete -->

## Possible Issues

The tactic `"Ring"` does not prove it, since subtraction is not an operation of a semiring:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n - n == 0], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Failure["NotRingEquation", ...] -->
