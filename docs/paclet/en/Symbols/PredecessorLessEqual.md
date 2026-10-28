---
Template: Symbol
Name: PredecessorLessEqual
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PredecessorLessEqual
Keywords: [predecessor, less, equal, prelude, natural numbers]
SeeAlso: [NaturalNumberPredecessor, LessEqualPredecessor, LessEqualStep]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PredecessorLessEqual]()[*n*]</code> proves <code>[NaturalNumberPredecessor]()[*n*] <= *n*</code>.

## Details & Options

- [PredecessorLessEqual]() is a theorem of the prelude, proved by cases on *n* with the recursor of [NonNegativeIntegers]().

## Basic Examples

The statement of [PredecessorLessEqual]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PredecessorLessEqual]]
```

<!-- => ∀_n∶ℕ n - 1 ≤ n -->

---

So `5 <= 6`:

```wl
TypeTheoryCheck[TypeTheoryTerm[PredecessorLessEqual[6]], TypeTheoryTerm[5 <= 6]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The predecessor of 0 is 0, so at 0 it proves `0 <= 0`:

```wl
TypeTheoryCheck[TypeTheoryTerm[PredecessorLessEqual[0]], TypeTheoryTerm[0 <= 0]]
```

<!-- => Success["TypeChecked", ...] -->

---

At a successor `x + 1`, it proves `x <= x + 1`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals]}, PredecessorLessEqual[x + 1]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals]}, x <= x + 1]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

`n - 1` is the predecessor of *n* by computation, so it proves `n - 1 <= n`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[n, Naturals]}, PredecessorLessEqual[n]]],
    TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n - 1 <= n]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

The tactic `"Decide"` does not prove it for a variable, whose predecessor does not compute:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n - 1 <= n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Decide"]
}]
```

<!-- => Failure["NotDecided", ...] -->
