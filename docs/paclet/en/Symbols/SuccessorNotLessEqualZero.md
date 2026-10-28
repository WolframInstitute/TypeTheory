---
Template: Symbol
Name: SuccessorNotLessEqualZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SuccessorNotLessEqualZero
Keywords: [successor, not, less, equal, zero, prelude, natural numbers]
SeeAlso: [SuccessorNotZero, LessIrreflexivity, LessEqualZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SuccessorNotLessEqualZero]()[*n*]</code> proves <code>[Not]()[*n* + 1 <= 0]</code>.

## Details & Options

- [SuccessorNotLessEqualZero]() is a theorem of the prelude, proved with the recursor of [LessEqual]() and [SuccessorNotZero]().

## Basic Examples

The statement of [SuccessorNotLessEqualZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorNotLessEqualZero]]
```

<!-- => ∀_n∶ℕ ¬n + 1 ≤ 0 -->

---

So `3 <= 0` is false:

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorNotLessEqualZero[2]], TypeTheoryTerm[Not[3 <= 0]]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

In a proof, it refutes a hypothesis `n + 1 <= 0`, and [FalseElimination]() proves the goal from the contradiction:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Implies[n + 1 <= 0, n == 7]], {
    TypeTheoryTactic["Introduce", n, h],
    TypeTheoryTactic["Exact", FalseElimination[SuccessorNotLessEqualZero[n][h]]]
}]
```

<!-- => Proof complete -->

---

`n < 0` unfolds to `n + 1 <= 0`, so it proves that no number is less than 0:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[n, Naturals]}, SuccessorNotLessEqualZero[n]]],
    TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, Not[n < 0]]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

At 0 it proves that 0 is not less than 0, the first case of [LessIrreflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorNotLessEqualZero[0]], TypeTheoryTerm[Not[0 < 0]]]
```

<!-- => Success["TypeChecked", ...] -->

---

The tactic `"Decide"` proves its instances with literals:

```wl
TypeTheoryProof[Not[3 <= 0], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
