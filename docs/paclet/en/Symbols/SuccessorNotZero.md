---
Template: Symbol
Name: SuccessorNotZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SuccessorNotZero
Keywords: [successor, not, zero, prelude, natural numbers]
SeeAlso: [SuccessorInjectivity, Unequal, SuccessorNotLessEqualZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SuccessorNotZero]()[*n*]</code> proves <code>*n* + 1 != 0</code>.

## Details & Options

- [SuccessorNotZero]() is a theorem of the prelude: a predicate that is [True]() at successors and [False]() at `0`, defined with the recursor of [NonNegativeIntegers](), carries a proof of [True]() along an equation `n + 1 == 0` to a proof of [False]().
- <code>*x* != *y*</code> is [Unequal](), which unfolds to <code>[Not]()[*x* == *y*]</code>.

## Basic Examples

The statement of [SuccessorNotZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorNotZero]]
```

<!-- => ∀_n∶ℕ n + 1 ≠ 0 -->

---

So `5 != 0`:

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorNotZero[4]], TypeTheoryTerm[5 != 0]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The tactic `"Introduce"` unfolds `n + 1 != 0` into a hypothesis `n + 1 == 0` and the goal [False]():

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 1 != 0], {TypeTheoryTactic["Introduce", n, h]}]
```

<!-- => Proof, 1 goal: n ∶ ℕ, h ∶ n + 1 == 0 ⊢ False -->

Applied to *n* and the hypothesis, it proves [False]():

```wl
TypeTheoryTactic["Exact", SuccessorNotZero[n][h]][proof]
```

<!-- => Proof complete -->

---

`x + 2` computes to the successor of `x + 1`, so the theorem at `x + 1` proves `x + 2 != 0`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals]}, SuccessorNotZero[x + 1]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals]}, x + 2 != 0]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

With [EqualitySymmetry](), it proves the inequation the other way around, `0 != n + 1`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[n, Naturals], Typed[h, 0 == n + 1]}, SuccessorNotZero[n][EqualitySymmetry[h]]]],
    TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, 0 != n + 1]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

`1 + n` is not a successor by computation, since addition recurses on its second argument, so `1 + n != 0` is not an instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, SuccessorNotZero[n]]], TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, 1 + n != 0]]]
```

<!-- => Failure["TypeMismatch", ...] -->
