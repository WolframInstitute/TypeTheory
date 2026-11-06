---
Template: Symbol
Name: NaturalNumberPredecessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NaturalNumberPredecessor
Keywords: [natural, number, predecessor, prelude, natural numbers, recursion, subtraction, successor, injectivity]
SeeAlso: [Naturals, InductiveRecursor, Subtract, TypeTheoryNaturalNumbers]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[NaturalNumberPredecessor]()[*n*]</code> is the natural number before *n*, and `0` before `0`.

## Details & Options

- [NaturalNumberPredecessor]() is a definition of the prelude, by the recursor of [NonNegativeIntegers](): the predecessor of `0` is `0`, and of <code>*k* + 1</code> is *k*, as Lean's `Nat.pred`.
- It computes on a literal of any size in one step, and at a successor `n + 1` of a variable to `n`; at a variable `n` it does not reduce.
- [Subtract]() is defined from it: <code>*m* - (*n* + 1)</code> is the predecessor of <code>*m* - *n*</code>, so subtraction stops at 0 as the predecessor does.
- The predecessor undoes the successor, so `"successorInjectivity"` is proved from it, by congruence.
- <code>[NaturalNumberPredecessor]()[*n*]</code> shows as `n - 1`, which it is by computation.

## Basic Examples

The type of [NaturalNumberPredecessor]():

```wl
TypeTheoryType[NaturalNumberPredecessor]
```

<!-- => ℕ → ℕ -->

---

The number before 10:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[10]]]
```

<!-- => 9 -->

---

The predecessor shows as `n - 1`:

```wl
TypeTheoryTerm[Typed[n, Naturals] |-> NaturalNumberPredecessor[n]]
```

<!-- => (n ∶ ℕ) ↦ n - 1 -->

## Scope

At a successor of a variable it computes, so the number before `n + 1` is *n* by `"Reflexivity"`:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, NaturalNumberPredecessor[n + 1] == n], {
    "Introduce"[n],
    "Reflexivity"
}]
```

<!-- => Proof complete -->

---

At a literal it computes, however large the literal:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[10^20]]]
```

<!-- => 99999999999999999999 -->

---

The predecessor of a predecessor:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[NaturalNumberPredecessor[5]]]]
```

<!-- => 3 -->

## Applications

The successor is injective: the predecessor, applied to both sides of `m + 1 == n + 1` by congruence, gives `m == n`:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals], Typed[h, m + 1 == n + 1]}, m == n], {
    "Introduce"[m, n, h],
    "Exact"["equalityCongruence"[NaturalNumberPredecessor, h]]
}]
```

<!-- => Proof complete -->

---

For a number that is at least 1, the successor of its predecessor is the number: by cases, where 0 contradicts the hypothesis and a successor computes:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Implies[1 <= n, NaturalNumberPredecessor[n] + 1 == n]], {
    "Introduce"[n],
    "Cases"[n],
    "Introduce"[h],
    "Exact"["falseElimination"["successorNotLessEqualZero"[0, h]]],
    "Introduce"[k, h],
    "Reflexivity"
}]
```

<!-- => Proof complete -->

## Properties and Relations

Its definition, by the recursor of the natural numbers, whose step gives the number *k* before the successor `k + 1`:

```wl
TypeTheoryEnvironment["Prelude"][NaturalNumberPredecessor]
```

<!-- => definition NaturalNumberPredecessor : ℕ → ℕ := (n ∶ ℕ) ↦ ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ k, n] -->

---

Subtracting 1 is the predecessor by computation, which is why the predecessor of *n* shows as `n - 1`:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, Naturals] |-> n - 1], TypeTheoryTerm[NaturalNumberPredecessor]]
```

<!-- => True -->

---

Subtracting a successor takes the predecessor of the difference, by computation:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m - (n + 1) == NaturalNumberPredecessor[m - n]], {"Introduce"[m, n], "Reflexivity"}]
```

<!-- => Proof complete -->

---

The predecessor is never larger, a theorem of the prelude:

```wl
TypeTheoryType["predecessorLessEqual"]
```

<!-- => ∀_n∶ℕ n - 1 <= n -->

## Possible Issues

The predecessor of 0 is 0, so adding 1 back gives 1, not 0:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[0] + 1]]
```

<!-- => 1 -->

---

At a variable the predecessor does not compute, and `(n - 1) + 1 == n` fails at 0, so it is no equation by computation; it needs `1 <= n` and cases, as above:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, NaturalNumberPredecessor[n] + 1 == n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

---

It takes natural numbers only; in <code>[TypeTheoryEnvironment]()["Integers"]</code>, an integer is not one:

```wl
TypeTheoryType[NaturalNumberPredecessor[Typed[3, Integers]], "Integers"]
```

<!-- => Failure["TypeMismatch", ...] -->
