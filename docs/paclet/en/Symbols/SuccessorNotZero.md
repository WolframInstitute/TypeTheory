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
