---
Template: Symbol
Name: LessEqualDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualDecidable
Keywords: [decidable, less or equal, natural numbers, decision, prelude]
SeeAlso: [NaturalNumberEqualityDecidable, Decidable, Decide, LessEqualStep]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualDecidable]()[*m*, *n*]</code> decides <code>*m* <= *n*</code> for natural numbers *m* and *n*.

## Details & Options

- [LessEqualDecidable]() is a definition of the prelude, as Lean's `Nat.decLe`: it is what the Boolean comparison `"lessEqual"` gives, with the proof of `m <= n` or of its negation that the theorems `"lessEqualTrue"` and `"lessEqualFalse"` give for it.
- `"lessEqual"` is defined by recursion on both numbers, as Lean's `Nat.ble`, and registered with the kernel, which computes it on literals with integers, so deciding literals of any size is one step.

## Basic Examples

The type of [LessEqualDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualDecidable]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ Decidable[m ≤ n] -->

---

1 <= 4 computes to its proof:

```wl
WeakHeadNormalForm[TypeTheoryTerm[LessEqualDecidable[1, 4]]]
```

<!-- => DecidableTrue[lessEqualTrue[1, 4, EqualityReflexivity[lessEqual[1, 4]]]] -->

---

3 <= 2 is decided false:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[LessEqualDecidable[3, 2]]]]
```

<!-- => false -->
