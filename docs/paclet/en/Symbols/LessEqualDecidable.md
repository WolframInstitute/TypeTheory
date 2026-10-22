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

- [LessEqualDecidable]() is a definition of the prelude, by recursion on *m* and then on *n*, as Lean's `Nat.decLe`.
- It computes on literals, to the proof or refutation it finds.

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

<!-- => DecidableTrue[LessEqualSuccessor[LessEqualZero[3]]] -->

---

3 <= 2 is decided false:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[LessEqualDecidable[3, 2]]]]
```

<!-- => false -->
