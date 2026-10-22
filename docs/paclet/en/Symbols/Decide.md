---
Template: Symbol
Name: Decide
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Decide
Keywords: [decide, decision, Boolean, computation, prelude]
SeeAlso: [Decidable, DecideSoundness, NaturalNumberEqualityDecidable, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Decide]()[*d*]</code> gives the Boolean of the decision *d*: `"true"` for a proof, `"false"` for a refutation.

## Details & Options

- [Decide]() is a definition of the prelude, by recursion on *d*, as Lean's `Decidable.decide`.
- The proposition *d* decides is an implicit argument.
- The Booleans are named by strings, `"true"` and `"false"`.

## Basic Examples

The type of [Decide]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Decide]]
```

<!-- => ∀_{p ∶ Prop} Decidable[p] → 𝔹 -->

---

2 == 2 is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[NaturalNumberEqualityDecidable[2, 2]]]]
```

<!-- => true -->

---

3 <= 2 is decided false:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[LessEqualDecidable[3, 2]]]]
```

<!-- => false -->

## Properties and Relations

[DecideSoundness]() turns a decision that computes to `"true"` into a proof:

```wl
TypeTheoryCheck[TypeTheoryTerm[DecideSoundness[NaturalNumberEqualityDecidable[3, 3], EqualityReflexivity["true"]]]]
```

<!-- => 3 == 3 -->
