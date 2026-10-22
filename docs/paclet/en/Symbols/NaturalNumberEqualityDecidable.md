---
Template: Symbol
Name: NaturalNumberEqualityDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NaturalNumberEqualityDecidable
Keywords: [decidable, equality, natural numbers, decision, prelude]
SeeAlso: [LessEqualDecidable, Decidable, Decide, Naturals]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[NaturalNumberEqualityDecidable]()[*m*, *n*]</code> decides <code>*m* == *n*</code> for natural numbers *m* and *n*.

## Details & Options

- [NaturalNumberEqualityDecidable]() is a definition of the prelude, as Lean's `Nat.decEq`: it is what the Boolean comparison `"equal"` gives, with the proof of `m == n` or of its negation that the theorems `"equalTrue"` and `"equalFalse"` give for it.
- It is an instance: [Decide]() and the tactic `"Decide"` find it for an equation of natural numbers.
- `"equal"` is defined by recursion on both numbers, as Lean's `Nat.beq`, and registered with the kernel, which computes it on literals with integers, so deciding literals of any size is one step: [Decide]() of it gives the Boolean of the equation.

## Basic Examples

The type of [NaturalNumberEqualityDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NaturalNumberEqualityDecidable]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ Decidable[m == n] -->

---

2 == 2 is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Construct[Decide, 2 == 2, NaturalNumberEqualityDecidable[2, 2]]]]
```

<!-- => true -->

## Properties and Relations

[Decide]() finds it as the decision of an equation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[12^3 + 1 == 9^3 + 10^3]]]
```

<!-- => true -->

---

[DecideSoundness]() turns the decision into a proof:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DecideSoundness[EqualityReflexivity["true"]], 3 == 3]]]
```

<!-- => 3 == 3 -->
