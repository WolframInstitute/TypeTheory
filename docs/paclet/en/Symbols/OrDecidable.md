---
Template: Symbol
Name: OrDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OrDecidable
Keywords: [decidable, instance, disjunction, decision, prelude]
SeeAlso: [Decidable, AndDecidable, NotDecidable, Decide]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions]
---

## Usage

[OrDecidable]() is the instance deciding <code>[Or]()[*p*, *q*]</code> from the instances of <code>[Decidable]()[*p*]</code> and <code>[Decidable]()[*q*]</code>.

## Details & Options

- [OrDecidable]() is an instance of the prelude, by cases on the decisions, as Lean's `instDecidableOr`.
- Elaboration uses it: [Decide]() and the tactic `"Decide"` find it, with the decisions it takes, for a proposition of its form.

## Basic Examples

The type of [OrDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OrDecidable]]
```

<!-- => ∀_{p∶Prop} ∀_{q∶Prop} ∀_[d∶Decidable[p]] ∀_[e∶Decidable[q]] Decidable[p∨q] -->

---

It decides a proposition of its form, with the decisions it takes found in turn:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[OrDecidable, Decidable[3 <= 2 || 2 == 2]]]]
```

<!-- => Decidable[3≤2∨2 == 2] -->

## Properties and Relations

[Decide]() finds it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[3 <= 2 || 2 == 2]]]
```

<!-- => true -->
