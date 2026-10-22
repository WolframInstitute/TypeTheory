---
Template: Symbol
Name: NotDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NotDecidable
Keywords: [decidable, instance, negation, decision, prelude]
SeeAlso: [Decidable, AndDecidable, OrDecidable, Decide]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions]
---

## Usage

[NotDecidable]() is the instance deciding <code>[Not]()[*p*]</code> from the instance of <code>[Decidable]()[*p*]</code>.

## Details & Options

- [NotDecidable]() is an instance of the prelude, by cases on the decisions, as Lean's `instDecidableNot`.
- Elaboration uses it: [Decide]() and the tactic `"Decide"` find it, with the decisions it takes, for a proposition of its form.

## Basic Examples

The type of [NotDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NotDecidable]]
```

<!-- => ∀_{p∶Prop} ∀_[d∶Decidable[p]] Decidable[¬p] -->

---

It decides a proposition of its form, with the decisions it takes found in turn:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[NotDecidable, Decidable[Not[2 == 3]]]]]
```

<!-- => Decidable[¬2 == 3] -->

## Properties and Relations

[Decide]() finds it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[Not[2 == 3]]]]
```

<!-- => true -->
