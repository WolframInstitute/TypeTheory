---
Template: Symbol
Name: AndDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AndDecidable
Keywords: [decidable, instance, conjunction, decision, prelude]
SeeAlso: [Decidable, OrDecidable, NotDecidable, Decide]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions]
---

## Usage

[AndDecidable]() is the instance deciding <code>[And]()[*p*, *q*]</code> from the instances of <code>[Decidable]()[*p*]</code> and <code>[Decidable]()[*q*]</code>.

## Details & Options

- [AndDecidable]() is an instance of the prelude, by cases on the decisions, as Lean's `instDecidableAnd`.
- Elaboration uses it: [Decide]() and the tactic `"Decide"` find it, with the decisions it takes, for a proposition of its form.

## Basic Examples

The type of [AndDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AndDecidable]]
```

<!-- => ∀_{p∶Prop} ∀_{q∶Prop} ∀_[d∶Decidable[p]] ∀_[e∶Decidable[q]] Decidable[p∧q] -->

---

It decides a proposition of its form, with the decisions it takes found in turn:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[AndDecidable, Decidable[1 <= 2 && 2 == 2]]]]
```

<!-- => Decidable[1≤2∧2 == 2] -->

## Properties and Relations

[Decide]() finds it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[1 <= 2 && 2 == 2]]]
```

<!-- => true -->
