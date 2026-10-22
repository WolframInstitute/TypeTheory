---
Template: Symbol
Name: AndDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AndDecidable
Keywords: [decidable, conjunction, decision, prelude]
SeeAlso: [Decidable, OrDecidable, NotDecidable, Decide]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AndDecidable]()[*d*, *e*]</code> decides <code>[And]()[*p*, *q*]</code> from a decision *d* of *p* and a decision *e* of *q*.

## Details & Options

- [AndDecidable]() is a definition of the prelude, by cases on *d* and then *e*, as Lean's `instDecidableAnd`.
- *p* and *q* are implicit arguments, found from the types of *d* and *e*.

## Basic Examples

The type of [AndDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AndDecidable]]
```

<!-- => ∀_{p ∶ Prop} ∀_{q ∶ Prop} Decidable[p] → Decidable[q] → Decidable[p ∧ q] -->

---

A decision of a conjunction:

```wl
TypeTheoryCheck[TypeTheoryTerm[AndDecidable[LessEqualDecidable[1, 2], NaturalNumberEqualityDecidable[2, 2]]]]
```

<!-- => Decidable[1 ≤ 2 ∧ 2 == 2] -->

## Properties and Relations

It is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[AndDecidable[LessEqualDecidable[1, 2], NaturalNumberEqualityDecidable[2, 2]]]]]
```

<!-- => true -->
