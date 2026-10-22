---
Template: Symbol
Name: OrDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OrDecidable
Keywords: [decidable, disjunction, decision, prelude]
SeeAlso: [Decidable, AndDecidable, NotDecidable, Decide]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[OrDecidable]()[*d*, *e*]</code> decides <code>[Or]()[*p*, *q*]</code> from a decision *d* of *p* and a decision *e* of *q*.

## Details & Options

- [OrDecidable]() is a definition of the prelude, by cases on *d* and then *e*, as Lean's `instDecidableOr`.
- *p* and *q* are implicit arguments, found from the types of *d* and *e*.

## Basic Examples

The type of [OrDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OrDecidable]]
```

<!-- => ∀_{p ∶ Prop} ∀_{q ∶ Prop} Decidable[p] → Decidable[q] → Decidable[p ∨ q] -->

---

One true side decides a disjunction true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[OrDecidable[LessEqualDecidable[3, 2], NaturalNumberEqualityDecidable[2, 2]]]]]
```

<!-- => true -->
