---
Template: Symbol
Name: NotDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NotDecidable
Keywords: [decidable, negation, decision, prelude]
SeeAlso: [Decidable, AndDecidable, OrDecidable, Decide]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[NotDecidable]()[*d*]</code> decides <code>[Not]()[*p*]</code> from a decision *d* of *p*.

## Details & Options

- [NotDecidable]() is a definition of the prelude, by cases on *d*, as Lean's `instDecidableNot`.
- *p* is an implicit argument, found from the type of *d*.

## Basic Examples

The type of [NotDecidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NotDecidable]]
```

<!-- => ∀_{p ∶ Prop} Decidable[p] → Decidable[¬p] -->

---

A decision of `¬2 == 3`:

```wl
TypeTheoryCheck[TypeTheoryTerm[NotDecidable[NaturalNumberEqualityDecidable[2, 3]]]]
```

<!-- => Decidable[¬2 == 3] -->

## Properties and Relations

It is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[NotDecidable[NaturalNumberEqualityDecidable[2, 3]]]]]
```

<!-- => true -->
