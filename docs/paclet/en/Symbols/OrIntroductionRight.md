---
Template: Symbol
Name: OrIntroductionRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OrIntroductionRight
Keywords: [Or, disjunction, proof, constructor, prelude, logic]
SeeAlso: [OrIntroductionLeft, AndIntroduction, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[OrIntroductionRight]()[*q*]</code> proves <code>[Or]()[*a*, *b*]</code> from a proof *q* of *b*.

## Details & Options

- [Or]() is an inductive proposition of the prelude with two parameters, *a* and *b*, and two constructors, [OrIntroductionLeft]() and [OrIntroductionRight]().
- *a* and *b* are implicit arguments. *b* is found from the type of *q*, but *a* only from the type the proof is expected to have.

## Basic Examples

The type of [OrIntroductionRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} b ⇒ (a || b) -->

---

A proof of `False || 1 + 2 == 3`, whose right side holds by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight[EqualityReflexivity[3]], TypeTheoryEnvironment["Prelude"]], TypeTheoryTerm[Or[False, 1 + 2 == 3]]]
```

<!-- => True -->
