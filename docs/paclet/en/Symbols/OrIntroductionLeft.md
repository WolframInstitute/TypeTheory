---
Template: Symbol
Name: OrIntroductionLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OrIntroductionLeft
Keywords: [Or, disjunction, proof, constructor, prelude, logic]
SeeAlso: [OrIntroductionRight, AndIntroduction, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[OrIntroductionLeft]()[*p*]</code> proves <code>[Or]()[*a*, *b*]</code> from a proof *p* of *a*.

## Details & Options

- [Or]() is an inductive proposition of the prelude with two parameters, *a* and *b*, and two constructors, [OrIntroductionLeft]() and [OrIntroductionRight]().
- *a* and *b* are implicit arguments. *a* is found from the type of *p*, but *b* only from the type the proof is expected to have.
- A proof of <code>[Or]()[*a*, *b*]</code> eliminates only into propositions: it does not say which side holds.

## Basic Examples

The type of [OrIntroductionLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionLeft]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} a ⇒ (a ∨ b) -->

---

A proof of `True || False`:

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionLeft[TrueIntroduction]], TypeTheoryTerm[Or[True, False]]]
```

<!-- => True -->

## Scope

[Typed]() gives the expected type inside the term:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[OrIntroductionLeft[TrueIntroduction], Or[True, False]]]]
```

<!-- => True ∨ False -->

## Possible Issues

Without an expected type, the right side of the disjunction is unknown:

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionLeft[TrueIntroduction]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->
