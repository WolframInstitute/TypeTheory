---
Template: Symbol
Name: Choice
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Choice
Keywords: [choice, axiom, axiom of choice, element, nonempty, prelude, classical logic]
SeeAlso: [Nonempty, ChosenWitness, PropositionalExtensionality, FunctionExtensionality, ExcludedMiddle]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Choice]()[*h*]</code> is an element of the type *a*, chosen given a proof *h* of <code>[Nonempty]()[*a*]</code>.

## Details & Options

- [Choice]() is one of the three axioms of the prelude.
- *a* is an implicit argument, found from the type of *h*.
- [ChosenWitness]() uses it to choose a witness of an existential statement.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, does not have it.

## Basic Examples

The statement of [Choice]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Choice]]
```

<!-- => ∀_{α ∶ Sort u} Nonempty[α] → α -->

---

A natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[Choice[NonemptyIntroduction[3]]]]
```

<!-- => ℕ -->

## Properties and Relations

All proofs of a proposition are equal, so [Choice]() chooses the same element whatever proof it is given:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Choice[NonemptyIntroduction[3]]], TypeTheoryTerm[Choice[NonemptyIntroduction[5]]]]
```

<!-- => True -->

## Possible Issues

An axiom does not compute, so which element [Choice]() chooses is not known, even from a proof made of a particular one:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Choice[NonemptyIntroduction[3]]]]
```

<!-- => Choice[NonemptyIntroduction[3]] -->
