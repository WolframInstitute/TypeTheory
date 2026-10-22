---
Template: Symbol
Name: DecidableTrue
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DecidableTrue
Keywords: [decidable, decision, proof, constructor, prelude]
SeeAlso: [Decidable, DecidableFalse, Decide, DecideSoundness]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DecidableTrue]()[*h*]</code> decides the proposition *p* true, from a proof *h* of *p*.

## Details & Options

- [DecidableTrue]() is the second constructor of [Decidable]().
- *p* is an implicit argument, found from the type of *h*.
- [Decide]() gives `"true"` for it.

## Basic Examples

The statement of [DecidableTrue]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DecidableTrue]]
```

<!-- => ∀_{p ∶ Prop} p → Decidable[p] -->

---

[TrueIntroduction]() decides [True]() true:

```wl
TypeTheoryCheck[TypeTheoryTerm[DecidableTrue[TrueIntroduction]]]
```

<!-- => Decidable[True] -->

## Properties and Relations

[Decide]() gives `"true"` for it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Construct[Decide, True, DecidableTrue[TrueIntroduction]]]]
```

<!-- => true -->
