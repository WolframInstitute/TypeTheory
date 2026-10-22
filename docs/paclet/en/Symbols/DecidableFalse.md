---
Template: Symbol
Name: DecidableFalse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DecidableFalse
Keywords: [decidable, decision, negation, constructor, prelude]
SeeAlso: [Decidable, DecidableTrue, Decide, NotDecidable]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DecidableFalse]()[*h*]</code> decides the proposition *p* false, from a proof *h* of <code>[Not]()[*p*]</code>.

## Details & Options

- [DecidableFalse]() is the first constructor of [Decidable]().
- *p* is an implicit argument, found from the type of *h*.
- [Decide]() gives `"false"` for it.

## Basic Examples

The statement of [DecidableFalse]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DecidableFalse]]
```

<!-- => ∀_{p ∶ Prop} (¬p) → Decidable[p] -->

---

False is decided false by the identity on its proofs:

```wl
TypeTheoryCheck[TypeTheoryTerm[DecidableFalse[Function[{Typed[h, False]}, h]]]]
```

<!-- => Decidable[False] -->

## Properties and Relations

[Decide]() gives `"false"` for it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Construct[Decide, False, DecidableFalse[Function[{Typed[h, False]}, h]]]]]
```

<!-- => false -->
