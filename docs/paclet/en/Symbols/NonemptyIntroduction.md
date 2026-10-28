---
Template: Symbol
Name: NonemptyIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NonemptyIntroduction
Keywords: [nonempty, introduction, element, prelude, classical logic]
SeeAlso: [Nonempty, Choice, ExistsIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[NonemptyIntroduction]()[*x*]</code> proves <code>[Nonempty]()[*a*]</code> from an element *x* of *a*.

## Details & Options

- [NonemptyIntroduction]() is the constructor of [Nonempty]().
- *a* is an implicit argument, found from the type of *x*.

## Basic Examples

The statement of [NonemptyIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction]]
```

<!-- => ∀_{α ∶ Sort u} α → Nonempty[α] -->

---

A natural number shows that there are natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction[3]]]
```

<!-- => Nonempty[ℕ] -->

## Scope

[Typed]() gives the type of an element when the element alone does not say it: the empty list shows that there are lists:

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction[Typed[EmptyList, Lists[Naturals]]]]]
```

<!-- => Nonempty[Lists[ℕ]] -->

---

`"Apply"` leaves the element to give, a goal that is a type:

```wl
proof = TypeTheoryProof[Nonempty[Naturals], {TypeTheoryTactic["Apply", NonemptyIntroduction]}]
```

<!-- => Proof, 1 goal: ⊢ ℕ -->

Any natural number solves it:

```wl
TypeTheoryTactic["Exact", 0][proof]
```

<!-- => Proof complete -->

## Properties and Relations

A proof forgets its element: the proofs from 3 and from 5 are equal, as any two proofs of a proposition are:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[NonemptyIntroduction[3]], TypeTheoryTerm[NonemptyIntroduction[5]]]
```

<!-- => True -->

## Possible Issues

[Choice]() does not give the element back: it does not compute, even on a proof made from 3:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Choice[NonemptyIntroduction[3]]]]
```

<!-- => Choice[NonemptyIntroduction[3]] -->
