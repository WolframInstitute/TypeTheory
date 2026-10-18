---
Template: Symbol
Name: AndIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AndIntroduction
Keywords: [And, conjunction, proof, constructor, prelude, logic]
SeeAlso: [AndEliminationLeft, AndEliminationRight, OrIntroductionLeft, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[AndIntroduction]()[*p*, *q*]</code> proves <code>[And]()[*a*, *b*]</code> from a proof *p* of *a* and a proof *q* of *b*.

## Details & Options

- [And]() is an inductive proposition of the prelude with two parameters, *a* and *b*, and [AndIntroduction]() is its one constructor.
- *a* and *b* are implicit arguments, found from the types of *p* and *q*.
- [And]() is a structure: a proof `h` of <code>[And]()[*a*, *b*]</code> has the fields `h[[1]]`, a proof of *a*, and `h[[2]]`, a proof of *b*. [AndEliminationLeft]() and [AndEliminationRight]() give them as theorems.

## Basic Examples

The type of [AndIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AndIntroduction, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} a ⇒ b ⇒ (a && b) -->

---

Prove two statements at once:

```wl
TypeTheoryCheck[TypeTheoryTerm[AndIntroduction[TrueIntroduction, EqualityReflexivity[2]], TypeTheoryEnvironment["Prelude"]]]
```

<!-- => True && 2 == 2 -->

## Scope

The tactic `"Apply"` leaves a goal for each part:

```wl
TypeTheoryProof[And[True, 1 + 1 == 2], TypeTheoryEnvironment["Prelude"], {TypeTheoryTactic["Apply", AndIntroduction]}]
```

<!-- => Proof, 2 goals: ⊢ True; ⊢ 1 + 1 == 2 -->

## Properties and Relations

A proof of a conjunction is a structure whose fields are proofs:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, And[True, 1 == 1]]}, h[[2]]], TypeTheoryEnvironment["Prelude"]]]
```

<!-- => (True && 1 == 1) ⇒ 1 == 1 -->
