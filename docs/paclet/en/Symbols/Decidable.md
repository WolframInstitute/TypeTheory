---
Template: Symbol
Name: Decidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Decidable
Keywords: [decidable, decision, proposition, Boolean, prelude, inductive type]
SeeAlso: [DecidableTrue, DecidableFalse, Decide, DecideSoundness, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Decidable]()[*p*]</code> is the type of decisions of the proposition *p*: a proof of *p*, or a proof of its negation.

## Details & Options

- [Decidable]() is an inductive type of the prelude, with the constructors [DecidableFalse]() and [DecidableTrue](), in that order, as Lean's `Decidable`.
- A decision is data, in `Type`, not a proposition, so it computes: [Decide]() turns it into a Boolean, and [DecideSoundness]() turns a decision that computes to `"true"` into a proof of *p*.
- The prelude decides equations and inequalities of natural numbers with [NaturalNumberEqualityDecidable]() and [LessEqualDecidable](), and combines decisions with [NotDecidable](), [AndDecidable]() and [OrDecidable]().
- The tactic `"Decide"` of [TypeTheoryTactic]() builds a decision of the goal from these and proves it with [DecideSoundness]().

## Basic Examples

The type of [Decidable]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Decidable]]
```

<!-- => Prop → Type -->

---

A decision of an equation is a type:

```wl
TypeTheoryCheck[TypeTheoryTerm[Decidable[2 == 3]]]
```

<!-- => Type -->

## Scope

A decision computes to the constructor that holds, with its proof:

```wl
WeakHeadNormalForm[TypeTheoryTerm[LessEqualDecidable[1, 4]]]
```

<!-- => DecidableTrue[LessEqualSuccessor[LessEqualZero[3]]] -->

## Properties and Relations

The tactic `"Decide"` proves a closed statement by computing its decision:

```wl
TypeTheoryProof[And[1 <= 2, Not[2 == 3]], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
