---
Template: Symbol
Name: Decidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Decidable
Keywords: [decidable, decision, proposition, Boolean, prelude, inductive type, class, instance, type class resolution, excluded middle, constructive]
SeeAlso: [Decide, TypeTheoryTactic, TypeTheoryDefinition, InductiveRecursor]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions]
---

## Usage

<code>[Decidable]()[*p*]</code> is the type of decisions of the proposition *p*: a proof of *p*, or a proof of its negation.

## Details & Options

- [Decidable]() is an inductive type of the prelude, with the constructors `"decidableFalse"`, which takes a proof of <code>[Not]()[*p*]</code>, and `"decidableTrue"`, which takes a proof of *p*, in that order, as Lean's `Decidable`.
- A decision is data, in `Type`, not a proposition, so it computes, and its recursor eliminates into any universe: [Decide]() turns it into a Boolean, and `"decideSoundness"` turns a decision that computes to `"true"` into a proof of *p*.
- [Decidable]() is a class: its instances are definitions declared with `"Instance" -> True`, and elaboration finds the decision of a proposition among them, as Lean's type class resolution does.
- The prelude's instances decide equations and inequalities of natural numbers with `"naturalNumberEqualityDecidable"` and `"lessEqualDecidable"`, which compare literals in one step of the kernel, combine decisions with `"notDecidable"`, `"andDecidable"` and `"orDecidable"`, and decide [True](), [False]() and equations of Booleans with `"trueDecidable"`, `"falseDecidable"` and `"booleanEqualityDecidable"`.
- The tactic `"Decide"` of [TypeTheoryTactic]() finds the decision of the goal and proves it with `"decideSoundness"`; an environment extends it with instances of its own.

## Basic Examples

The type of [Decidable]():

```wl
TypeTheoryType[Decidable]
```

<!-- => Prop → Type -->

---

The decisions of an equation are a type:

```wl
TypeTheoryType[Decidable[2 == 3]]
```

<!-- => Type -->

---

The decision of `1 <= 4` computes to `"decidableTrue"` with a proof:

```wl
WeakHeadNormalForm[TypeTheoryTerm["lessEqualDecidable"[1, 4]]]
```

<!-- => decidableTrue[lessEqualTrue[1, 4, equalityReflexivity[lessEqual[1, 4]]]] -->

## Scope

The declaration of [Decidable](), with its two constructors:

```wl
$TypeTheoryEnvironment[Decidable]
```

<!-- => inductive Decidable : Prop → Type | decidableFalse : ∀_{p∶Prop} (¬p) → Decidable[p] | decidableTrue : ∀_{p∶Prop} p → Decidable[p] -->

---

The decision of `4 <= 1` computes to `"decidableFalse"`, with a proof that `4 <= 1` is false:

```wl
WeakHeadNormalForm[TypeTheoryTerm["lessEqualDecidable"[4, 1]]]
```

<!-- => decidableFalse[lessEqualFalse[4, 1, equalityReflexivity[lessEqual[4, 1]]]] -->

---

The decision of an equation of natural numbers:

```wl
WeakHeadNormalForm[TypeTheoryTerm["naturalNumberEqualityDecidable"[2, 3]]]
```

<!-- => decidableFalse[equalFalse[2, 3, equalityReflexivity[equal[2, 3]]]] -->

---

A decision written out from a proof:

```wl
TypeTheoryType[Typed["decidableTrue"["equalityReflexivity"[2]], Decidable[2 == 2]]]
```

<!-- => Decidable[2 == 2] -->

---

The instance that decides a conjunction takes the decisions of its sides as instance-implicit arguments, which elaboration finds in turn:

```wl
TypeTheoryType["andDecidable"]
```

<!-- => ∀_{p∶Prop} ∀_{q∶Prop} ∀_[d∶Decidable[p]] ∀_[e∶Decidable[q]] Decidable[p ∧ q] -->

## Applications

The prelude decides no [Nonempty]() type, so the tactic `"Decide"` does not prove that the natural numbers have an element:

```wl
TypeTheoryProof[Nonempty[Naturals], {"Decide"}]
```

<!-- => Failure["NotDecidable", ...] -->

An instance deciding it, declared with `"Instance" -> True`:

```wl
decided = TypeTheoryEnvironment[{
    TypeTheoryDefinition[NaturalsNonempty, Typed["decidableTrue"["nonempty"[0]], Decidable[Nonempty[Naturals]]], "Instance" -> True]
}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

[Decide]() finds it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[Nonempty[Naturals]], decided]]
```

<!-- => true -->

So does the tactic `"Decide"`:

```wl
TypeTheoryProof[Nonempty[Naturals], decided, {"Decide"}]
```

<!-- => Proof complete -->

---

A decidable proposition is true or false without the excluded middle. `"Cases"` on its decision, in the environment without classical axioms:

```wl
TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[d, Decidable[p]]}, Or[p, Not[p]]], "Constructive", {
    "Introduce"[p, d],
    "Cases"[d]
}]
```

<!-- => Proof, 2 goals: case decidableFalse p ∶ Prop ⊢ (¬p) ⇒ (p ∨ ¬p); case decidableTrue p ∶ Prop ⊢ p ⇒ (p ∨ ¬p) -->

Each case gives a side of the disjunction:

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[d, Decidable[p]]}, Or[p, Not[p]]], "Constructive", {
    "Introduce"[p, d],
    "Cases"[d],
    "Introduce"[h], "Exact"["orIntroductionRight"[h]],
    "Introduce"[h], "Exact"["orIntroductionLeft"[h]]
}]
```

<!-- => Proof complete -->

The theorem it proves:

```wl
constructive = TypeTheoryEnvironment["Constructive", TypeTheoryTheorem[DecidableExcludedMiddle, proof]]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->

It rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[DecidableExcludedMiddle, constructive]]
```

<!-- => <||> -->

## Properties and Relations

[Decide]() finds the decision of a proposition among the instances:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[1 <= 2 && Not[2 == 3]]]]
```

<!-- => true -->

---

The tactic `"Decide"` proves a closed statement by computing its decision:

```wl
TypeTheoryProof[And[1 <= 2, Not[2 == 3]], {"Decide"}]
```

<!-- => Proof complete -->

---

A decision is data, so its recursor eliminates into any universe, `Sort u`, and computes with it, as [Decide]() does into the Booleans:

```wl
TypeTheoryType[InductiveRecursor[Decidable]]
```

<!-- => ∀_{p∶Prop} ∀_m∶Decidable[p] → Sort u (∀_h∶¬p m[decidableFalse[h]]) → (∀_h∶p m[decidableTrue[h]]) → ∀_t∶Decidable[p] m[t] -->

## Possible Issues

A decision is no proposition, so a theorem cannot state one; a definition gives it:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[TwoDecided, Decidable[2 == 2], "naturalNumberEqualityDecidable"[2, 2]]]
```

<!-- => Failure["PropositionExpected", ...] -->

---

`"decidableTrue"` needs a proof of the proposition itself:

```wl
TypeTheoryType[Typed["decidableTrue"["equalityReflexivity"[2]], Decidable[2 == 3]]]
```

<!-- => Failure["TypeMismatch", ...] -->
