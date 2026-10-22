---
Template: Symbol
Name: Decide
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Decide
Keywords: [decide, decision, Boolean, computation, instance, prelude]
SeeAlso: [Decidable, DecideSoundness, NaturalNumberEqualityDecidable, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions]
---

## Usage

<code>[Decide]()[*p*]</code> gives the Boolean of the decision of the proposition *p*: `"true"` if it decides *p* true, `"false"` if it decides *p* false.

## Details & Options

- [Decide]() is a definition of the prelude, by recursion on the decision, as Lean's `decide`.
- The decision is an instance-implicit argument: elaboration finds it among the instances of <code>[Decidable]()[*p*]</code>.
- The prelude has instances deciding `==` and `<=` of natural numbers, `==` of Booleans, [True](), [False](), [Not](), [And]() and [Or](); a definition such as [Less]() or [Unequal]() unfolds to a proposition that has one.
- <code>[Construct]()[[Decide](), *p*, *d*]</code> gives the decision *d* itself.
- The Booleans are named by strings, `"true"` and `"false"`.

## Basic Examples

The type of [Decide]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Decide]]
```

<!-- => ∀_p∶Prop ∀_[d∶Decidable[p]] 𝔹 -->

---

2 == 2 is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2 == 2]]]
```

<!-- => true -->

---

3 <= 2 is decided false:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[3 <= 2]]]
```

<!-- => false -->

## Scope

The connectives combine decisions, and [Less]() and [Unequal]() unfold to propositions with decisions:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2 < 3 && 4 != 5]]]
```

<!-- => true -->

---

Equations of Booleans are decided too:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide["true" == "not"["false"]]]]
```

<!-- => true -->

---

A decision given explicitly:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Construct[Decide, 3 <= 2, LessEqualDecidable[3, 2]]]]
```

<!-- => false -->

## Properties and Relations

[DecideSoundness]() turns a decision that computes to `"true"` into a proof:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DecideSoundness[EqualityReflexivity["true"]], 3 == 3]]]
```

<!-- => 3 == 3 -->

## Possible Issues

A proposition with no instance of [Decidable]() has no decision:

```wl
TypeTheoryCheck[TypeTheoryTerm[Decide[Nonempty[Naturals]]]]
```

<!-- => Failure["NoInstance", ...] -->
