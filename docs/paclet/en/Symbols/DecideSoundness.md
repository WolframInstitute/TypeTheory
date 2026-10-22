---
Template: Symbol
Name: DecideSoundness
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DecideSoundness
Keywords: [decide, soundness, decision, proof by computation, prelude]
SeeAlso: [Decide, Decidable, EqualityReflexivity, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DecideSoundness]()[*h*]</code> proves the proposition *p* from a proof *h* of <code>[Decide]()[*p*] == "true"</code>.

## Details & Options

- [DecideSoundness]() is a theorem of the prelude, by cases on the decision, as Lean's `of_decide_eq_true`.
- *p* is an implicit argument and the decision an instance-implicit one, the instance of <code>[Decidable]()[*p*]</code> that elaboration finds.
- *p* comes from the type the proof is checked against, as with [Typed]() or a tactic's goal.
- Given <code>[EqualityReflexivity]()["true"]</code> for *h*, the kernel checks the proof by computing <code>[Decide]()[*p*]</code>: a proof by computation.
- The tactic `"Decide"` of [TypeTheoryTactic]() builds exactly this proof.

## Basic Examples

The statement of [DecideSoundness]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DecideSoundness]]
```

<!-- => ∀_{p∶Prop} ∀_[d∶Decidable[p]] Decide[p] == true ⇒ p -->

---

3 == 3, by computing its decision:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DecideSoundness[EqualityReflexivity["true"]], 3 == 3]]]
```

<!-- => 3 == 3 -->

## Scope

A statement with connectives is proved the same way:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DecideSoundness[EqualityReflexivity["true"]], 3^2 + 4^2 == 5^2 && 2 < 3]]]
```

<!-- => 3^2 + 4^2 == 5^2 ∧ 2 < 3 -->

## Properties and Relations

The tactic `"Decide"` proves a goal with it:

```wl
TypeTheoryProof[2 + 2 == 4, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

A decision that computes to `"false"` proves nothing: the kernel does not compute <code>[Decide]()[*p*]</code> to `"true"`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DecideSoundness[EqualityReflexivity["true"]], 2 == 3]]]
```

<!-- => Failure["TypeMismatch", ...] -->
