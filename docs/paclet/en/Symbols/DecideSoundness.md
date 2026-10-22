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

<code>[DecideSoundness]()[*d*, *h*]</code> proves the proposition *p* from a decision *d* of *p* and a proof *h* of <code>[Decide]()[*d*] == "true"</code>.

## Details & Options

- [DecideSoundness]() is a theorem of the prelude, by cases on *d*, as Lean's `of_decide_eq_true`.
- Given <code>[EqualityReflexivity]()["true"]</code> for *h*, the kernel checks the proof by computing <code>[Decide]()[*d*]</code>: a proof by computation.
- The tactic `"Decide"` of [TypeTheoryTactic]() builds exactly this proof.

## Basic Examples

The statement of [DecideSoundness]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DecideSoundness]]
```

<!-- => ∀_{p ∶ Prop} ∀_d∶Decidable[p] Decide[d] == true ⇒ p -->

---

3 == 3, by computing its decision:

```wl
TypeTheoryCheck[TypeTheoryTerm[DecideSoundness[NaturalNumberEqualityDecidable[3, 3], EqualityReflexivity["true"]]]]
```

<!-- => 3 == 3 -->

## Properties and Relations

The tactic `"Decide"` proves a goal with it:

```wl
TypeTheoryProof[2 + 2 == 4, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
