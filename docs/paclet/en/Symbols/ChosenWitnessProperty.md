---
Template: Symbol
Name: ChosenWitnessProperty
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ChosenWitnessProperty
Keywords: [witness, choice, existential, property, prelude, classical logic]
SeeAlso: [ChosenWitness, Choice, ExistsIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ChosenWitnessProperty]()[*h*]</code> proves <code>*P*[[ChosenWitness]()[*h*]]</code> from a proof *h* of <code>[Exists]()[*P*]</code>.

## Details & Options

- [ChosenWitnessProperty]() is a theorem of the prelude, proved by the second field of the element of <code>[Subtype]()[*P*]</code> that [Choice]() chooses.
- The type of the witness and *P* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [ChosenWitnessProperty]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ChosenWitnessProperty]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} ∀_h∶Exists[P] P[ChosenWitness[h]] -->

---

The double of the chosen number is 6:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Exists[Function[{Typed[n, Naturals]}, n + n == 6]]]}, ChosenWitnessProperty[h]]]]
```

<!-- => ∀_h∶∃_n∶ℕ n + n == 6 ChosenWitness[h] + ChosenWitness[h] == 6 -->
