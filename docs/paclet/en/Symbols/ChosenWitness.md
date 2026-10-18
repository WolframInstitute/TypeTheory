---
Template: Symbol
Name: ChosenWitness
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ChosenWitness
Keywords: [witness, choice, existential, exists, prelude, classical logic]
SeeAlso: [ChosenWitnessProperty, Choice, Exists, Subtype]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ChosenWitness]()[*h*]</code> is an element *x* with <code>*P*[*x*]</code>, chosen from a proof *h* of <code>[Exists]()[*P*]</code>.

## Details & Options

- [ChosenWitness]() is a definition of the prelude. The recursor of [Exists]() turns *h* into a proof of <code>[Nonempty]()[[Subtype]()[*P*]]</code>, [Choice]() chooses an element of the [Subtype](), and [ChosenWitness]() is its first field.
- A proof of an existential statement cannot be taken apart to give its witness as data; [ChosenWitness]() gives one, and [ChosenWitnessProperty]() proves that it has the property.
- The type of the witness and *P* are implicit arguments, found from the type of *h*.
- It does not compute, as [Choice]() does not.

## Basic Examples

The type of [ChosenWitness]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ChosenWitness]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} Exists[P] → α -->

---

A number whose double is 6, from a proof that there is one:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Exists[Function[{Typed[n, NonNegativeIntegers]}, n + n == 6]]]}, ChosenWitness[h]]]]
```

<!-- => (∃_n∶ℕ n + n == 6) → ℕ -->
