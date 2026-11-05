---
Template: Symbol
Name: ChosenWitness
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ChosenWitness
Keywords: [witness, choice, existential, exists, prelude, classical logic]
SeeAlso: [Exists, Subtype]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ChosenWitness]()[*h*]</code> is an element *x* with <code>*P*[*x*]</code>, chosen from a proof *h* of <code>[Exists]()[*P*]</code>.

## Details & Options

- [ChosenWitness]() is a definition of the prelude. The recursor of [Exists]() turns *h* into a proof of <code>[Nonempty]()[[Subtype]()[*P*]]</code>, `"choice"` chooses an element of the [Subtype](), and [ChosenWitness]() is its first field.
- A proof of an existential statement cannot be taken apart to give its witness as data; [ChosenWitness]() gives one, and `"chosenWitnessProperty"` proves that it has the property.
- The type of the witness and *P* are implicit arguments, found from the type of *h*.
- It does not compute, as `"choice"` does not.

## Basic Examples

The type of [ChosenWitness]():

```wl
TypeTheoryType[ChosenWitness]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} Exists[P] → α -->

---

A number whose double is 6, from a proof that there is one:

```wl
TypeTheoryType[Typed[h, Exists[Typed[n, Naturals] |-> n + n == 6]] |-> ChosenWitness[h]]
```

<!-- => (∃_n∶ℕ n + n == 6) → ℕ -->

## Scope

A witness chosen from a proof made with 3; [Typed]() gives the property, which the proof alone does not determine:

```wl
TypeTheoryType[ChosenWitness[Typed["existsIntroduction"[3, "equalityReflexivity"[6]], Exists[Typed[n, Naturals] |-> n + n == 6]]]]
```

<!-- => ℕ -->

## Applications

A function defined by choice: half of a number, given a proof that it has a half:

```wl
halves = TypeTheoryEnvironment[{TypeTheoryDefinition[Half, {Typed[n, Naturals], Typed[h, Exists[Typed[k, Naturals] |-> k + k == n]]} |-> ChosenWitness[h]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Its declaration:

```wl
halves[Half]
```

<!-- => definition Half : ∀_n∶ℕ (∃_k∶ℕ k + k == n) → ℕ := (n ∶ ℕ) (h ∶ ∃_k∶ℕ k + k == n) ↦ ChosenWitness[h] -->

## Properties and Relations

The witness does not depend on the proof: proofs made with 2 and with 4 give the same one, since the two proofs are equal:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[ChosenWitness[Typed["existsIntroduction"[2, "lessEqualReflexivity"], Exists[Typed[n, Naturals] |-> 2 <= n]]]],
    TypeTheoryTerm[ChosenWitness[Typed["existsIntroduction"[4, "lessEqualStep"["lessEqualStep"["lessEqualReflexivity"]]], Exists[Typed[n, Naturals] |-> 2 <= n]]]]
]
```

<!-- => True -->

## Possible Issues

It does not compute, so even from a proof made with 3 the chosen number is not 3 by computation:

```wl
TypeTheoryProof[ChosenWitness[Typed["existsIntroduction"[3, "equalityReflexivity"[6]], Exists[Typed[n, Naturals] |-> n + n == 6]]] == 3, {"Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->
