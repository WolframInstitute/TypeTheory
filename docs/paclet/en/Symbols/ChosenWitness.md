---
Template: Symbol
Name: ChosenWitness
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ChosenWitness
Keywords: [witness, choice, existential, exists, prelude, classical logic, axiom of choice, chosenWitnessProperty, Classical.choose]
SeeAlso: [Exists, Subtype, Nonempty, TypeTheoryAxiomClosure]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ChosenWitness]()[*h*]</code> is an element *x* with <code>*P*[*x*]</code>, chosen from a proof *h* of <code>[Exists]()[*P*]</code>.

## Details & Options

- [ChosenWitness]() is a definition of the prelude, as Lean's `Classical.choose`. The recursor of [Exists]() turns *h* into a proof of <code>[Nonempty]()[[Subtype]()[*P*]]</code>, the axiom `"choice"` chooses an element of the [Subtype](), and [ChosenWitness]() is its first field.
- A proof of an existential statement cannot be taken apart to give its witness as data; [ChosenWitness]() gives one, and `"chosenWitnessProperty"` proves that it has the property: <code>"chosenWitnessProperty"[*h*]</code> proves <code>*P*[[ChosenWitness]()[*h*]]</code>.
- The type of the witness and *P* are implicit arguments, found from the type of *h*. A proof written out with `"existsIntroduction"` does not determine *P*, so it is given with [Typed]().
- Any two proofs of a proposition are equal, so the witness depends on the statement *h* proves, not on the witness *h* was made with.
- It does not compute, as `"choice"` does not, and it rests on the axiom `"choice"`.

## Basic Examples

The type of [ChosenWitness]():

```wl
TypeTheoryType[ChosenWitness]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} Exists[P] → α -->

---

A number whose double is 6, from a proof that there is one:

```wl
TypeTheoryType[Typed[h, Exists[n |-> n + n == 6]] |-> ChosenWitness[h]]
```

<!-- => (∃_n∶ℕ n + n == 6) → ℕ -->

---

`"chosenWitnessProperty"` proves that the number chosen has the property:

```wl
TypeTheoryType[Typed[h, Exists[n |-> n + n == 6]] |-> "chosenWitnessProperty"[h]]
```

<!-- => ∀_h∶∃_n∶ℕ n + n == 6 ChosenWitness[h] + ChosenWitness[h] == 6 -->

## Scope

A witness chosen from a proof made with 3; [Typed]() gives the property, which the proof alone does not determine:

```wl
TypeTheoryType[ChosenWitness[Typed["existsIntroduction"[3, "equalityReflexivity"[6]], Exists[n |-> n + n == 6]]]]
```

<!-- => ℕ -->

---

The type of `"chosenWitnessProperty"`:

```wl
TypeTheoryType["chosenWitnessProperty"]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} ∀_h∶Exists[P] P[ChosenWitness[h]] -->

---

A proof that uses the property of the chosen witness:

```wl
TypeTheoryProof[ForAll[{Typed[h, Exists[n |-> n + n == 6]]}, ChosenWitness[h] + ChosenWitness[h] == 6], {
    "Introduce"[h],
    "Exact"["chosenWitnessProperty"[h]]
}]
```

<!-- => Proof complete -->

## Applications

A function defined by choice: half of a number, given a proof that it has a half:

```wl
halves = TypeTheoryEnvironment[{TypeTheoryDefinition[Half, {n, Typed[h, Exists[k |-> k + k == n]]} |-> ChosenWitness[h]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its declaration:

```wl
halves[Half]
```

<!-- => definition Half : ∀_n∶ℕ (∃_k∶ℕ k + k == n) → ℕ := (n ∶ ℕ) (h ∶ ∃_k∶ℕ k + k == n) ↦ ChosenWitness[h] -->

Twice the half is the number, by the property of the witness, since `Half` unfolds to it:

```wl
TypeTheoryProof[ForAll[{n, Typed[h, Exists[k |-> k + k == n]]}, Half[n, h] + Half[n, h] == n], halves, {
    "Introduce"[n, h],
    "Exact"["chosenWitnessProperty"[h]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The witness does not depend on the proof: proofs made with 2 and with 4 give the same one, since the two proofs are equal:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[ChosenWitness[Typed["existsIntroduction"[2, "lessEqualReflexivity"], Exists[n |-> 2 <= n]]]],
    TypeTheoryTerm[ChosenWitness[Typed["existsIntroduction"[4, "lessEqualStep"["lessEqualStep"["lessEqualReflexivity"]]], Exists[n |-> 2 <= n]]]]
]
```

<!-- => True -->

---

The definition of [ChosenWitness](): the first field, `[[1]]`, of the element of the [Subtype]() that `"choice"` chooses:

```wl
$TypeTheoryEnvironment[ChosenWitness]
```

<!-- => definition ChosenWitness : ∀_{α∶Sort u} ∀_{P∶α → Prop} Exists[P] → α := {α∶Sort u} {P∶α → Prop} (h∶Exists[P]) ↦ choice[Exists_rec[(t∶Exists[P]) ↦ Nonempty[Subtype[P]], (w∶α) (k∶P[w]) ↦ nonempty[subtype[w, k]], h]][[1]] -->

---

It rests on the axiom of choice:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[ChosenWitness]]
```

<!-- => <|"choice" -> "Signature"|> -->

## Possible Issues

It does not compute, so even from a proof made with 3 the chosen number is not 3 by computation:

```wl
TypeTheoryProof[ChosenWitness[Typed["existsIntroduction"[3, "equalityReflexivity"[6]], Exists[n |-> n + n == 6]]] == 3, {"Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

---

Computation stops at `"choice"`, an axiom:

```wl
WeakHeadNormalForm[TypeTheoryTerm[ChosenWitness[Typed["existsIntroduction"[3, "equalityReflexivity"[6]], Exists[n |-> n + n == 6]]]]]
```

<!-- => choice[Exists_rec[(t ∶ ∃_n∶ℕ n + n == 6) ↦ Nonempty[{n ∶ ℕ // n + n == 6}], (w ∶ ℕ) (k ∶ ((n ∶ ℕ) ↦ n + n == 6)[w]) ↦ nonempty[subtype[w, k]], existsIntroduction[3, equalityReflexivity[6]]]][[1]] -->

---

Without [Typed](), the property is not found from the proof alone, as many properties hold of 3:

```wl
TypeTheoryType[ChosenWitness["existsIntroduction"[3, "equalityReflexivity"[6]]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The constructive environment has no `"choice"`, and so no [ChosenWitness]():

```wl
TypeTheoryType[ChosenWitness, "Constructive"]
```

<!-- => Failure["ElaborationFailed", ...] -->
