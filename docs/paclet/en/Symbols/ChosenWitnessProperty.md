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

## Scope

For a proof made with 3, it proves the property of the chosen witness, not of 3:

```wl
TypeTheoryCheck[TypeTheoryTerm[ChosenWitnessProperty[Typed[ExistsIntroduction[3, EqualityReflexivity[6]], Exists[Function[{Typed[n, Naturals]}, n + n == 6]]]]]]
```

<!-- => ChosenWitness[ExistsIntroduction[3, EqualityReflexivity[6]]] + ChosenWitness[ExistsIntroduction[3, EqualityReflexivity[6]]] == 6 -->

## Applications

A function defined by choice, with a theorem about it that [ChosenWitnessProperty]() proves:

```wl
halves = TypeTheoryEnvironment[{
    TypeTheoryDefinition[Half, Function[{Typed[n, Naturals], Typed[h, Exists[Function[{Typed[k, Naturals]}, k + k == n]]]}, ChosenWitness[h]]],
    TypeTheoryTheorem[
        HalfDoubled,
        ForAll[{Typed[n, Naturals], Typed[h, Exists[Function[{Typed[k, Naturals]}, k + k == n]]]}, Half[n, h] + Half[n, h] == n],
        Function[{Typed[n, Naturals], Typed[h, Exists[Function[{Typed[k, Naturals]}, k + k == n]]]}, ChosenWitnessProperty[h]]
    ]
}]
```

<!-- => TypeTheoryEnvironment summary box: 171 constants -->

The theorem:

```wl
halves[HalfDoubled]
```

<!-- => theorem HalfDoubled : ∀_n∶ℕ ∀_h∶∃_k∶ℕ k + k == n Half[n, h] + Half[n, h] == n -->

## Properties and Relations

To prove a proposition no choice is needed: `"Cases"` takes the existential apart and gives its witness:

```wl
TypeTheoryProof[ForAll[{Typed[h, Exists[Function[{Typed[n, Naturals]}, n + n == 6]]]}, Exists[Function[{Typed[m, Naturals]}, m + m + 1 == 7]]], {
    TypeTheoryTactic["Introduce", h],
    TypeTheoryTactic["Cases", h],
    TypeTheoryTactic["Introduce", w, k],
    TypeTheoryTactic["Exact", ExistsIntroduction[w, EqualityCongruence[NaturalNumberSuccessor, k]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

`"Rewrite"` cannot replace `6` by the sum here: `ChosenWitness[h]` holds the property `n + n == 6` as an implicit argument, and replacing `6` there too gives a statement that is not well typed:

```wl
TypeTheoryProof[ForAll[{Typed[h, Exists[Function[{Typed[n, Naturals]}, n + n == 6]]]}, ChosenWitness[h] <= 6], {
    TypeTheoryTactic["Introduce", h],
    TypeTheoryTactic["Rewrite", ChosenWitnessProperty[h], "RightToLeft"]
}]
```

<!-- => Failure["MotiveNotTypeCorrect", ...] -->

Replacing the sum by `6` works, once [LessEqualTransitivity]() and [LessEqualAddition]() put the sum in the goal:

```wl
TypeTheoryProof[ForAll[{Typed[h, Exists[Function[{Typed[n, Naturals]}, n + n == 6]]]}, ChosenWitness[h] <= 6], {
    TypeTheoryTactic["Introduce", h],
    TypeTheoryTactic["Apply", LessEqualTransitivity],
    TypeTheoryTactic["Exact", LessEqualAddition[ChosenWitness[h], ChosenWitness[h]]],
    TypeTheoryTactic["Rewrite", ChosenWitnessProperty[h]],
    TypeTheoryTactic["Exact", LessEqualReflexivity]
}]
```

<!-- => Proof complete -->
