---
Template: Symbol
Name: UnivalenceComputation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/UnivalenceComputation
Keywords: [univalence, computation rule, transport, HoTT]
SeeAlso: [EquivalenceToEquality, EqualityToEquivalence, Univalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[UnivalenceComputation]()[*e*]</code> proves <code>[EqualityToEquivalence]()[[EquivalenceToEquality]()[*e*]] == *e*</code>: carrying along the path of an equivalence is that equivalence.

## Details & Options

- [UnivalenceComputation]() is a theorem of the HoTT environment, read off the axiom [Univalence](). Without Prop, a theorem may state any type, and like any theorem it is never unfolded.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [UnivalenceComputation]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[UnivalenceComputation, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} ∀_e∶Equivalence[A, B] EqualityToEquivalence[EquivalenceToEquality[e]] == e -->

## Scope

An instance, for the negation of the Booleans, [NegationEquivalence]().

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Its statement:

```wl
TypeTheoryCheck[TypeTheoryTerm[UnivalenceComputation[NegationEquivalence], hott]]
```

<!-- => EqualityToEquivalence[EquivalenceToEquality[NegationEquivalence]] == NegationEquivalence -->

## Applications

With [EqualityCongruence](), [UnivalenceComputation]() shows that the path of negation, read back as an equivalence, takes `"true"` to `"false"`, up to a path.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The proof:

```wl
TypeTheoryProof[EqualityToEquivalence[EquivalenceToEquality[NegationEquivalence]][[1]]["true"] == "false", hott, {
    TypeTheoryTactic["Exact", EqualityCongruence[Function[{Typed[e, Equivalence[Booleans, Booleans]]}, e[[1]]["true"]], UnivalenceComputation[NegationEquivalence]]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

In the cubical environment univalence computes, and no such theorem is needed: transport along the path of negation, [EquivalenceToPath](), gives `"false"` by computation.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Transport of `"true"` along the path of negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "true"], cubical]]
```

<!-- => false -->

## Possible Issues

[Univalence]() is an axiom in the HoTT environment, so the two sides of [UnivalenceComputation]() are equal by the theorem, not by computation.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

`"Reflexivity"` does not prove the instance for negation:

```wl
TypeTheoryProof[EqualityToEquivalence[EquivalenceToEquality[NegationEquivalence]] == NegationEquivalence, hott, {TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Failure["NotReflexive", ...] -->
