---
Template: Symbol
Name: UniverseNotSet
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/UniverseNotSet
Keywords: [universe, set, univalence, HoTT, homotopy type theory]
SeeAlso: [IsSet, Univalence, NegationEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

[UniverseNotSet]() proves <code>[Not]()[[IsSet]()[[TypeUniverse]()[1]]]</code>: the universe of types is not a set.

## Details & Options

- The proof follows the HoTT book. If any two paths between types were equal, the path that [NegationEquivalence]() gives through [Univalence]() would be reflexivity, so carrying `true` along it would give `true`; by [UnivalenceComputation]() it gives what negation does, `false`, and a path from `false` to `true` carries an element of [True]() to one of [False]().
- It is a theorem of the HoTT environment: its statement is a type, as any statement is under rules without Prop.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [UniverseNotSet]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[UniverseNotSet, hott]]
```

<!-- => ¬IsSet[Type] -->

## Scope

[Not]() is a function into [False](), so [UniverseNotSet]() takes a proof that the universe is a set to an element of [False]().

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement, unfolded:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Not[IsSet[TypeUniverse[1]]], hott]]
```

<!-- => IsSet[Type] → False -->

## Applications

From a proof that the universe is a set, anything follows: [UniverseNotSet]() gives an element of [False](), and [FalseElimination]() an element of any type.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

If the universe is a set, `"true"` equals `"false"`:

```wl
TypeTheoryProof[Implies[IsSet[TypeUniverse[1]], "true" == "false"], hott, {
    TypeTheoryTactic["Introduce", s],
    TypeTheoryTactic["Exact", FalseElimination[UniverseNotSet[s]]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Under the prelude's rules the universe is a set: an equation is a proposition, and any two proofs of a proposition are equal by computation.

In the prelude, `"Reflexivity"` proves that any two proofs of an equation between types are equal:

```wl
TypeTheoryProof[ForAll[{Typed[x, TypeUniverse[1]], Typed[y, TypeUniverse[1]], Typed[p, x == y], Typed[q, x == y]}, p == q], {
    TypeTheoryTactic["Introduce", x, y, p, q],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

## Possible Issues

[UniverseNotSet]() is a theorem of the HoTT environment only. A term without an environment is in the prelude, which does not have it.

The statement of [UniverseNotSet](), in the prelude:

```wl
TypeTheoryCheck[TypeTheoryTerm[UniverseNotSet]]
```

<!-- => Failure["ElaborationFailed", ...] -->
