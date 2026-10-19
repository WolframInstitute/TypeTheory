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
