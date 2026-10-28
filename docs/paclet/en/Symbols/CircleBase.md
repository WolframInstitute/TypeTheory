---
Template: Symbol
Name: CircleBase
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CircleBase
Keywords: [circle, base point, higher inductive type, HoTT]
SeeAlso: [CircleLoop, CircleInduction, Circle]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

[CircleBase]() is the point of the circle, [Circle](), in the HoTT environment.

## Details & Options

- The circle is a higher inductive type, given by axioms: [CircleBase](), the path [CircleLoop]() and [CircleInduction]().
- [Circle]() is the built-in symbol of the circle, as [NonNegativeIntegers]() is that of the natural numbers; it shows as 𝕊¹.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The type of [CircleBase]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[CircleBase, hott]]
```

<!-- => 𝕊¹ -->

## Scope

[CircleLoop]() is a path from [CircleBase]() to itself, so it proves `CircleBase == CircleBase`, as reflexivity does.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

A proof by the loop:

```wl
TypeTheoryProof[CircleBase == CircleBase, hott, {TypeTheoryTactic["Exact", CircleLoop]}]
```

<!-- => Proof complete -->

## Applications

Circle induction computes on [CircleBase](), by the rewrite rule [CircleInductionBase](), so `"Reflexivity"` proves what it gives there.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Induction into the constant family of Booleans, at the base point:

```wl
TypeTheoryProof[CircleInduction[Function[{Typed[x, Circle]}, Booleans], "false", TransportConstant[CircleLoop, "false"], CircleBase] == "false", hott, {TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Proof complete -->

## Properties and Relations

[CircleBase]() is an axiom of the HoTT environment, as are the circle, its loop and its induction.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The axioms of the environment:

```wl
Information[hott, "Axioms"]
```

<!-- => {Univalence, Circle, CircleBase, CircleLoop, CircleInduction, CircleInductionLoop} -->

## Possible Issues

The circle is in the HoTT environment only. A term without an environment is in the prelude, which has no [CircleBase]().

The type of [CircleBase](), in the prelude:

```wl
TypeTheoryCheck[TypeTheoryTerm[CircleBase]]
```

<!-- => Failure["ElaborationFailed", ...] -->
