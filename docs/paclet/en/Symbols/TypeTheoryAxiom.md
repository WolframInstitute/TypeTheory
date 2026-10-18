---
Template: Symbol
Name: TypeTheoryAxiom
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryAxiom
Keywords: [axiom, declaration, assumption, excluded middle, environment]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryAxiom]()[*name*, *type*]</code> declares *name* as an axiom of the given *type*, when added to a [TypeTheoryEnvironment]().

## Details & Options

- A declaration is inert until it is added to an environment with <code>[TypeTheoryEnvironment]()[*env*, {*declaration*}]</code> or <code>[Append]()[*env*, *declaration*]</code>, which check that *type* is a type.
- An axiom is assumed, not proved. <code>[Information]()[*env*, "Axioms"]</code> lists the axioms of an environment.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

Assume the excluded middle:

```wl
classical = Append[
    TypeTheoryEnvironment["Prelude"],
    TypeTheoryAxiom[ExcludedMiddle, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]
];
TypeOf[TypeTheoryTerm[ExcludedMiddle[True], classical]]
```

<!-- => True || !True -->

The environment's axioms:

```wl
Information[classical, "Axioms"]
```

<!-- => {ExcludedMiddle} -->

## Possible Issues

An axiom's type must be a type:

```wl
Append[TypeTheoryEnvironment["Prelude"], TypeTheoryAxiom[Five, 5]]
```

<!-- => Failure["TypeExpected", ...] -->
