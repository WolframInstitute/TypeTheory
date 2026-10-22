---
Template: Symbol
Name: GlueIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/GlueIntroduction
Keywords: [Glue type, glue, cubical type theory, system]
SeeAlso: [GlueType, GlueElimination, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[GlueIntroduction]()[{*face* -> *t*, ...}, *a*]</code> is the element of the Glue type expected that is *t* where a face holds, over *a*, an element of the base that the equivalence takes *t* to.

<code>[GlueIntroduction]()[*A*, *system*, {*face* -> *t*, ...}, *a*]</code> gives the Glue type <code>[GlueType]()[*A*, *system*]</code> in full.

## Details & Options

- The terms have the faces of the Glue type, in order. Each equivalence must take its term to *a* where its face holds.
- Where a face holds, the element is its term. [GlueElimination]() of it is *a*.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

An element of a Glue type over the Booleans, `"true"` where `i == 0` holds, over `"false"`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[i, Interval]}, GlueIntroduction[Booleans, {i == 0 -> {Booleans, NegationEquivalence}}, {i == 0 -> "true"}, "false"]], cubical]]
```

<!-- => Path[(i ∶ Interval) ↦ GlueType[𝔹, {i == 0 -> DependentPair[𝔹, NegationEquivalence]}], true, GlueIntroduction[{False -> true}, false]] -->

## Possible Issues

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Negation takes `"true"` to `"false"`, not to `"true"`:

```wl
TypeTheoryEnvironment[cubical, {TypeTheoryDefinition[WrongBase, Function[{Typed[i, Interval]}, GlueIntroduction[Booleans, {i == 0 -> {Booleans, NegationEquivalence}}, {i == 0 -> "true"}, "true"]]]}]
```

<!-- => Failure["GlueMismatch", ...] -->
