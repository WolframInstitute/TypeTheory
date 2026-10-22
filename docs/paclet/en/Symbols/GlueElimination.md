---
Template: Symbol
Name: GlueElimination
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/GlueElimination
Keywords: [Glue type, unglue, cubical type theory]
SeeAlso: [GlueType, GlueIntroduction, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[GlueElimination]()[*b*]</code> is the element of the base under *b*, an element of a Glue type.

<code>[GlueElimination]()[*A*, *system*, *b*]</code> gives the Glue type <code>[GlueType]()[*A*, *system*]</code> in full.

## Details & Options

- Where a face of the Glue type holds, [GlueElimination]() is the equivalence there applied to *b*; of <code>[GlueIntroduction]()[*terms*, *a*]</code> it is *a*.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Where the face holds, the element under it is the equivalence applied:

```wl
WeakHeadNormalForm[TypeTheoryTerm[GlueElimination[Booleans, {1 -> {Booleans, NegationEquivalence}}, "true"], cubical]]
```

<!-- => false -->

---

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Under an element built over `"false"`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[i, Interval]}, GlueElimination[GlueIntroduction[Booleans, {i == 0 -> {Booleans, NegationEquivalence}}, {i == 0 -> "true"}, "false"]]], cubical],
    TypeTheoryTerm[Function[{Typed[i, Interval]}, "false"], cubical]
]
```

<!-- => True -->
