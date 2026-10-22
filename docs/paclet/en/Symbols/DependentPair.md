---
Template: Symbol
Name: DependentPair
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DependentPair
Keywords: [dependent pair, sigma type, cubical type theory]
SeeAlso: [DependentSum]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[DependentPair]()[*a*, *b*]</code> is the pair of *a* and *b* : *B*[*a*] in <code>[DependentSum]()[*A*, *B*]</code>, in the cubical environment.

## Details & Options

- *A* and *B* are implicit, found from the type expected.
- Its fields are <code>*p*[[1]]</code> and <code>*p*[[2]]</code>.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The first field of a pair:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[DependentPair["true", Function[{i}, "true"]], DependentSum[Booleans, Function[{Typed[b, Booleans]}, Path[Booleans, b, b]]]][[1]], cubical]]
```

<!-- => true -->
