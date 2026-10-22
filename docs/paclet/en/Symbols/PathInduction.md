---
Template: Symbol
Name: PathInduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PathInduction
Keywords: [path induction, J, transport, cubical type theory]
SeeAlso: [CubicalTransport, PathSymmetry]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[PathInduction]()[*P*, *d*, *p*]</code> gives *P*[*y*, *p*] for a path *p* from *x* to *y*, from *d* : *P*[*x*, the constant path]: transport along the line of *i* that is *P*[*p*[*i*], the function of *j* that is <code>*p*[[Min]()[*i*, *j*]]</code>].

## Details & Options

- On the constant path it computes to *d* where *P* is a family of closed types; in general only up to a path, as in cubical type theory.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A family of Booleans along a constant path:

```wl
WeakHeadNormalForm[TypeTheoryTerm[PathInduction[Function[{Typed[y, Booleans], Typed[p, Path[Booleans, "true", y]]}, Booleans], "false", Function[{i}, "true"]], cubical]]
```

<!-- => false -->
