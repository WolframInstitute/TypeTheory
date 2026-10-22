---
Template: Symbol
Name: IsomorphismEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsomorphismEquivalence
Keywords: [isomorphism, equivalence, cubical type theory, Glue type]
SeeAlso: [Equivalence, NegationEquivalence, EquivalenceToPath]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IsomorphismEquivalence]()[*f*, *g*, *s*, *t*]</code> is the equivalence that a function *f* with an inverse *g* gives, *s* and *t* the paths from *f*[*g*[*b*]] to *b* and from *g*[*f*[*a*]] to *a*.

## Details & Options

- The center of the fiber over *y* is {*g*[*y*], *s*[*y*]}; the square that joins any element of the fiber to it is built from compositions, as in the cubical library of Agda.
- Its function is *f*: along [EquivalenceToPath]() of it, transport applies *f*.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Negation, the isomorphism of the Booleans with themselves that is its own inverse:

```wl
cubical[NegationEquivalence]
```

<!-- => definition NegationEquivalence : Equivalence[𝔹, 𝔹] := IsomorphismEquivalence[not, not, NegationInvolution, NegationInvolution] -->
