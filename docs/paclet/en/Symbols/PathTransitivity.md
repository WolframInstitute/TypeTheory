---
Template: Symbol
Name: PathTransitivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PathTransitivity
Keywords: [path, transitivity, concatenation, composition, cubical type theory]
SeeAlso: [PathSymmetry, CubicalComposition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[PathTransitivity]()[*p*, *q*]</code> is the path *p* followed by *q*: at *i* the composition of the box with base *p*[*i*] and sides the constant `x` at `i == 0` and *q* at `i == 1`.

## Details & Options

- Its endpoints are those of *p* at 0 and *q* at 1, by computation.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathTransitivity, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_{y ∶ A} ∀_{z ∶ A} x ≡ y → y ≡ z → x ≡ z -->
