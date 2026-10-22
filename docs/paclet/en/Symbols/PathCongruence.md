---
Template: Symbol
Name: PathCongruence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PathCongruence
Keywords: [path, congruence, function, cubical type theory]
SeeAlso: [PathSymmetry, PathFunctionExtensionality]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[PathCongruence]()[*f*, *p*]</code> is the path from *f*[*x*] to *f*[*y*] that a function *f* gives from a path *p* from *x* to *y*: the function of *i* that is *f*[*p*[*i*]].

## Details & Options

- It is a function of the interval, with no composition.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathCongruence, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_f∶A → B ∀_{x ∶ A} ∀_{y ∶ A} x ≡ y → f[x] ≡ f[y] -->
