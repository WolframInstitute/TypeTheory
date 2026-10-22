---
Template: Symbol
Name: PathSymmetry
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PathSymmetry
Keywords: [path, symmetry, inverse, cubical type theory]
SeeAlso: [PathTransitivity, IntervalReverse]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[PathSymmetry]()[*p*]</code> is the path *p* reversed: the function of *i* that is *p*[1 - *i*].

## Details & Options

- Reversing twice gives the path back, by computation.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathSymmetry, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_{y ∶ A} x ≡ y → y ≡ x -->

---

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Reversing twice:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, PathSymmetry[PathSymmetry[p]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p], cubical]
]
```

<!-- => True -->
