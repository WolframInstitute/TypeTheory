---
Template: Symbol
Name: CubicalComposition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CubicalComposition
Keywords: [composition, open box, system, face, cubical type theory, hcomp]
SeeAlso: [CubicalTransport, PathTransitivity, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[CubicalComposition]()[*A*, [Function]()[{*i*}, {*face* -> *u*, ...}], *a*]</code> composes in the type *A*: it gives the lid of the open box whose base is *a* and whose sides are the lines *u* over the faces.

## Details & Options

- A face is an element of the interval read as the condition that it is 1; a system writes them `i == 0`, `i == 1`, [And]() and [Or]() of faces, or an element of the interval. The faces may not mention the variable of the sides.
- Each side is checked where its face holds, with the face substituted into it, its type and its context; any two sides agree where both faces hold, and each is *a* at `i = 0`.
- Where a face holds, the composition is its side at `i = 1`. In a function type it composes the values, and in a path type the points, with the path's endpoints as two more sides.
- Composition in a universe has no rule, and does not compute. [CubicalComposition]() must be given all three arguments.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Where a face holds, the composition is its side at 1:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalComposition[Booleans, Function[{j}, {1 -> "true"}], "true"], cubical]]
```

<!-- => true -->

---

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The concatenation of paths is a composition:

```wl
cubical[PathTransitivity]
```

<!-- => definition PathTransitivity : ∀_{A∶Type u} ∀_{x∶A} ∀_{y∶A} ∀_{z∶A} x≡y→y≡z→x≡z := {A∶Type u} {x∶A} {y∶A} {z∶A} (p∶x≡y) (q∶y≡z) (i∶Interval)↦CubicalComposition[A,(j∶Interval)↦{i == 0->x,i == 1->q[j]},p[i]] -->

## Possible Issues

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A side must be the base at 0:

```wl
TypeTheoryEnvironment[cubical, {TypeTheoryDefinition[WrongSide, Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]]},
    Function[{Typed[i, Interval]}, CubicalComposition[A, Function[{j}, {i == 0 -> y}], p[i]]]
]]}]
```

<!-- => Failure["CapMismatch", ...] -->
