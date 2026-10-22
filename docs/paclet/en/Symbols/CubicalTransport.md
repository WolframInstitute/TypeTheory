---
Template: Symbol
Name: CubicalTransport
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CubicalTransport
Keywords: [transport, line of types, cubical type theory, face, univalence, coercion]
SeeAlso: [CubicalComposition, TypeTheoryCubical, EquivalenceToPath, PathInduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[CubicalTransport]()[*A*, *φ*, *a*]</code> carries *a*, an element of *A*[0], along the line of types *A*, a function of the interval into a universe, to an element of *A*[1]. *A* must be constant where the face *φ* holds, and there the transport is *a*.

## Details & Options

- *A* may be written as a type, the constant line, or as a path of types, which is a function of the interval.
- The kernel checks that *A* is constant on every conjunction of the face *φ*, and fails with `"TransportNotConstant"` otherwise.
- Transport computes by the type it is in: it is *a* where *φ* holds, and in a universe or an inductive type with no parameters and no indices; in a function type and a path type it is built from transport and composition in the parts.
- In a Glue type, where *φ* is 0 and no face of the Glue type holds all along the line, it carries the element under *a* along the base and takes the centers of the fibers of the equivalences at the end: along the path of [EquivalenceToPath](), it applies the equivalence.
- Where no rule applies the transport does not compute. [CubicalTransport]() must be given all three arguments.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Transport of a function along a constant line of function types:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Function[{i}, TypeSpecifier[{Booleans} -> Booleans]], 0, "not"]["true"], cubical]]
```

<!-- => false -->

---

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Transport along univalence applies the equivalence:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "true"], cubical]]
```

<!-- => false -->

## Scope

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Path induction is transport along the connection of a path, `p[Min[i, j]]`:

```wl
cubical[PathInduction]
```

<!-- => definition PathInduction : ∀_{A∶Type u} ∀_{x∶A} ∀_P∶∀_y∶A x≡y→Type v P[x,(i∶Interval)↦x]→∀_{y∶A} ∀_p∶x≡y P[y,p] := {A∶Type u} {x∶A} (P∶∀_y∶A x≡y→Type v) (d∶P[x,(i∶Interval)↦x]) {y∶A} (p∶x≡y)↦CubicalTransport[(i∶Interval)↦P[p[i],(j∶Interval)↦p[i∧j]],0,d] -->

## Possible Issues

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A path of types need not be constant where `1` holds, everywhere:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, Path[TypeUniverse[1], Booleans, Booleans]]}, CubicalTransport[p, 1, "true"]], cubical]]
```

<!-- => Failure["TransportNotConstant", ...] -->
