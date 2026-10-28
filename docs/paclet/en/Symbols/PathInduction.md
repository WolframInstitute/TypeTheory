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

## Scope

[PathInduction]() takes a family *P* over the paths from `x`, its value at the constant path, and a path.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The type of [PathInduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PathInduction, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_P∶∀_y∶A x ≡ y → Type v P[x, (i∶Interval) ↦ x] → ∀_{y ∶ A} ∀_p∶x ≡ y P[y, p] -->

---

In a constant family of Booleans, [PathInduction]() gives *d* on any path, not only on the constant one, since transport in the Booleans is the identity.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

On a path `p` from `"true"` to `y`, it is `"false"`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[y, Booleans], Typed[p, Path[Booleans, "true", y]]}, PathInduction[Function[{Typed[z, Booleans], Typed[q, Path[Booleans, "true", z]]}, Booleans], "false", p]], cubical],
    TypeTheoryTerm[Function[{Typed[y, Booleans], Typed[p, Path[Booleans, "true", y]]}, "false"], cubical]
]
```

<!-- => True -->

## Applications

Path induction proves symmetry: in the family of paths back to `x`, the constant path at `x` is carried along `p` to a path from `y` to `x`.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The proof:

```wl
TypeTheoryProof[ForAll[{Typed[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, Path[A, y, x]], cubical, {
    TypeTheoryTactic["Introduce", A, x, y, p],
    TypeTheoryTactic["Exact", PathInduction[Function[{Typed[z, A], Typed[q, Path[A, x, z]]}, Path[A, z, x]], Function[{Typed[i, Interval]}, x], p]]
}]
```

<!-- => Proof complete -->

## Possible Issues

On the constant path, [PathInduction]() computes to *d* only in a family of closed types. In a family of paths it gives *d* only up to a path, as in cubical type theory.

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

In the family of paths back to `"true"`, path induction on the constant path is not the constant path by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[PathInduction[Function[{Typed[z, Booleans], Typed[q, Path[Booleans, "true", z]]}, Path[Booleans, z, "true"]], Function[{Typed[i, Interval]}, "true"], Function[{Typed[i, Interval]}, "true"]], cubical],
    TypeTheoryTerm[Function[{Typed[i, Interval]}, "true"], cubical]
]
```

<!-- => False -->
