---
Template: Symbol
Name: DependentSum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DependentSum
Keywords: [dependent sum, sigma type, pair, cubical type theory]
SeeAlso: [DependentPair, TypeTheoryCubical, Equivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[DependentSum]()[*A*, *B*]</code> is the dependent sum Σ *x* : *A*, *B*[*x*] of the cubical environment, whose elements are the pairs <code>[DependentPair]()[*a*, *b*]</code>.

## Details & Options

- It is a structure: <code>*p*[[1]]</code> and <code>*p*[[2]]</code> are the fields of a pair *p*.
- [TypeTheoryCubical]() names it, and the kernel writes the equivalences of Glue types with it.
- It is a constant of <code>[TypeTheoryEnvironment]()["Cubical"]</code>.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its declaration:

```wl
cubical[DependentSum]
```

<!-- => inductive DependentSum : ∀_A∶Type u (A→Type v)→Type (max u v) ; | DependentPair : ∀_{A∶Type u} ∀_{B∶A→Type v} ∀_a∶A B[a]→DependentSum[A,B] -->

## Scope

A type *A* and a family of types over it give a type, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The type of [DependentSum]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentSum, cubical]]
```

<!-- => ∀_A∶Type u (A → Type v) → Type (max u v) -->

---

With a family that does not depend on the first element, the pairs are plain pairs, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A pair of two Booleans:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DependentPair["true", "false"], DependentSum[Booleans, Function[{Typed[b, Booleans]}, Booleans]]], cubical]]
```

<!-- => DependentSum[𝔹, (b ∶ 𝔹) ↦ 𝔹] -->

Its second field:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[DependentPair["true", "false"], DependentSum[Booleans, Function[{Typed[b, Booleans]}, Booleans]]][[2]], cubical]]
```

<!-- => false -->

## Applications

The cubical library writes [Fiber](), [IsContractible]() and [Equivalence]() with it, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A fiber of *f* over *y* is the dependent sum of the elements *x* with a path from `f[x]` to *y*:

```wl
cubical[Fiber]
```

<!-- => definition Fiber : ∀_{A ∶ Type u} ∀_{B ∶ Type u} (A → B) → B → Type u := {A ∶ Type u} {B ∶ Type u} (f ∶ A → B) (y ∶ B) ↦ DependentSum[A, (x ∶ A) ↦ f[x] ≡ y] -->

## Possible Issues

The prelude does not have it, so a term that uses it names the cubical environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentSum]]
```

<!-- => Failure["ElaborationFailed", ...] -->
