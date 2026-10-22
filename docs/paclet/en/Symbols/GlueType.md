---
Template: Symbol
Name: GlueType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/GlueType
Keywords: [Glue type, univalence, equivalence, cubical type theory, system]
SeeAlso: [GlueIntroduction, GlueElimination, EquivalenceToPath, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[GlueType]()[*A*, {*face* -> *pair*, ...}]</code> is the type *A* glued, where each face holds, to the type *T* of the pair, an element {*T*, *e*} of the dependent sum with *e* an equivalence from *T* to *A*; where a face holds it is *T*.

## Details & Options

- A pair may be written as `{T, e}`, or with the constructor of the dependent sum, such as <code>[DependentPair]()[*T*, *e*]</code>.
- An equivalence is a function with contractible fibers, the type the kernel writes with the dependent sum and paths; [Equivalence]() is that type in the cubical environment.
- Where a face holds, the Glue type is its glued type. Univalence, [EquivalenceToPath](), is a line of Glue types.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Where its face holds, a Glue type is its glued type:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[GlueType[Booleans, {1 -> {Booleans, NegationEquivalence}}], cubical], TypeTheoryTerm[Booleans, cubical]]
```

<!-- => True -->

---

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Univalence glues along the equivalence at 0 and the identity at 1:

```wl
cubical[EquivalenceToPath]
```

<!-- => definition EquivalenceToPath : ∀_{A∶Type u} ∀_{B∶Type u} Equivalence[A,B]→A≡B := {A∶Type u} {B∶Type u} (e∶Equivalence[A,B]) (i∶Interval)↦GlueType[B,{i == 0->DependentPair[A,e],i == 1->DependentPair[B,IdentityEquivalence[B]]}] -->

## Possible Issues

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

A function is not an equivalence:

```wl
TypeTheoryEnvironment[cubical, {TypeTheoryDefinition[NotGlued, Function[{Typed[i, Interval]}, GlueType[Booleans, {i == 0 -> {Booleans, "not"}}]]]}]
```

<!-- => Failure["TypeMismatch", ...] -->
