---
Template: Symbol
Name: DependentPair
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DependentPair
Keywords: [dependent pair, sigma type, cubical type theory]
SeeAlso: [DependentSum]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[DependentPair]()[*a*, *b*]</code> is the pair of *a* and *b* : *B*[*a*] in <code>[DependentSum]()[*A*, *B*]</code>, in the cubical environment.

## Details & Options

- *A* and *B* are implicit, found from the type expected.
- Its fields are <code>*p*[[1]]</code> and <code>*p*[[2]]</code>.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The first field of a pair:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[DependentPair["true", Function[{i}, "true"]], DependentSum[Booleans, Function[{Typed[b, Booleans]}, Path[Booleans, b, b]]]][[1]], cubical]]
```

<!-- => true -->

## Scope

The type of the second element depends on the first, here a path from the first element to itself, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

`"true"` with its constant path, with [Typed]() giving the family:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DependentPair["true", Function[{i}, "true"]], DependentSum[Booleans, Function[{Typed[b, Booleans]}, Path[Booleans, b, b]]]], cubical]]
```

<!-- => DependentSum[𝔹, (b ∶ 𝔹) ↦ b ≡ b] -->

## Applications

A point of a fiber is a pair: `"true"` with a path from `"not"["true"]` to `"false"`, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

`"not"["true"]` computes to `"false"`, so the constant path will do:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[DependentPair["true", Function[{i}, "false"]], Fiber["not", "false"]], cubical]]
```

<!-- => DependentSum[𝔹, (x ∶ 𝔹) ↦ !x ≡ false] -->

## Properties and Relations

A pair is made of its fields: by eta for structures, the pair of the two fields of *p* is *p*, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The pair rebuilt from the fields, against *p* itself:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[p, DependentSum[Booleans, Function[{Typed[b, Booleans]}, Booleans]]]}, Typed[DependentPair[p[[1]], p[[2]]], DependentSum[Booleans, Function[{Typed[b, Booleans]}, Booleans]]]], cubical],
    TypeTheoryTerm[Function[{Typed[p, DependentSum[Booleans, Function[{Typed[b, Booleans]}, Booleans]]]}, p], cubical]
]
```

<!-- => True -->

## Possible Issues

Without the type expected, the family *B* is unknown, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The pair alone does not say which family the type of its second element comes from:

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentPair["true", "false"], cubical]]
```

<!-- => Failure["TypeMismatch", ...] -->
