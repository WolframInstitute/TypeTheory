---
Template: Symbol
Name: NaturalNumberSuccessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NaturalNumberSuccessor
Keywords: [natural numbers, successor, constructor, literal, prelude]
SeeAlso: [NaturalNumberZero, TypeTheoryNaturalNumbers, DefinitionallyEqualQ, WeakHeadNormalForm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[NaturalNumberSuccessor]()[*n*]</code> is the natural number after *n*.

## Details & Options

- [NonNegativeIntegers]() is the inductive type of natural numbers in the prelude, and [NaturalNumberZero]() and [NaturalNumberSuccessor]() are its constructors.
- The prelude registers them with [TypeTheoryNaturalNumbers](), so a literal `n + 1` is <code>[NaturalNumberSuccessor]()[*n*]</code> by computation.

## Basic Examples

The type of [NaturalNumberSuccessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NaturalNumberSuccessor]]
```

<!-- => ℕ → ℕ -->

---

The successor of `41` is `42`:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[41]], TypeTheoryTerm[42]]
```

<!-- => True -->

## Scope

Adding one is taking the successor, since addition recurses on its second argument:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + 1]],
    TypeTheoryTerm[NaturalNumberSuccessor]
]
```

<!-- => True -->

## Properties and Relations

A constructor applied to an argument is already in weak head normal form:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberSuccessor[41]]]
```

<!-- => 41 + 1 -->
