---
Template: Symbol
Name: NaturalNumberZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NaturalNumberZero
Keywords: [natural numbers, zero, constructor, literal, prelude]
SeeAlso: [NaturalNumberSuccessor, TypeTheoryNaturalNumbers, DefinitionallyEqualQ]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[NaturalNumberZero]()</code> is the natural number zero, written `0`.

## Details & Options

- [NonNegativeIntegers]() is the inductive type of natural numbers in the prelude, and [NaturalNumberZero]() and [NaturalNumberSuccessor]() are its constructors.
- The prelude registers them with [TypeTheoryNaturalNumbers](), so the literal `0` is [NaturalNumberZero]() by computation, and `n` is [NaturalNumberSuccessor]() applied `n` times.

## Basic Examples

[NaturalNumberZero]() is a natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[NaturalNumberZero]]
```

<!-- => ℕ -->

---

It is the literal `0`:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberZero], TypeTheoryTerm[0]]
```

<!-- => True -->
