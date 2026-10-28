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

## Scope

The recursor of [NonNegativeIntegers]() computes at it, and gives its value for 0:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Naturals][Function[{Typed[t, Naturals]}, Naturals], 7, Function[{Typed[k, Naturals], Typed[r, Naturals]}, r + 2], NaturalNumberZero]]]
```

<!-- => 7 -->

## Properties and Relations

Its successor is the literal 1:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberZero]], TypeTheoryTerm[1]]
```

<!-- => True -->

---

The prelude registers it as the zero of its natural numbers:

```wl
Information[TypeTheoryEnvironment["Prelude"], "NaturalNumbers"]["Zero"]
```

<!-- => NaturalNumberZero -->

## Possible Issues

The literal 0 is [NaturalNumberZero]() only in an environment with natural numbers, so in the empty environment it does not check:

```wl
TypeTheoryCheck[TypeTheoryTerm[0, TypeTheoryEnvironment[]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
