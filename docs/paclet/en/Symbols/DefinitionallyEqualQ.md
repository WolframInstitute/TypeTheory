---
Template: Symbol
Name: DefinitionallyEqualQ
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DefinitionallyEqualQ
Keywords: [definitional equality, conversion, computation, reduction, eta, proof irrelevance]
SeeAlso: [WeakHeadNormalForm, TypeTheoryCheck, TypeTheoryTerm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[DefinitionallyEqualQ]()[*term1*, *term2*]</code> gives [True]() if the [TypeTheoryTerm]() expressions *term1* and *term2* are equal by computation in their environment, and [False]() otherwise.

## Details & Options

- Two terms are definitionally equal when they reduce to the same term, up to eta for functions and for structures, and when they are proofs of the same proposition (proof irrelevance).
- A term without an environment takes the other's.
- A term that does not type-check is not equal to anything: [DefinitionallyEqualQ]() gives [False]().

## Basic Examples

Literals compute:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
DefinitionallyEqualQ[TypeTheoryTerm[2 + 3, prelude], TypeTheoryTerm[5]]
```

<!-- => True -->

```wl
DefinitionallyEqualQ[TypeTheoryTerm[2 + 3, prelude], TypeTheoryTerm[6]]
```

<!-- => False -->

## Scope

A literal is its constructor form:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberSuccessor[NaturalNumberZero]], TypeTheoryEnvironment["Prelude"]], TypeTheoryTerm[2]]
```

<!-- => True -->

---

Eta: a function equals the function that applies it:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, NaturalNumberSuccessor[n]], TypeTheoryEnvironment["Prelude"]],
    TypeTheoryTerm[NaturalNumberSuccessor]
]
```

<!-- => True -->

## Properties and Relations

`n + 0` computes to `n`, because addition recurses on its second argument; `0 + n` does not:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
{
    DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + 0], prelude], TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n]]],
    DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, 0 + n], prelude], TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n]]]
}
```

<!-- => {True, False} -->
