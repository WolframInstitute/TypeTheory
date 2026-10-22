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
- Definitions unfold as in Lean's kernel, one at a time: of two applications of different definitions, the higher definition unfolds first, the one defined in terms of the other, whose height is greater, and the two are compared again, so two applications of the same definition are compared by their arguments before either computes. A definition's height is one more than the greatest height of the definitions its value mentions.
- A term without an environment takes the other's.
- A term that does not type-check is not equal to anything: [DefinitionallyEqualQ]() gives [False]().

## Basic Examples

Literals compute:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[2 + 3], TypeTheoryTerm[5]]
```

<!-- => True -->

```wl
DefinitionallyEqualQ[TypeTheoryTerm[2 + 3], TypeTheoryTerm[6]]
```

<!-- => False -->

## Scope

A literal is its constructor form:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberSuccessor[NaturalNumberZero]]], TypeTheoryTerm[2]]
```

<!-- => True -->

---

Eta: a function equals the function that applies it:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[n, Naturals]}, NaturalNumberSuccessor[n]]],
    TypeTheoryTerm[NaturalNumberSuccessor]
]
```

<!-- => True -->

---

The parity of a natural number by recursion, and a definition by it:

```wl
parity = TypeTheoryEnvironment[{
    TypeTheoryDefinition[Parity, Function[{Typed[n, Naturals]},
        InductiveRecursor[Naturals][Function[{Typed[t, Naturals]}, Booleans], "true", Function[{Typed[k, Naturals], Typed[r, Booleans]}, "not"[r]], n]
    ]],
    TypeTheoryDefinition[ParityAgain, Function[{Typed[n, Naturals]}, Parity[n]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 171 constants -->

`ParityAgain` is higher than `Parity`, so it unfolds first, and the recursion 100000 steps deep that `Parity[100000]` computes is not needed:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[ParityAgain[100000], parity], TypeTheoryTerm[Parity[100000], parity]]
```

<!-- => True -->

## Properties and Relations

`n + 0` computes to `n`, because addition recurses on its second argument; `0 + n` does not:

```wl
{
    DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n + 0]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, n]]],
    DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, 0 + n]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, n]]]
}
```

<!-- => {True, False} -->
