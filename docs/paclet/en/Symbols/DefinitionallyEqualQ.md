---
Template: Symbol
Name: DefinitionallyEqualQ
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DefinitionallyEqualQ
Keywords: [definitional equality, conversion, computation, reduction, beta, eta, proof irrelevance, unfolding, definition height]
SeeAlso: [WeakHeadNormalForm, NormalForm, TypeTheoryCheck, TypeTheoryTerm, TypeTheoryDefinition]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[DefinitionallyEqualQ]()[*term1*, *term2*]</code> gives [True]() if the [TypeTheoryTerm]() expressions *term1* and *term2* are equal by computation in their environment, and [False]() otherwise.

## Details & Options

- Two terms are definitionally equal when they reduce to the same term: a function applied to an argument computes (beta), a recursor applied to a constructor computes, a definition unfolds to its value, and literals compute with the operations of the natural numbers. They are equal up to the names of bound variables, up to eta for functions and for structures, and when they are proofs of the same proposition (proof irrelevance).
- Definitions unfold as in Lean's kernel, one at a time: of two applications of different definitions, the higher definition unfolds first, the one defined in terms of the other, whose height is greater, and the two are compared again, so two applications of the same definition are compared by their arguments before either computes. A definition's height is one more than the greatest height of the definitions its value mentions.
- A term without an environment takes the other's, and two without one are in the default environment, the prelude.
- The kernel checks each term before they are compared. A term that does not type-check is not equal to anything, and neither are two terms that carry different environments: [DefinitionallyEqualQ]() gives [False]().
- Equality by computation is decidable but not every equation that holds is one: `0 + n == n` holds for every natural number `n`, by induction, and `0 + n` does not compute to `n`.
- [DefinitionallyEqualQ]() does not hold its arguments; each is a [TypeTheoryTerm]().

## Basic Examples

Literals compute:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[2 + 3], TypeTheoryTerm[5]]
```

<!-- => True -->

---

The Booleans compute:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["not"["true"]], TypeTheoryTerm["false"]]
```

<!-- => True -->

---

Beta: a function applied to an argument computes:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[(Typed[n, Naturals] |-> n + 1)[2]], TypeTheoryTerm[3]]
```

<!-- => True -->

## Scope

A literal is its constructor form:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["successor"["successor"["zero"]]], TypeTheoryTerm[2]]
```

<!-- => True -->

---

Eta: a function equals the function that applies it:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Typed[n, Naturals] |-> "successor"[n]],
    TypeTheoryTerm["successor"]
]
```

<!-- => True -->

---

The names of bound variables do not matter:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[a, Naturals] |-> a], TypeTheoryTerm[Typed[b, Naturals] |-> b]]
```

<!-- => True -->

---

Eta for structures: a pair equals the pair of its fields:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Typed[p, CartesianProductType[Naturals, Naturals]] |-> p],
    TypeTheoryTerm[Typed[p, CartesianProductType[Naturals, Naturals]] |-> Construct["pair", Naturals, Naturals, p[[1]], p[[2]]]]
]
```

<!-- => True -->

---

Proof irrelevance: two proofs of the same proposition are equal:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm["equalitySymmetry"["equalityReflexivity"[4]]]]
```

<!-- => True -->

---

A local definition computes:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[With[{square = Typed[n, Naturals] |-> n n}, square[3] + square[4]]], TypeTheoryTerm[25]]
```

<!-- => True -->

---

A list literal is the list built with [Prepend]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[{1, 2}], TypeTheoryTerm[Prepend[{2}, 1]]]
```

<!-- => True -->

---

`n + 0` computes to `n` for a variable `n`, because addition recurses on its second argument:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0], TypeTheoryTerm[Typed[n, Naturals] |-> n]]
```

<!-- => True -->

---

A definition of doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Typed[n, Naturals] |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The constant unfolds to its value:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Double, doubled], TypeTheoryTerm[Typed[n, Naturals] |-> n + n]]
```

<!-- => True -->

---

A type of bits, and flipping a bit by its recursor:

```wl
bits = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryDefinition[Flip, Typed[b, Bit] |-> InductiveRecursor[Bit][Typed[t, Bit] |-> Bit, BitOne, BitZero, b]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 262 constants -->

Flipping twice gives the bit back; the term without an environment takes the other's:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Flip[Flip[BitOne]], bits], TypeTheoryTerm[BitOne]]
```

<!-- => True -->

Flipping once does not:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Flip[BitOne], bits], TypeTheoryTerm[BitOne]]
```

<!-- => False -->

---

The head of an expression computes, as the prelude declares the Wolfram Language's expressions:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Head[f[1]]], TypeTheoryTerm[HoldForm[f]]]
```

<!-- => True -->

---

The parity of a natural number by recursion, and a definition by it:

```wl
parity = TypeTheoryEnvironment[{
    TypeTheoryDefinition[Parity, Function[{Typed[n, Naturals]},
        InductiveRecursor[Naturals][Typed[t, Naturals] |-> Booleans, "true", {Typed[k, Naturals], Typed[r, Booleans]} |-> "not"[r], n]
    ]],
    TypeTheoryDefinition[ParityAgain, Typed[n, Naturals] |-> Parity[n]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The recursion computes, seven steps to `"false"`:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Parity[7], parity], TypeTheoryTerm["false", parity]]
```

<!-- => True -->

`ParityAgain` is higher than `Parity`, so it unfolds first, and the recursion 100000 steps deep that `Parity[100000]` computes is not needed:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[ParityAgain[100000], parity], TypeTheoryTerm[Parity[100000], parity]]
```

<!-- => True -->

## Properties and Relations

Two terms are definitionally equal when their normal forms are the same; [NormalForm]() computes one:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n -->

---

A proof by reflexivity of an equation checks exactly when its sides are definitionally equal:

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[6]], TypeTheoryTerm[2 * 3 == 3 + 3]]
```

<!-- => Success["TypeChecked", ...] -->

---

So the tactic `"Decide"` proves it:

```wl
TypeTheoryProof[2 * 3 == 3 + 3, {"Decide"}]
```

<!-- => Proof complete -->

## Possible Issues

`0 + n == n` holds for every natural number, by induction, but `0 + n` does not compute: the recursion of addition is on its second argument, a variable here:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, Naturals] |-> 0 + n], TypeTheoryTerm[Typed[n, Naturals] |-> n]]
```

<!-- => False -->

---

A definition of doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Typed[n, Naturals] |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

`k + k` and `2 k` are equal for every `k`, but neither computes for a variable:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[k, Naturals] |-> Double[k], doubled], TypeTheoryTerm[Typed[k, Naturals] |-> 2 k]]
```

<!-- => False -->

---

Terms of different types are not equal:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[0], TypeTheoryTerm["false"]]
```

<!-- => False -->

---

A term that does not type-check is not equal to anything, itself included:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[1 + True], TypeTheoryTerm[1 + True]]
```

<!-- => False -->

---

Terms in different environments are not equal, even the same literal:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[2, "Integers"], TypeTheoryTerm[2, "Rationals"]]
```

<!-- => False -->

---

The arguments are evaluated, so expressions that are not in [TypeTheoryTerm]() compute first, and nothing matches:

```wl
DefinitionallyEqualQ[2 + 3, 5]
```

<!-- => DefinitionallyEqualQ[5, 5] -->
