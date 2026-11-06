---
Template: Symbol
Name: QuotientInduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientInduction
Keywords: [quotient, induction, classes, Quot.ind, Lean, prelude, integers, Induction tactic, proof by representatives]
SeeAlso: [QuotientType, QuotientIntroduction, QuotientLift, TypeTheoryQuotients, TypeTheoryProof, Construct]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation, TheIntegers]
---

## Usage

<code>[QuotientInduction]()[*premise*, *q*]</code> proves *P*[*q*] for the class *q* from a proof *premise* of <code>*P*[[QuotientIntroduction]()[*r*, *a*]]</code> for every *a*.

## Details & Options

- [QuotientInduction]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude, as Lean's `Quot.ind`.
- The type α, the relation *r* and the property *P*, a proposition about classes, are implicit arguments. *P* is found from the expected type, as the goal of a proof or a type [Typed]() gives, and not from the premise alone; <code>[Construct]()[[QuotientInduction](), α, *r*, *P*, *premise*]</code> gives it explicitly.
- *P* is a proposition: a property of every class needs no proof that it respects *r*, since any two proofs of a proposition are equal. A function into data comes from [QuotientLift]() instead, with such a proof.
- It computes on a class: <code>[QuotientInduction]()[*premise*, [QuotientIntroduction]()[*r*, *a*]]</code> is *premise*[*a*].
- The tactic `"Induction"` on a variable of a quotient type uses it: the goal becomes a proposition about the class of an element, the case `QuotientIntroduction`. On a type of data it fails with `"QuotientEliminationIntoData"`.
- With the integers, induction on a class and `"quotientSoundness"` reduce a law of integers to an equation of natural numbers, which is how the library proves the laws of a commutative ring.

## Basic Examples

The type of [QuotientInduction]():

```wl
TypeTheoryType[QuotientInduction]
```

<!-- => ∀_{α ∶ Sort u} ∀_{r ∶ α → α → Prop} ∀_{β ∶ QuotientType[r] → Prop} (∀_a∶α β[QuotientIntroduction[r, a]]) ⇒ ∀_q∶QuotientType[r] β[q] -->

---

To prove that negating an integer twice gives it back, it is enough to prove it for the class of every pair:

```wl
TypeTheoryProof[ForAll[{Typed[q, Integers]}, -(-q) == q], "Integers", {"Apply"[QuotientInduction]}]
```

<!-- => Proof, 1 goal: ⊢ ∀_a∶ℕ × ℕ -(-(QuotientIntroduction[integerRelation, a])) == QuotientIntroduction[integerRelation, a] -->

On a class negation computes, swapping the pair twice, so reflexivity proves it:

```wl
TypeTheoryProof[ForAll[{Typed[q, Integers]}, -(-q) == q], "Integers", {"Apply"[QuotientInduction], "Introduce"[a], "Reflexivity"}]
```

<!-- => Proof complete -->

---

The same proof as a term, where the statement it is [Typed]() with gives *P*:

```wl
TypeTheoryType[Typed[
    QuotientInduction[Typed[p, CartesianProductType[Naturals, Naturals]] |-> "equalityReflexivity"[QuotientIntroduction["integerRelation", p]]],
    ForAll[{Typed[q, Integers]}, -(-q) == q]
], "Integers"]
```

<!-- => ∀_q∶ℤ -(-q) == q -->

## Scope

[Construct]() gives the implicit arguments, *P* among them. Adding 0 to every integer leaves it: the class of (a, b) plus 0 computes to the class of (a + 0, b + 0), which is related to (a, b) by computation:

```wl
TypeTheoryType[Construct[QuotientInduction,
    CartesianProductType[Naturals, Naturals],
    "integerRelation",
    Typed[x, Integers] |-> x + 0 == x,
    Typed[p, CartesianProductType[Naturals, Naturals]] |-> "quotientSoundness"["equalityReflexivity"[p[[1]] + p[[2]]]]
], "Integers"]
```

<!-- => ∀_q∶QuotientType[integerRelation] q + 0 == q -->

---

The tactic `"Induction"` on an integer gives the goal for the class of a pair, as the case `QuotientIntroduction`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, -(-x) == x], "Integers", {"Introduce"[x], "Induction"[x]}]
```

<!-- => Proof, 1 goal: case QuotientIntroduction ⊢ ∀_a∶ℕ × ℕ -(-(QuotientIntroduction[integerRelation, a])) == QuotientIntroduction[integerRelation, a] -->

## Applications

Multiplication of integers is commutative. Induction on both classes gives two pairs, `"quotientSoundness"` the relation of their products, an equation of natural numbers, and `"Ring"` proves it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], "Integers", {
    "Introduce"[x, y],
    "Induction"[x], "Introduce"[p],
    "Induction"[y], "Introduce"[q],
    "Apply"["quotientSoundness"],
    "Ring"
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"Induction"` on a class builds a [QuotientInduction]() into the proof:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, Integers]}, -(-x) == x], "Integers", {"Introduce"[x], "Induction"[x], "Introduce"[p], "Reflexivity"}]
```

<!-- => Proof complete -->

Its term:

```wl
proof["Term"]
```

<!-- => (x ∶ ℤ) ↦ QuotientInduction[(p ∶ ℕ × ℕ) ↦ equalityReflexivity[-(-(QuotientIntroduction[integerRelation, p]))], x] -->

---

On a class, [QuotientInduction]() computes to the premise at its element:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Construct[QuotientInduction,
    CartesianProductType[Naturals, Naturals],
    "integerRelation",
    Typed[x, Integers] |-> -(-x) == x,
    Typed[p, CartesianProductType[Naturals, Naturals]] |-> "equalityReflexivity"[QuotientIntroduction["integerRelation", p]],
    QuotientIntroduction["integerRelation", "pair"[2, 5]]
], "Integers"]]
```

<!-- => equalityReflexivity[QuotientIntroduction[integerRelation, (2, 5)]] -->

## Possible Issues

The premise alone does not say what *P* is, since a class of a variable is no variable to abstract; [Typed]() or [Construct]() gives it:

```wl
TypeTheoryType[QuotientInduction[Typed[p, CartesianProductType[Naturals, Naturals]] |-> "equalityReflexivity"[QuotientIntroduction["integerRelation", p]], Typed[2 - 5, Integers]], "Integers"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

*P* must be a proposition. A family of types, as for a function into data, is refused:

```wl
TypeTheoryType[Construct[QuotientInduction,
    CartesianProductType[Naturals, Naturals],
    "integerRelation",
    Typed[x, Integers] |-> Naturals,
    Typed[p, CartesianProductType[Naturals, Naturals]] |-> p[[1]]
], "Integers"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

So `"Induction"` on an integer refuses a goal of data; a function from the integers is lifted from pairs with [QuotientLift]():

```wl
TypeTheoryProof[TypeSpecifier[{Integers} -> Naturals], "Integers", {"Introduce"[x], "Induction"[x]}]
```

<!-- => Failure["QuotientEliminationIntoData", ...] -->
