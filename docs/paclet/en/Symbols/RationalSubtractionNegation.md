---
Template: Symbol
Name: RationalSubtractionNegation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalSubtractionNegation
Keywords: [rationals, subtraction, negation, theorem, Lean]
SeeAlso: [RationalAdditionNegation, RationalAdditionZero, IntegerSubtractionNegation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalSubtractionNegation]()[*x*, *y*]</code> proves <code>*x* - *y* == *x* + -*y*</code> for rationals *x* and *y*.

## Details & Options

- [RationalSubtractionNegation]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- `x - y` is defined as `x + -y`, so the law holds by computation, as Lean's `Rat.sub_eq_add_neg`. `"Rewrite"` with it turns a difference into a sum, to which the laws of addition apply.
- It is proved by `"Reflexivity"`.

## Basic Examples

The statement of [RationalSubtractionNegation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalSubtractionNegation, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ x - y == x + -y -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalSubtractionNegation[1/2, 1/3], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 1/2 - 1/3 == 1/2 + -(1/3) -->

## Scope

An instance with a fraction:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals]}, RationalSubtractionNegation[x, 1/2]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x - 1/2 == x + -(1/2) -->

## Applications

`"Rewrite"` with the law turns a difference into a sum, and the laws of addition then prove `(x - y) + y == x`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, (x - y) + y == x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", RationalSubtractionNegation],
    TypeTheoryTactic["Rewrite", RationalAdditionAssociativity],
    TypeTheoryTactic["Rewrite", RationalAdditionCommutativity[-y, y]],
    TypeTheoryTactic["Rewrite", RationalAdditionNegation],
    TypeTheoryTactic["Rewrite", RationalAdditionZero]
}]
```

<!-- => Proof complete -->

## Properties and Relations

A difference of literals computes to a rational, which can be negative, and `"Decide"` proves its value:

```wl
TypeTheoryProof[Typed[1/3 - 1/2, Rationals] == -1/6, TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

Wolfram Language reads `x + -y` as `x - y`, so a statement of the law written that way has the same two sides:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x - y == x + -y], TypeTheoryEnvironment["Rationals"]]
```

<!-- => Proof, 1 goal: ⊢ ∀_x∶ℚ ∀_y∶ℚ x - y == x - y -->

Wrapping the negation in [Typed]() keeps it a negation, and `"Reflexivity"` proves the law, which holds by computation:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x - y == x + Typed[-y, Rationals]], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->
