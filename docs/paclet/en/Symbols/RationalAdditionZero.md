---
Template: Symbol
Name: RationalAdditionZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalAdditionZero
Keywords: [rationals, addition, zero, identity, theorem, Lean]
SeeAlso: [RationalAdditionNegation, RationalMultiplicationOne, IntegerAdditionZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalAdditionZero]()[*x*]</code> proves <code>*x* + 0 == *x*</code> for a rational *x*.

## Details & Options

- [RationalAdditionZero]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.add_zero`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalAdditionZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionZero, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x + 0 == x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionZero[2/3], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 2/3 + 0 == 2/3 -->

## Scope

An instance with a fraction of a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals]}, RationalAdditionZero[x / 2]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x/2 + 0 == x/2 -->

## Applications

Zero on the left follows with [RationalAdditionCommutativity]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, 0 + x == x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Rewrite", RationalAdditionCommutativity],
    TypeTheoryTactic["Exact", RationalAdditionZero[x]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [RationalEqualityDecidable]() decides equations of rationals:

```wl
TypeTheoryProof[Typed[2/3 + 0, Rationals] == 2/3, TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

For a rational variable `x + 0 == x` does not hold by computation, so `"Reflexivity"` does not prove it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, x + 0 == x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
