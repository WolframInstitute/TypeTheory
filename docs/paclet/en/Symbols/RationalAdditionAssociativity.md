---
Template: Symbol
Name: RationalAdditionAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalAdditionAssociativity
Keywords: [rationals, addition, associativity, theorem, Lean]
SeeAlso: [RationalAdditionCommutativity, RationalMultiplicationAssociativity, IntegerAdditionAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalAdditionAssociativity]()[*x*, *y*, *z*]</code> proves <code>(*x* + *y*) + *z* == *x* + (*y* + *z*)</code> for rationals *x*, *y* and *z*.

## Details & Options

- [RationalAdditionAssociativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.add_assoc`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalAdditionAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionAssociativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ ∀_z∶ℚ x + y + z == x + (y + z) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionAssociativity[1/2, 1/3, 1/6], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 1/2 + 1/3 + 1/6 == 1/2 + (1/3 + 1/6) -->

## Scope

An instance with fractions of a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals]}, RationalAdditionAssociativity[x, x / 2, x / 3]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x + x/2 + x/3 == x + (x/2 + x/3) -->

## Applications

`"Rewrite"` with `"RightToLeft"` regroups a sum the other way:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, x + (y + z) == (x + y) + z], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Rewrite", RationalAdditionAssociativity, "RightToLeft"]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"Ring"` proves an identity that regroups a sum and adds its fractions:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, (x + 1/2) + 1/2 == x + 1], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

## Possible Issues

For rational variables the two sides are not equal by computation, so `"Reflexivity"` does not prove the law:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x + y) + z == x + (y + z)], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
