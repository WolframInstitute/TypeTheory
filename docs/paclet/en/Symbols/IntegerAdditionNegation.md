---
Template: Symbol
Name: IntegerAdditionNegation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionNegation
Keywords: [integers, addition, negation, inverse, theorem, Lean]
SeeAlso: [IntegerAdditionZero, IntegerSubtractionNegation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionNegation]()[*x*]</code> proves <code>*x* + -*x* == 0</code> for an integer *x*.

## Details & Options

- [IntegerAdditionNegation]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_right_neg`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionNegation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionNegation, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x + -x == 0 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionNegation[4], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 4 + -4 == 0 -->

## Scope

An instance with a product, `x y`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[y, Integers]}, IntegerAdditionNegation[x y]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x y + -(x y) == 0 -->

## Applications

The negation on the left follows with [IntegerAdditionCommutativity]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, -x + x == 0], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Rewrite", IntegerAdditionCommutativity],
    TypeTheoryTactic["Exact", IntegerAdditionNegation[x]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`x - x` is `x + -x` by computation, so the law proves `x - x == 0` as it stands:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x - x == 0], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Exact", IntegerAdditionNegation[x]]
}]
```

<!-- => Proof complete -->

---

`4 + -4` and `0` are the classes of two different pairs, (4, 4) and (0, 0), so they are not equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[4 + -4, Integers], TypeTheoryEnvironment["Integers"]], TypeTheoryTerm[Typed[0, Integers], TypeTheoryEnvironment["Integers"]]]
```

<!-- => False -->

`"Decide"` proves them equal:

```wl
TypeTheoryProof[Typed[4 + -4, Integers] == 0, TypeTheoryEnvironment["Integers"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
