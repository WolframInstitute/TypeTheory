---
Template: Symbol
Name: IntegerMultiplicationOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerMultiplicationOne
Keywords: [integers, multiplication, one, identity, theorem, Lean]
SeeAlso: [IntegerAdditionZero, MultiplicationOneRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerMultiplicationOne]()[*x*]</code> proves <code>*x* * 1 == *x*</code> for an integer *x*.

## Details & Options

- [IntegerMultiplicationOne]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.mul_one`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerMultiplicationOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationOne, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x 1 == x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationOne[-7], TypeTheoryEnvironment["Integers"]]]
```

<!-- => (-7) 1 == -7 -->

## Scope

An instance with a sum:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[y, Integers]}, IntegerMultiplicationOne[x + y]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ (x + y) 1 == x + y -->

## Applications

`"Rewrite"` removes a factor 1 inside a sum:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x 1 + y == x + y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationOne]
}]
```

<!-- => Proof complete -->

## Properties and Relations

One on the left follows with [IntegerMultiplicationCommutativity]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, 1 x == x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationCommutativity],
    TypeTheoryTactic["Exact", IntegerMultiplicationOne[x]]
}]
```

<!-- => Proof complete -->

## Possible Issues

For an integer variable `x 1 == x` does not hold by computation, so `"Reflexivity"` does not prove it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x 1 == x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
