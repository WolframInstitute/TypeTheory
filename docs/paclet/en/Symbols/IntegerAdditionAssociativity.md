---
Template: Symbol
Name: IntegerAdditionAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionAssociativity
Keywords: [integers, addition, associativity, theorem, Lean]
SeeAlso: [IntegerAdditionCommutativity, IntegerMultiplicationAssociativity, AdditionAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionAssociativity]()[*x*, *y*, *z*]</code> proves <code>(*x* + *y*) + *z* == *x* + (*y* + *z*)</code> for integers.

## Details & Options

- [IntegerAdditionAssociativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_assoc`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionAssociativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x + y + z == x + (y + z) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionAssociativity[1, -2, 3], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 1 + -2 + 3 == 1 + (-2 + 3) -->

## Scope

`"Rewrite"` with `"RightToLeft"` regroups a sum the other way:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x + (y + z) == (x + y) + z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity, "RightToLeft"]
}]
```

<!-- => Proof complete -->

## Applications

Each `"Rewrite"` regroups one sum, the innermost first, so three of them regroup a sum of four terms:

```wl
TypeTheoryProof[ForAll[{Typed[w, Integers], Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, ((w + x) + y) + z == w + (x + (y + z))], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", w, x, y, z],
    TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity],
    TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity],
    TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [IntegerEqualityDecidable]() decides equations of integers:

```wl
TypeTheoryProof[Typed[(1 + -2) + 3, Integers] == 1 + (-2 + 3), TypeTheoryEnvironment["Integers"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

`"Exact"` needs the grouping of the law, so it fails on a statement grouped the other way:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x + (y + z) == (x + y) + z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Exact", IntegerAdditionAssociativity[x, y, z]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

[EqualitySymmetry]() turns the law around:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x + (y + z) == (x + y) + z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Exact", EqualitySymmetry[IntegerAdditionAssociativity[x, y, z]]]
}]
```

<!-- => Proof complete -->
