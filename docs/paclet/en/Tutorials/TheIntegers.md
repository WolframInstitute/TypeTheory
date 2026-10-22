---
Template: TechNote
Name: TheIntegers
Title: The Integers
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TheIntegers
Keywords: [integers, quotient, quotient type, commutative ring, coercion, induction, Ring, Lean]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions, RulesAndComputation]
---

The integers are not in the prelude; <code>[TypeTheoryEnvironment]()["Integers"]</code> adds them, built and checked the first time it is asked for. An integer there is a class of pairs of natural numbers: (a, b) stands for a - b, and two pairs (a, b) and (c, d) are the same integer when a + d == c + b. That is a quotient type, the way many textbooks build the integers; Lean's `Int` is an inductive type instead. Every operation is lifted from pairs, and every law of a commutative ring is proved by TypeTheory's own tactics, then checked by the kernel.

## The Integers as a Quotient

The environment, the prelude with the integers:

```wl
integers = TypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 200 constants -->

[Integers]() is the quotient of pairs by a relation, and shows as ℤ:

```wl
integers[Integers]
```

<!-- => definition ℤ : Type := QuotientType[integerRelation] -->

The relation:

```wl
integers["integerRelation"]
```

<!-- => definition integerRelation : CartesianProduct[ℕ, ℕ] → CartesianProduct[ℕ, ℕ] → Prop := (p ∶ CartesianProduct[ℕ, ℕ]) (q ∶ CartesianProduct[ℕ, ℕ]) ↦ p〚1〛 + q〚2〛 == q〚1〛 + p〚2〛 -->

A natural number n is the class of (n, 0), and the function that takes it there is a coercion, inserted where a natural number stands for an integer:

```wl
integers["integerOfNatural"]
```

<!-- => coercion integerOfNatural : ℕ → ℤ := (n ∶ ℕ) ↦ integerOfPair[Pair[n, 0]] -->

## Arithmetic

In this environment `+`, `*`, `-`, the comparisons and negative literals are the integers' wherever the types say so, and the natural numbers' otherwise, as in Lean:

```wl
TypeTheoryTerm[Function[{Typed[x, Integers], Typed[n, Naturals]}, 2 x - 7 <= x + n], integers]
```

<!-- => (x ∶ ℤ) (n ∶ ℕ) ↦ 2 x - 7 ≤ x + n -->

Its type; the natural number `n` is coerced to an integer where it is added to one:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[n, Naturals]}, 2 x - 7 <= x + n], integers]]
```

<!-- => ℤ → ℕ → Prop -->

Numbers alone are natural numbers, unless an integer is expected:

```wl
{TypeOf[TypeTheoryTerm[2 + 3, integers]], TypeOf[TypeTheoryTerm[Typed[2 + 3, Integers], integers]]}
```

<!-- => {ℕ, ℤ} -->

## Equations of Integers

Two pairs with the same difference are two representatives of one integer. They are not equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[2 - 5, Integers], integers], TypeTheoryTerm[Typed[-3, Integers], integers]]
```

<!-- => False -->

They are equal by [QuotientSoundness](): `2 - 5` is the class of (2, 5) and `-3` that of (0, 3), and 2 + 3 and 0 + 5 both compute to 5:

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientSoundness[EqualityReflexivity[5]], integers], TypeTheoryTerm[Typed[2 - 5, Integers] == -3, integers]]
```

<!-- => Success["TypeChecked", ...] -->

## The Laws

The laws of a commutative ring are theorems, such as [IntegerDistributivity]():

```wl
integers[IntegerDistributivity]
```

<!-- => theorem IntegerDistributivity : ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x (y + z) == x y + x z -->

They rewrite integer terms as the laws of the natural numbers rewrite theirs. A difference is a sum with the negation, [IntegerSubtractionNegation](); then associativity, the inverse and zero finish the proof:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + y) - y == x], integers, {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", IntegerSubtractionNegation],
    TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity],
    TypeTheoryTactic["Rewrite", IntegerAdditionNegation],
    TypeTheoryTactic["Rewrite", IntegerAdditionZero]
}]
```

<!-- => Proof complete -->

## Proving a Law

The library proves each law the same way, and so can you. `"Induction"` on an integer, a class, gives a goal for the class of a pair:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], integers, {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
    TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q]
}]
```

<!-- => Proof, 1 goal: p ∶ CartesianProduct[ℕ, ℕ], q ∶ CartesianProduct[ℕ, ℕ] ⊢ QuotientIntroduction[integerRelation, p] QuotientIntroduction[integerRelation, q] == QuotientIntroduction[integerRelation, q] QuotientIntroduction[integerRelation, p] -->

The product of two classes computes to the class of a pair, so [QuotientSoundness]() leaves the relation of two pairs, an equation of natural numbers:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], integers, {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
    TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
    TypeTheoryTactic["Apply", QuotientSoundness]
}]
```

<!-- => Proof, 1 goal: p ∶ CartesianProduct[ℕ, ℕ], q ∶ CartesianProduct[ℕ, ℕ] ⊢ integerRelation[Pair[p〚1〛 q〚1〛 + p〚2〛 q〚2〛, p〚1〛 q〚2〛 + p〚2〛 q〚1〛], Pair[q〚1〛 p〚1〛 + q〚2〛 p〚2〛, q〚1〛 p〚2〛 + q〚2〛 p〚1〛]] -->

`"Ring"` proves it, taking the fields of the pairs as atoms:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], integers, {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
    TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
    TypeTheoryTactic["Apply", QuotientSoundness],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

Induction on a class proves propositions only. A function into data, such as negation, is lifted from pairs with [QuotientLift](), given a proof that it respects the relation, which `"LinearArithmetic"` and `"PolynomialReduce"` prove for the library's operations.
