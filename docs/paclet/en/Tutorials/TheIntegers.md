---
Template: TechNote
Name: TheIntegers
Title: The Integers
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TheIntegers
Keywords: [integers, quotient, quotient type, commutative ring, coercion, induction, Ring, inequality, sum of squares, SumOfSquares]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions, RulesAndComputation]
---

The integers are not in the prelude; <code>[TypeTheoryEnvironment]()["Integers"]</code> adds them, read from the file saved with the paclet the first time it is asked for. An integer there is a class of pairs of natural numbers: (a, b) stands for a - b, and two pairs (a, b) and (c, d) are the same integer when a + d == c + b. That is a quotient type, the way many textbooks build the integers. Every operation is lifted from pairs, and every law of a commutative ring is proved by TypeTheory's own tactics, then checked by the kernel.

## The Integers as a Quotient

The environment, the prelude with the integers:

```wl
integers = TypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 356 constants -->

[Integers]() is the quotient of pairs by a relation, and shows as ℤ:

```wl
integers[Integers]
```

<!-- => definition ℤ : Type := QuotientType[integerRelation] -->

The relation:

```wl
integers["integerRelation"]
```

<!-- => definition integerRelation : ℕ × ℕ → ℕ × ℕ → Prop := (p ∶ ℕ × ℕ) (q ∶ ℕ × ℕ) ↦ p〚"first"〛 + q〚"second"〛 == q〚"first"〛 + p〚"second"〛 -->

A natural number n is the class of (n, 0), and the function that takes it there is a coercion, inserted where a natural number stands for an integer:

```wl
integers["integerOfNatural"]
```

<!-- => coercion integerOfNatural : ℕ → ℤ := (n ∶ ℕ) ↦ integerOfPair[(n, 0)] -->

## Arithmetic

In this environment `+`, `*`, `-`, `^` with a natural number exponent, the comparisons and negative literals are the integers' wherever the types say so, and the natural numbers' otherwise:

```wl
TypeTheoryTerm[{Typed[x, Integers], Typed[n, Naturals]} |-> 2 x - 7 <= x + n, integers]
```

<!-- => (x ∶ ℤ) (n ∶ ℕ) ↦ 2 x - 7 ≤ x + n -->

Its type; the natural number `n` is coerced to an integer where it is added to one:

```wl
TypeTheoryType[{Typed[x, Integers], Typed[n, Naturals]} |-> 2 x - 7 <= x + n, integers]
```

<!-- => ℤ → ℕ → Prop -->

Numbers alone are natural numbers, unless an integer is expected:

```wl
{TypeTheoryType[2 + 3, integers], TypeTheoryType[Typed[2 + 3, Integers], integers]}
```

<!-- => {ℕ, ℤ} -->

## Equations of Integers

Two pairs with the same difference are two representatives of one integer. They are not equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[2 - 5, Integers], integers], TypeTheoryTerm[Typed[-3, Integers], integers]]
```

<!-- => False -->

They are equal by `"quotientSoundness"`: `2 - 5` is the class of (2, 5) and `-3` that of (0, 3), and 2 + 3 and 0 + 5 both compute to 5:

```wl
TypeTheoryCheck[TypeTheoryTerm["quotientSoundness"["equalityReflexivity"[5]], integers], TypeTheoryTerm[Typed[2 - 5, Integers] == -3, integers]]
```

<!-- => Success["TypeChecked", ...] -->

## The Laws

The laws of a commutative ring are theorems, such as `"integerDistributivity"`:

```wl
integers["integerDistributivity"]
```

<!-- => theorem integerDistributivity : ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x (y + z) == x y + x z -->

They rewrite integer terms as the laws of the natural numbers rewrite theirs. A difference is a sum with the negation, `"integerSubtractionNegation"`; then associativity, the inverse and zero finish the proof:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + y) - y == x], integers, {
    "Introduce"[x, y],
    "Rewrite"["integerSubtractionNegation"],
    "Rewrite"["integerAdditionAssociativity"],
    "Rewrite"["integerAdditionNegation"],
    "Rewrite"["integerAdditionZero"]
}]
```

<!-- => Proof complete -->

## Proving a Law

The library proves each law the same way, and so can you. `"Induction"` on an integer, a class, gives a goal for the class of a pair:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], integers, {
    "Introduce"[x, y],
    "Induction"[x], "Introduce"[p],
    "Induction"[y], "Introduce"[q]
}]
```

<!-- => Proof, 1 goal: p ∶ ℕ × ℕ, q ∶ ℕ × ℕ ⊢ QuotientIntroduction[integerRelation, p] QuotientIntroduction[integerRelation, q] == QuotientIntroduction[integerRelation, q] QuotientIntroduction[integerRelation, p] -->

The product of two classes computes to the class of a pair, so `"quotientSoundness"` leaves the relation of two pairs, an equation of natural numbers:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], integers, {
    "Introduce"[x, y],
    "Induction"[x], "Introduce"[p],
    "Induction"[y], "Introduce"[q],
    "Apply"["quotientSoundness"]
}]
```

<!-- => Proof, 1 goal: p ∶ ℕ × ℕ, q ∶ ℕ × ℕ ⊢ integerRelation[(p〚"first"〛 q〚"first"〛 + p〚"second"〛 q〚"second"〛, p〚"first"〛 q〚"second"〛 + p〚"second"〛 q〚"first"〛), (q〚"first"〛 p〚"first"〛 + q〚"second"〛 p〚"second"〛, q〚"first"〛 p〚"second"〛 + q〚"second"〛 p〚"first"〛)] -->

`"Ring"` proves it, taking the fields of the pairs as atoms:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], integers, {
    "Introduce"[x, y],
    "Induction"[x], "Introduce"[p],
    "Induction"[y], "Introduce"[q],
    "Apply"["quotientSoundness"],
    "Ring"
}]
```

<!-- => Proof complete -->

Induction on a class proves propositions only. A function into data, such as negation, is lifted from pairs with [QuotientLift](), given a proof that it respects the relation, which `"LinearArithmetic"` and `"PolynomialReduce"` prove for the library's operations.

## Ring over the Integers

With the laws proved, `"Ring"` proves an equation of integers on its own, as it does one of natural numbers: it normalizes each side to a polynomial with integer coefficients, built from the integers' laws, where like monomials cancel. An identity of commutative rings, such as the square of a difference:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y)^2 == x^2 - 2 x y + y^2], integers, {
    "Introduce"[x, y],
    "Ring"
}]
```

<!-- => Proof complete -->

The atoms of the polynomials need not be variables, and the integers of natural numbers keep their sums, products and powers:

```wl
TypeTheoryProof[ForAll[{Typed[f, TypeSpecifier[{Integers} -> Integers]], Typed[n, Naturals]}, (f[n] + n)^2 == f[n]^2 + 2 n f[n] + Typed[n^2, Integers]], integers, {
    "Introduce"[f, n],
    "Ring"
}]
```

<!-- => Proof complete -->

What holds in no ring does not follow:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x - x == 1], integers, {"Introduce"[x], "Ring"}]
```

<!-- => Failure["NotRingEquation", ...] -->

## Inequalities and Sums of Squares

`x <= y` means that `y` is `x` plus a natural number. A square is at least 0, `"integerSquareNonnegative"`:

```wl
integers["integerSquareNonnegative"]
```

<!-- => theorem integerSquareNonnegative : ∀_z∶ℤ 0 ≤ z z -->

So are sums and natural multiples of what is at least 0, by `"integerNonnegativeAddition"` and `"integerNonnegativeScaling"`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 0 <= 3 (x x) + y y], integers, {
    "Introduce"[x, y],
    "Exact"["integerNonnegativeAddition"["integerNonnegativeScaling"[3, "integerSquareNonnegative"[x]], "integerSquareNonnegative"[y]]]
}]
```

<!-- => Proof complete -->

An inequality `x <= y` follows when a positive multiple of `y - x` is equal to something at least 0, `"integerLessEqualOfMultiple"`:

```wl
integers["integerLessEqualOfMultiple"]
```

<!-- => theorem integerLessEqualOfMultiple : ∀_d∶ℕ ∀_{x∶ℤ} ∀_{y∶ℤ} ∀_s∶ℤ ↑(d + 1) (y - x) == s ⇒ 0 ≤ s ⇒ x ≤ y -->

The tactic `"SumOfSquares"` proves an inequality this way. Wolfram finds a positive integer `d` and a sum `s` of squares of polynomials, each times a positive integer, with `d (y - x) == s`. `"Ring"` proves that equation, and the lemmas above prove that `s` is at least 0. Here `2 (x^2 + y^2 + z^2 - x y - y z - z x)` is the sum of the squares of `x - y`, `y - z` and `z - x`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x y + y z + z x <= x^2 + y^2 + z^2], integers, {
    "Introduce"[x, y, z],
    "SumOfSquares"
}]
```

<!-- => Proof complete -->

An inequality of natural numbers is that of their integers, by `"integerOfNaturalLessEqual"`:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, 2 a b <= a^2 + b^2], integers, {
    "Introduce"[a, b],
    "SumOfSquares"
}]
```

<!-- => Proof complete -->

Where the Gram matrix has free entries, a diagonally dominant one, each diagonal entry at least the sum of the absolute values of the others in its row, is positive semidefinite, and linear inequalities find one exactly; failing that, [SemidefiniteOptimization]() finds one. The Gram matrices of `x^4 - 4 x + 3`, three times which is `(x^2 + 2 x - 3)^2 + 2 (x^2 - x)^2`, have a free entry:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, 4 x <= x^4 + 3], integers, {
    "Introduce"[x],
    "SumOfSquares"
}]
```

<!-- => Proof complete -->

Wolfram finds no sum of squares where there is none. Here the inequality is false at `x = 2`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x^2 <= 2], integers, {"Introduce"[x], "SumOfSquares"}]
```

<!-- => Failure["NoSumOfSquares", ...] -->

## Deciding Equations

An equation of integers is decidable, by `"integerEqualityDecidable"`: the Boolean it computes compares a + d and c + b for the pairs (a, b) and (c, d). So [Decide]() computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[2 - 5, Integers] == -3], integers]]
```

<!-- => true -->

And `"Decide"` proves a closed equation, the two representatives that computation alone does not make equal included:

```wl
TypeTheoryProof[Typed[2 - 5, Integers] == -3, integers, {"Decide"}]
```

<!-- => Proof complete -->

## Quotient and Remainder

[Quotient]() and [Mod]() of integers are the Wolfram Language's: the quotient rounded down, and the remainder of the divisor's sign:

```wl
TypeTheoryExpression[NormalForm[TypeTheoryTerm[{Quotient[-7, 2], Mod[-7, 2], Quotient[7, -2], Mod[7, -2]}, integers]]]
```

<!-- => {-4, 1, -4, -1} -->

An integer is a class of pairs, so a function of it must give one value for every pair of the class. The quotient is a function of the integer's normal pair, (a - b, b - a) of a representing pair (a, b) in the natural numbers' subtraction, which stops at 0. Both representatives of -3 have the same normal pair:

```wl
NormalForm[TypeTheoryTerm[{"integerNormalPair"[Typed[2 - 5, Integers]], "integerNormalPair"[Typed[-3, Integers]]}, integers]]
```

<!-- => {(0, 3), (0, 3)} -->

That a - b == c - d where a + d == c + b is the theorem `"subtractionOfRelation"`, which makes the normal pair a function of the class; the quotient is then defined by the signs of the normal pairs. `"Decide"` proves an equation of quotients by computation:

```wl
TypeTheoryProof[Quotient[-9223372036854775809, 2] == -4611686018427387905, integers, {"Decide"}]
```

<!-- => Proof complete -->

Of natural numbers, [Quotient]() and [Mod]() are the natural numbers', defined by recursion on the dividend, so that the registration of their roles is checked, not trusted:

```wl
TypeTheoryType[Typed[n, Naturals] |-> Quotient[n (n + 1), 2], integers]
```

<!-- => ℕ → ℕ -->

## Theorems

The theorems of the integers are constants named by strings. These are those the integers add to the prelude's, each with its statement:

```wl
KeyDrop[Information[TypeTheoryEnvironment["Integers"], "Theorems"], Keys[Information[TypeTheoryEnvironment["Prelude"], "Theorems"]]]
```

<!-- => <|"integerNegationRespects" -> ..., ..., "integerAdditionCommutativity" -> ∀_x∶ℤ ∀_y∶ℤ x + y == y + x, ...|>, 72 theorems -->
