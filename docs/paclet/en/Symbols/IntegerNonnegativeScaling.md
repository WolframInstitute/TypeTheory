---
Template: Symbol
Name: IntegerNonnegativeScaling
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerNonnegativeScaling
Keywords: [integers, order, multiplication, nonnegative, sum of squares, theorem, Lean]
SeeAlso: [IntegerSquareNonnegative, IntegerNonnegativeAddition, IntegerNonnegativeCancellation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerNonnegativeScaling]()[*k*, *hx*]</code> proves <code>0 <= *k* *x*</code> from a proof *hx* of <code>0 <= *x*</code>, for a natural number *k* and an integer *x*.

## Details & Options

- [IntegerNonnegativeScaling]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- The natural number *k* is an integer by the coercion `"integerOfNatural"`; *x* is an implicit argument, found from the type of *hx*.

## Basic Examples

The statement of [IntegerNonnegativeScaling]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerNonnegativeScaling, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_k∶ℕ ∀_{x∶ℤ} 0 ≤ x ⇒ 0 ≤ ↑k x -->

---

Three times a square is at least 0:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, 0 <= 3 (x x)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Exact", IntegerNonnegativeScaling[3, IntegerSquareNonnegative[x]]]
}]
```

<!-- => Proof complete -->

## Scope

The factor can be a natural number variable:

```wl
TypeTheoryProof[ForAll[{Typed[k, Naturals], Typed[x, Integers]}, 0 <= k (x x)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", k, x],
    TypeTheoryTactic["Exact", IntegerNonnegativeScaling[k, IntegerSquareNonnegative[x]]]
}]
```

<!-- => Proof complete -->

---

`"Apply"` with the factor alone finds `x` from the goal and leaves `0 <= x` to prove:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, Implies[0 <= x, 0 <= 4 x]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, h],
    TypeTheoryTactic["Apply", IntegerNonnegativeScaling[4]]
}]
```

<!-- => Proof, 1 goal: x ∶ ℤ, h ∶ 0 ≤ x ⊢ 0 ≤ x -->

## Applications

A weighted sum of squares is at least 0, with [IntegerNonnegativeAddition]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 0 <= 2 (x x) + 5 (y y)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Exact", IntegerNonnegativeAddition[IntegerNonnegativeScaling[2, IntegerSquareNonnegative[x]], IntegerNonnegativeScaling[5, IntegerSquareNonnegative[y]]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The factor is a natural number, so an integer factor does not fit, even one known to be at least 0:

```wl
TypeTheoryProof[ForAll[{Typed[c, Integers], Typed[x, Integers]}, Implies[0 <= c, 0 <= c (x x)]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", c, x, h],
    TypeTheoryTactic["Exact", IntegerNonnegativeScaling[c, IntegerSquareNonnegative[x]]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->
