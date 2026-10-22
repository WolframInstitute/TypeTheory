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
