---
Template: Symbol
Name: AdditionSubtractionCancellation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionSubtractionCancellation
Keywords: [addition, subtraction, cancellation, prelude, natural numbers]
SeeAlso: [SubtractionSelf, SubtractionSuccessor, AdditionCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionSubtractionCancellation]()[*n*, *m*]</code> proves <code>(*n* + *m*) - *m* == *n*</code>.

## Details & Options

- [AdditionSubtractionCancellation]() is a theorem of the prelude, proved by induction on *m* with [SubtractionSuccessor]().

## Basic Examples

The statement of [AdditionSubtractionCancellation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSubtractionCancellation]]
```

<!-- => ∀_n∶ℕ ∀_m∶ℕ (n + m) - m == n -->

---

For variables:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals]}, AdditionSubtractionCancellation[x, y]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ (x + y) - y == x -->

## Scope

The tactic `"Rewrite"` cancels `y` inside a goal, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, (x + y) - y + 1 == x + 1], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", AdditionSubtractionCancellation[x, y]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

With [AdditionCommutativity](), the number added first cancels too:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, (y + x) - y == x], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", AdditionCommutativity[y, x]],
    TypeTheoryTactic["Exact", AdditionSubtractionCancellation[x, y]]
}]
```

<!-- => Proof complete -->

## Possible Issues

Subtraction stops at 0, so subtracting first and adding back does not cancel, and `(2 - 5) + 5` is 5:

```wl
WeakHeadNormalForm[TypeTheoryTerm[(2 - 5) + 5]]
```

<!-- => 5 -->

---

The tactic `"Ring"` does not prove it, since subtraction is not an operation of a semiring:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, (x + y) - y == x], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Failure["NotRingEquation", ...] -->
