---
Template: Symbol
Name: SuccessorInjectivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SuccessorInjectivity
Keywords: [successor, injectivity, prelude, natural numbers]
SeeAlso: [SuccessorNotZero, NaturalNumberPredecessor, EqualityCongruence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SuccessorInjectivity]()[*h*]</code> proves <code>*m* == *n*</code> from a proof *h* of <code>*m* + 1 == *n* + 1</code>.

## Details & Options

- [SuccessorInjectivity]() is a theorem of the prelude, proved by applying [NaturalNumberPredecessor]() to both sides with [EqualityCongruence]().
- *m* and *n* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [SuccessorInjectivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorInjectivity]]
```

<!-- => ∀_{m∶ℕ} ∀_{n∶ℕ} m + 1 == n + 1 ⇒ m == n -->

---

From `x + 1 == 5`, `x == 4`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[h, x + 1 == 5]}, SuccessorInjectivity[h]]]]
```

<!-- => ∀_x∶ℕ x + 1 == 5 ⇒ x == 4 -->

## Scope

The tactic `"Apply"` leaves the equation of the successors as the goal:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x + 1 == y + 1, x == y]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Apply", SuccessorInjectivity]
}]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, h ∶ x + 1 == y + 1 ⊢ x + 1 == y + 1 -->

The hypothesis proves it:

```wl
TypeTheoryTactic["Assumption"][proof]
```

<!-- => Proof complete -->

## Properties and Relations

It is [EqualityCongruence]() with [NaturalNumberPredecessor](), which takes both sides back to the numbers before them:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x + 1 == y + 1]}, EqualityCongruence[NaturalNumberPredecessor, h]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x + 1 == y + 1, x == y]]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

`1 + x` is not a successor by computation, since addition recurses on its second argument, so an equation `1 + x == 1 + y` does not fit:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, 1 + x == 1 + y]}, SuccessorInjectivity[h]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
