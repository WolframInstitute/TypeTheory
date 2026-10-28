---
Template: Symbol
Name: LessEqualReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualReflexivity
Keywords: [less, equal, reflexivity, prelude, natural numbers]
SeeAlso: [LessEqualStep, LessEqualZero, LessEqualTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[LessEqualReflexivity]() proves <code>*n* <= *n*</code>.

## Details & Options

- [LessEqual]() is an inductive family of the prelude, as Lean's `Nat.le`: <code>*m* <= *n*</code> when *n* is *m*, or the successor of a number at least *m*. [LessEqualReflexivity]() and [LessEqualStep]() are its constructors.
- *n* is an implicit argument, found from the type the proof is expected to have.

## Basic Examples

The statement of [LessEqualReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualReflexivity]]
```

<!-- => ∀_{n∶ℕ} n ≤ n -->

---

A proof of `3 <= 3`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualReflexivity], TypeTheoryTerm[3 <= 3]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The tactic `"Constructor"` applies it, the first constructor of [LessEqual]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals]}, x <= x], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Constructor"]
}]
```

<!-- => Proof complete -->

---

It proves `a <= b` whenever *a* and *b* are equal by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualReflexivity], TypeTheoryTerm[2 + 2 <= 4]]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

*n* is implicit, so [LessEqualReflexivity]() takes no argument:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualReflexivity[3]]]
```

<!-- => Failure["ElaborationFailed", ...] -->

[Construct]() gives *n* explicitly:

```wl
TypeTheoryCheck[TypeTheoryTerm[Construct[LessEqualReflexivity, 3]]]
```

<!-- => 3 ≤ 3 -->

---

`0 + x` is not *x* by computation, so it does not prove `0 + x <= x`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals]}, LessEqualReflexivity]], TypeTheoryTerm[ForAll[{Typed[x, Naturals]}, 0 + x <= x]]]
```

<!-- => Failure["TypeMismatch", ...] -->
