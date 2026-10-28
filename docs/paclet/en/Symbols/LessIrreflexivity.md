---
Template: Symbol
Name: LessIrreflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessIrreflexivity
Keywords: [less, irreflexivity, prelude, natural numbers]
SeeAlso: [LessEqualAntisymmetry, SuccessorNotLessEqualZero, Less]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessIrreflexivity]()[*n*]</code> proves <code>[Not]()[*n* < *n*]</code>.

## Details & Options

- [LessIrreflexivity]() is a theorem of the prelude, proved by induction on *n* with [SuccessorNotLessEqualZero]() and [LessEqualPredecessor]().

## Basic Examples

The statement of [LessIrreflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessIrreflexivity]]
```

<!-- => ∀_n∶ℕ ¬n < n -->

---

With it, `3 <= 2` is false: it would make `2 < 2`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, 3 <= 2]}, LessIrreflexivity[2][LessEqualTransitivity[h, LessEqualReflexivity]]]], TypeTheoryTerm[Not[3 <= 2]]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

From `x < y` and `y <= x`, [LessEqualTransitivity]() gives `x < x`, which it refutes:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x < y, Not[y <= x]]], {
    TypeTheoryTactic["Introduce", x, y, h1, h2],
    TypeTheoryTactic["Exact", LessIrreflexivity[x][LessEqualTransitivity[h1, h2]]]
}]
```

<!-- => Proof complete -->

---

`x > x` unfolds to `x < x`, so it refutes that too:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals]}, LessIrreflexivity[x]]], TypeTheoryTerm[ForAll[{Typed[x, Naturals]}, Not[x > x]]]]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

The tactic `"LinearArithmetic"` refutes `x < x` too:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals]}, Implies[x < x, False]], {
    TypeTheoryTactic["Introduce", x, h],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->

---

The tactic `"Decide"` proves its instances with literals:

```wl
TypeTheoryProof[Not[3 < 3], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
