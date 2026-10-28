---
Template: Symbol
Name: MultiplicationZeroLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationZeroLeft
Keywords: [multiplication, zero, left, prelude, natural numbers]
SeeAlso: [MultiplicationZeroRight, MultiplicationCommutativity, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationZeroLeft]()[*n*]</code> proves <code>0 * *n* == 0</code>.

## Details & Options

- [MultiplicationZeroLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [MultiplicationZeroLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationZeroLeft]]
```

<!-- => ∀_n∶ℕ 0 n == 0 -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, MultiplicationZeroLeft[n]]]]
```

<!-- => ∀_n∶ℕ 0 n == 0 -->

## Scope

The tactic `"Apply"` finds *n* from the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, 0 * (x + y) == 0], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", MultiplicationZeroLeft]
}]
```

<!-- => Proof complete -->

---

The tactic `"Rewrite"` with it, then with [AdditionZeroLeft](), clears `0 * n + n`:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 * n + n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Rewrite", MultiplicationZeroLeft[n]],
    TypeTheoryTactic["Rewrite", AdditionZeroLeft[n]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

With [MultiplicationCommutativity](), `0 * n` becomes `n * 0`, which is 0 by computation:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 * n == 0], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[0, n]],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

## Possible Issues

The tactic `"Reflexivity"` does not prove `0 * n == 0` for a variable *n*, since multiplication recurses on its second argument:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 * n == 0], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
