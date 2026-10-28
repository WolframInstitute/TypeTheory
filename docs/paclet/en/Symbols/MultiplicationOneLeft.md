---
Template: Symbol
Name: MultiplicationOneLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationOneLeft
Keywords: [multiplication, one, left, prelude, natural numbers]
SeeAlso: [MultiplicationOneRight, MultiplicationCommutativity, PowerOne]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationOneLeft]()[*n*]</code> proves <code>1 * *n* == *n*</code>.

## Details & Options

- [MultiplicationOneLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [MultiplicationOneLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationOneLeft]]
```

<!-- => ∀_n∶ℕ 1 n == n -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, MultiplicationOneLeft[n]]]]
```

<!-- => ∀_n∶ℕ 1 n == n -->

## Scope

The tactic `"Rewrite"` removes a factor of 1 on the left, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 1 * n + 1 == n + 1], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Rewrite", MultiplicationOneLeft[n]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`m^1` computes to `1 * m`, so this law proves [PowerOne]():

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m^1 == m], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Exact", MultiplicationOneLeft[m]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The tactic `"Reflexivity"` does not prove `1 * n == n` for a variable *n*, since multiplication recurses on its second argument:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 1 * n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
