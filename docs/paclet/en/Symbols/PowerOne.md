---
Template: Symbol
Name: PowerOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PowerOne
Keywords: [power, one, prelude, natural numbers]
SeeAlso: [PowerZero, PowerAddition, MultiplicationOneLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PowerOne]()[*m*]</code> proves <code>*m*^1 == *m*</code>.

## Details & Options

- [PowerOne]() is a theorem of the prelude: `m^1` computes to `1 * m`, and [MultiplicationOneLeft]() proves the rest.

## Basic Examples

The statement of [PowerOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerOne]]
```

<!-- => ∀_m∶ℕ m^1 == m -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[m, Naturals]}, PowerOne[m]]]]
```

<!-- => ∀_m∶ℕ m^1 == m -->

## Scope

The tactic `"Rewrite"` replaces `m^1` by *m*, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m^1 + 1 == m + 1], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Rewrite", PowerOne[m]]
}]
```

<!-- => Proof complete -->

---

Since `m^2` computes to `m^1 * m`, `"Change"` and then `"Rewrite"` with it prove that a square is a product:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m^2 == m * m], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Change", m^1 * m == m * m],
    TypeTheoryTactic["Rewrite", PowerOne[m]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`m^1` computes to `1 * m`, as `"Change"` shows, and [MultiplicationOneLeft]() proves the rest:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m^1 == m], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Change", 1 * m == m]
}]
```

<!-- => Proof, 1 goal: m ∶ ℕ ⊢ 1 m == m -->

## Possible Issues

The tactic `"Reflexivity"` does not prove `m^1 == m` for a variable *m*, since `1 * m` does not compute:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m^1 == m], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
