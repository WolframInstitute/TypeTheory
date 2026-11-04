---
Template: Symbol
Name: JoinAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/JoinAssociativity
Keywords: [list, join, append, associativity, prelude]
SeeAlso: [JoinEmptyRight, ReverseJoin, List]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[JoinAssociativity]()[*a*, *b*, *c*]</code> proves <code>[Join]()[[Join]()[*a*, *b*], *c*] == [Join]()[*a*, [Join]()[*b*, *c*]]</code>.

## Details & Options

- [JoinAssociativity]() is a theorem of the prelude, proved by recursion on *a*.

## Basic Examples

The statement of [JoinAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[JoinAssociativity]]
```

<!-- => ∀_{α ∶ Type u} ∀_a∶{α} ∀_b∶{α} ∀_c∶{α} Join[Join[a, b], c] == Join[a, Join[b, c]] -->

---

For lists of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[{Typed[a, {Naturals}], Typed[b, {Naturals}], Typed[c, {Naturals}]} |-> JoinAssociativity[a, b, c]]]
```

<!-- => ∀_a∶{ℕ} ∀_b∶{ℕ} ∀_c∶{ℕ} Join[Join[a, b], c] == Join[a, Join[b, c]] -->

## Scope

`"Rewrite"` with an instance regroups a join, and the goal closes once its sides are the same:

```wl
TypeTheoryProof[ForAll[{Typed[a, {Naturals}], Typed[b, {Naturals}], Typed[c, {Naturals}], Typed[d, {Naturals}]}, Join[Join[Join[a, b], c], d] == Join[Join[a, b], Join[c, d]]], {
    TypeTheoryTactic["Introduce", a, b, c, d],
    TypeTheoryTactic["Rewrite", JoinAssociativity[Join[a, b], c, d]]
}]
```

<!-- => Proof complete -->

## Applications

`"Simplify"` regroups as often as needed, here four lists to the right:

```wl
TypeTheoryProof[ForAll[{Typed[a, {Naturals}], Typed[b, {Naturals}], Typed[c, {Naturals}], Typed[d, {Naturals}]}, Join[Join[Join[a, b], c], d] == Join[a, Join[b, Join[c, d]]]], {
    TypeTheoryTactic["Introduce", a, b, c, d],
    TypeTheoryTactic["Simplify", {JoinAssociativity}]
}]
```

<!-- => Proof complete -->

## Properties and Relations

On lists written out both sides compute to the same list, so `"Reflexivity"` proves the instance:

```wl
TypeTheoryProof[
    Join[Join[Prepend[1][{}], Prepend[2][{}]], Prepend[3][{}]] == Join[Prepend[1][{}], Join[Prepend[2][{}], Prepend[3][{}]]],
    {TypeTheoryTactic["Reflexivity"]}
]
```

<!-- => Proof complete -->

## Possible Issues

On variables, [Join]() does not compute, so the law takes the theorem:

```wl
TypeTheoryProof[ForAll[{Typed[a, {Naturals}], Typed[b, {Naturals}], Typed[c, {Naturals}]}, Join[Join[a, b], c] == Join[a, Join[b, c]]], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
