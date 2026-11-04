---
Template: Symbol
Name: ReverseReverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ReverseReverse
Keywords: [list, reverse, involution, prelude]
SeeAlso: [ReverseJoin, LengthReverse, List]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ReverseReverse]()[*l*]</code> proves <code>[Reverse]()[[Reverse]()[*l*]] == *l*</code>.

## Details & Options

- [ReverseReverse]() is a theorem of the prelude, proved by recursion on *l*, from [ReverseJoin]().

## Basic Examples

The statement of [ReverseReverse]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ReverseReverse]]
```

<!-- => ∀_{α ∶ Type u} ∀_l∶{α} Reverse[Reverse[l]] == l -->

---

For the list of 1 and 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[ReverseReverse[Prepend[Prepend[{}, 2], 1]]]]
```

<!-- => Reverse[Reverse[{1, 2}]] == {1, 2} -->

## Scope

`"Simplify"` uses it on any list, here a join:

```wl
TypeTheoryProof[ForAll[{Typed[a, {Naturals}], Typed[b, {Naturals}]}, Reverse[Reverse[Join[a, b]]] == Join[a, b]], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Simplify", {ReverseReverse}]
}]
```

<!-- => Proof complete -->

## Applications

[Reverse]() is injective: rewriting from right to left writes `a` as the reverse of its reverse:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, {Naturals}], Typed[b, {Naturals}]}, Implies[Reverse[a] == Reverse[b], a == b]], {
    TypeTheoryTactic["Introduce", a, b, e],
    TypeTheoryTactic["Rewrite", ReverseReverse[a], "RightToLeft"]
}]
```

<!-- => Proof, 1 goal: a ∶ {ℕ}, b ∶ {ℕ}, e ∶ Reverse[a] == Reverse[b] ⊢ Reverse[Reverse[a]] == b -->

The hypothesis replaces the inner reverse:

```wl
proof = TypeTheoryTactic["Rewrite", e][proof]
```

<!-- => Proof, 1 goal: a ∶ {ℕ}, b ∶ {ℕ}, e ∶ Reverse[a] == Reverse[b] ⊢ Reverse[Reverse[b]] == b -->

[ReverseReverse]() finishes it:

```wl
TypeTheoryTactic["Rewrite", ReverseReverse[b]][proof]
```

<!-- => Proof complete -->

## Properties and Relations

On a list written out both reverses compute, so `"Reflexivity"` proves the instance:

```wl
TypeTheoryProof[Reverse[Reverse[Prepend[Prepend[{}, 2], 1]]] == Prepend[Prepend[{}, 2], 1], {TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Proof complete -->

## Possible Issues

On a variable, [Reverse]() does not compute, so the law takes the theorem:

```wl
TypeTheoryProof[ForAll[{Typed[l, {Naturals}]}, Reverse[Reverse[l]] == l], {TypeTheoryTactic["Introduce", l], TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Failure["NotReflexive", ...] -->
