---
Template: Symbol
Name: ReverseJoin
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ReverseJoin
Keywords: [list, reverse, join, prelude]
SeeAlso: [ReverseReverse, JoinAssociativity, JoinEmptyRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ReverseJoin]()[*a*, *b*]</code> proves <code>[Reverse]()[[Join]()[*a*, *b*]] == [Join]()[[Reverse]()[*b*], [Reverse]()[*a*]]</code>.

## Details & Options

- [ReverseJoin]() is a theorem of the prelude, proved by recursion on *a*, from [JoinEmptyRight]() and [JoinAssociativity]().

## Basic Examples

The statement of [ReverseJoin]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ReverseJoin]]
```

<!-- => ∀_{α ∶ Type u} ∀_a∶Lists[α] ∀_b∶Lists[α] Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]] -->

---

For lists of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, ReverseJoin[a, b]]]]
```

<!-- => ∀_a∶Lists[ℕ] ∀_b∶Lists[ℕ] Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]] -->

## Applications

Reversing a list with an element appended puts the element first:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]], Typed[x, Naturals]}, Reverse[Append[l, x]] == ListPrepend[x, Reverse[l]]], {
    TypeTheoryTactic["Introduce", l, x],
    TypeTheoryTactic["Exact", ReverseJoin[l, ListPrepend[x, EmptyList]]]
}]
```

<!-- => Proof complete -->

---

`"Simplify"` reverses a join of three lists:

```wl
TypeTheoryProof[ForAll[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]], Typed[c, Lists[Naturals]]}, Reverse[Join[a, Join[b, c]]] == Join[Join[Reverse[c], Reverse[b]], Reverse[a]]], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Simplify", {ReverseJoin}]
}]
```

<!-- => Proof complete -->

## Properties and Relations

On lists written out both sides compute, so `"Reflexivity"` proves the instance:

```wl
TypeTheoryProof[
    Reverse[Join[ListPrepend[1, EmptyList], ListPrepend[2, ListPrepend[3, EmptyList]]]] == Join[Reverse[ListPrepend[2, ListPrepend[3, EmptyList]]], Reverse[ListPrepend[1, EmptyList]]],
    {TypeTheoryTactic["Reflexivity"]}
]
```

<!-- => Proof complete -->

## Possible Issues

The reversed parts come in the other order: reversing the join of the lists of 1 and of 2 gives the list of 2 and 1:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Reverse[Join[ListPrepend[1, EmptyList], ListPrepend[2, EmptyList]]]], TypeTheoryTerm[ListPrepend[2, ListPrepend[1, EmptyList]]]]
```

<!-- => True -->

Joining the reversed parts in their own order does not give it:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Reverse[Join[ListPrepend[1, EmptyList], ListPrepend[2, EmptyList]]]], TypeTheoryTerm[Join[Reverse[ListPrepend[1, EmptyList]], Reverse[ListPrepend[2, EmptyList]]]]]
```

<!-- => False -->
