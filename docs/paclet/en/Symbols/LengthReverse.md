---
Template: Symbol
Name: LengthReverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LengthReverse
Keywords: [list, length, reverse, prelude]
SeeAlso: [LengthJoin, ReverseReverse, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LengthReverse]()[*l*]</code> proves <code>[Length]()[[Reverse]()[*l*]] == [Length]()[*l*]</code>.

## Details & Options

- [LengthReverse]() is a theorem of the prelude, proved by recursion on *l*, from [LengthJoin]().

## Basic Examples

The statement of [LengthReverse]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LengthReverse]]
```

<!-- => ∀_{α ∶ Type u} ∀_l∶Lists[α] Length[Reverse[l]] == Length[l] -->

---

For the list of 1 and 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[LengthReverse[ListPrepend[1, ListPrepend[2, EmptyList]]]]]
```

<!-- => Length[Reverse[{1, 2}]] == Length[{1, 2}] -->

## Applications

With [LengthJoin](), `"Simplify"` finds the length of a reversed join:

```wl
TypeTheoryProof[ForAll[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, Length[Reverse[Join[a, b]]] == Length[a] + Length[b]], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Simplify", {LengthReverse, LengthJoin}]
}]
```

<!-- => Proof complete -->

## Properties and Relations

On a list written out the length computes, so `"Reflexivity"` proves the instance:

```wl
TypeTheoryProof[Length[Reverse[ListPrepend[1, ListPrepend[2, EmptyList]]]] == 2, {TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Proof complete -->

---

Tactics prove it by induction, as the prelude does: [Reverse]() puts the first element at the end with [Append](), and [LengthJoin]() counts it:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Length[Reverse[l]] == Length[l]], {
    TypeTheoryTactic["Introduce", l],
    TypeTheoryTactic["Induction", l],
    TypeTheoryTactic["Simplify", {Reverse, Length}],
    TypeTheoryTactic["Introduce", x, rest, ih],
    TypeTheoryTactic["Simplify", {Reverse, Append, LengthJoin, Length, ih}]
}]
```

<!-- => Proof complete -->

## Possible Issues

On a variable, [Reverse]() does not compute, so `"Reflexivity"` does not prove it:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Length[Reverse[l]] == Length[l]], {TypeTheoryTactic["Introduce", l], TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Failure["NotReflexive", ...] -->
