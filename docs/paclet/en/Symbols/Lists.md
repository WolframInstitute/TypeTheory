---
Template: Symbol
Name: Lists
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Lists
Keywords: [list, lists, List, finite sequence, prelude, inductive type, Join, Length, Map, Reverse]
SeeAlso: [{}, Prepend, JoinAssociativity, ReverseReverse, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Lists]()[*α*]</code> is `{α}`, the type of finite lists of elements of *α*, by the name it had.

## Details & Options

- The type of lists is `List[α]`, written `{α}`: [List]() is a type and its elements alike, as the Wolfram Language writes both with one head. Where a type is expected, as the type of a binder, `{α}` is the type of lists of *α*; elsewhere `{a, b}` is a list. In a term on its own, the elements decide: types make the type.
- [Lists]()[*α*] is read as `{α}`, so that a term written with the name it had still elaborates.
- The type of lists is an inductive type of the prelude, with the constructors `{}` and `Prepend[x][l]`, the operator form of [Prepend]() applied, as Lean has `List.nil` and `List.cons x l`; `Prepend[l, x]` is the same list.
- The prelude defines [Join](), [Length](), [Map](), [Append]() and [Reverse]() on lists, each by recursion on its first list, and proves their laws: [JoinEmptyRight](), [JoinAssociativity](), [LengthJoin](), [LengthMap](), [MapJoin](), [MapComposition](), [ReverseJoin](), [ReverseReverse]() and [LengthReverse]().
- For *α* in `Type u`, `{α}` is in `Type u` too.

## Basic Examples

The type of the type of lists:

```wl
TypeTheoryCheck[TypeTheoryTerm[List]]
```

<!-- => Type u → Type u -->

---

The list of 1 and 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[Prepend[1][Prepend[2][{}]]]]
```

<!-- => {ℕ} -->

---

The name the type had reads as the type:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[{}, Lists[NonNegativeIntegers]]], TypeTheoryTerm[Typed[{}, {NonNegativeIntegers}]]]
```

<!-- => True -->

## Scope

The operations on lists compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[Prepend[1][Prepend[2][{}]]]]]
```

<!-- => 2 -->

## Properties and Relations

A law of lists by induction, unfolding [Join]() where it computes with the tactic `"Simplify"`:

```wl
TypeTheoryProof[ForAll[{Typed[a, {Naturals}], Typed[b, {Naturals}], Typed[c, {Naturals}]}, Join[Join[a, b], c] == Join[a, Join[b, c]]], {
	TypeTheoryTactic["Introduce", a, b, c],
	TypeTheoryTactic["Induction", a],
	TypeTheoryTactic["Simplify", {Join}],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["Simplify", {Join, ih}]
}]
```

<!-- => Proof complete -->
