---
Template: Symbol
Name: Lists
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Lists
Keywords: [list, lists, finite sequence, prelude, inductive type, Join, Length, Map, Reverse]
SeeAlso: [EmptyList, ListPrepend, JoinAssociativity, ReverseReverse, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Lists]()[*α*]</code> is the type of finite lists of elements of *α*.

## Details & Options

- [Lists]() is an inductive type of the prelude, with the constructors [EmptyList]() and [ListPrepend](), the head first, as Lean's `List`.
- The prelude defines [Join](), [Length](), [Map](), [Append]() and [Reverse]() on lists, each by recursion on its first list, and proves their laws: [JoinEmptyRight](), [JoinAssociativity](), [LengthJoin](), [LengthMap](), [MapJoin](), [MapComposition](), [ReverseJoin](), [ReverseReverse]() and [LengthReverse]().
- For *α* in `Type u`, <code>[Lists]()[*α*]</code> is in `Type u` too.

## Basic Examples

The type of [Lists]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Lists]]
```

<!-- => Type u → Type u -->

---

The list of 1 and 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[ListPrepend[1, ListPrepend[2, EmptyList]]]]
```

<!-- => Lists[ℕ] -->

## Scope

The operations on lists compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[ListPrepend[1, ListPrepend[2, EmptyList]]]]]
```

<!-- => 2 -->

## Properties and Relations

A law of lists by induction, unfolding [Join]() where it computes with the tactic `"Simplify"`:

```wl
TypeTheoryProof[ForAll[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]], Typed[c, Lists[Naturals]]}, Join[Join[a, b], c] == Join[a, Join[b, c]]], {
	TypeTheoryTactic["Introduce", a, b, c],
	TypeTheoryTactic["Induction", a],
	TypeTheoryTactic["Simplify", {Join}],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["Simplify", {Join, ih}]
}]
```

<!-- => Proof complete -->
