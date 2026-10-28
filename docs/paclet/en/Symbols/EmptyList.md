---
Template: Symbol
Name: EmptyList
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EmptyList
Keywords: [list, empty list, nil, constructor, prelude]
SeeAlso: [Lists, ListPrepend, OptionNone]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[EmptyList]() is the list of <code>[Lists]()[*α*]</code> with no elements.

## Details & Options

- [EmptyList]() is the first constructor of [Lists](), as Lean's `List.nil`.
- *α* is an implicit argument, found from the expected type.
- [EmptyList]() displays as `{}`, and a list it ends, <code>[ListPrepend]()[1, [ListPrepend]()[2, [EmptyList]()]]</code>, as `{1, 2}`.

## Basic Examples

The type of [EmptyList]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EmptyList]]
```

<!-- => ∀_{α ∶ Type u} Lists[α] -->

---

The empty list of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[EmptyList, Lists[Naturals]]]]
```

<!-- => Lists[ℕ] -->

## Scope

Its length is 0, by computation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[Typed[EmptyList, Lists[Naturals]]]]]
```

<!-- => 0 -->

## Properties and Relations

[Join]() computes by recursion on its first list, so joining [EmptyList]() in front gives the other list by computation:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Join[EmptyList, l] == l], {TypeTheoryTactic["Introduce", l], TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Proof complete -->

## Possible Issues

Joined at the end, [EmptyList]() does not compute away, since the first list is a variable:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Join[l, EmptyList] == l], {TypeTheoryTactic["Introduce", l], TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Failure["NotReflexive", ...] -->

The theorem [JoinEmptyRight]() proves it:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Join[l, EmptyList] == l], {TypeTheoryTactic["Introduce", l], TypeTheoryTactic["Exact", JoinEmptyRight[l]]}]
```

<!-- => Proof complete -->

---

Where nothing gives the type of its elements, it is unknown:

```wl
TypeTheoryCheck[TypeTheoryTerm[Length[EmptyList]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->
