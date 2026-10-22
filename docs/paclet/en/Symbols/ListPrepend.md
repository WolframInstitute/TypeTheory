---
Template: Symbol
Name: ListPrepend
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ListPrepend
Keywords: [list, cons, prepend, constructor, prelude]
SeeAlso: [Lists, EmptyList, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ListPrepend]()[*x*, *l*]</code> is the list whose first element is *x*, followed by the elements of *l*.

## Details & Options

- [ListPrepend]() is the second constructor of [Lists](), as Lean's `List.cons`.
- *α* is an implicit argument, found from the type of *x*.

## Basic Examples

The statement of [ListPrepend]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ListPrepend]]
```

<!-- => ∀_{α ∶ Type u} α → Lists[α] → Lists[α] -->

---

The list of 1 and 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[ListPrepend[1, ListPrepend[2, EmptyList]]]]
```

<!-- => Lists[ℕ] -->

## Properties and Relations

[Length]() counts the elements prepended:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[ListPrepend[1, ListPrepend[2, EmptyList]]]]]
```

<!-- => 2 -->
