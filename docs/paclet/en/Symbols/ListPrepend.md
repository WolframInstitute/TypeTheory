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
- A list that ends in [EmptyList]() displays as its elements in braces, <code>[ListPrepend]()[1, [ListPrepend]()[2, [EmptyList]()]]</code> as `{1, 2}`, and `{1, 2}` written in a term is that list; Lean writes `[1, 2]`, which in a Wolfram Language application, `f[[1, 2]]`, would read as [Part]().

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

---

The same list written with braces:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[{1, 2}], TypeTheoryTerm[ListPrepend[1, ListPrepend[2, EmptyList]]]]
```

<!-- => True -->
