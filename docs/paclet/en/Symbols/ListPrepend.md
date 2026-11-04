---
Template: Symbol
Name: ListPrepend
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ListPrepend
Keywords: [list, cons, prepend, constructor, prelude]
SeeAlso: [List, EmptyList, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[ListPrepend]()[*x*, *l*] is `Prepend[x][l]`, the list *l* with *x* in front, by the name it had.

## Details & Options

- The constructor of lists is written in the operator form of [Prepend](), `Prepend[x][l]`, its element first, as Lean's `List.cons x l`; the Wolfram Language's two-argument form `Prepend[l, x]` is the same list, and so is `Prepend \[Application] x \[Application] l`, which a list shows as where *l* is no literal list.
- [ListPrepend]()[*x*, *l*] is read as `Prepend[x][l]` where the environment declares no constant of that name.
- A definition by the recursor of lists takes the case of `Prepend[x][l]` as a function of *x*, *l* and the value at *l*, in that order.

## Basic Examples

The former name, with its arguments in the former order:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[ListPrepend[1, {2}]], TypeTheoryTerm[{1, 2}]]
```

<!-- => True -->

---

The length of a list, by the recursor of lists:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[Prepend[1][{2, 3}]]]]
```

<!-- => 3 -->
