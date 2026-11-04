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

[ListPrepend]()[*x*, *l*] is `Prepend[l, x]`, the list *l* with *x* in front, by the name and the order of arguments it had.

## Details & Options

- The constructor of lists is written `Prepend[l, x]`, its list first, as the Wolfram Language orders the arguments of `Prepend`, and `{x, ...}` is the list it makes of *x* and the elements of *l*.
- [ListPrepend]()[*x*, *l*] is read as `Prepend[l, x]` where the environment declares no constant of that name.
- A definition by the recursor of lists takes the case of `Prepend[l, x]` as a function of *l*, *x* and the value at *l*, in that order.

## Basic Examples

The former name, with its arguments in the former order:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[ListPrepend[1, {2}]], TypeTheoryTerm[{1, 2}]]
```

<!-- => True -->

---

The length of a list, by the recursor of lists:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[Prepend[{2, 3}, 1]]]]
```

<!-- => 3 -->
