---
Template: Symbol
Name: Option
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Option
Keywords: [option, optional value, maybe, prelude, inductive type]
SeeAlso: [OptionNone, OptionSome, DisjointUnionType, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Option]()[*α*]</code> is the type of optional values of *α*: none, or some element of *α*.

## Details & Options

- [Option]() is an inductive type of the prelude, with the constructors [OptionNone]() and [OptionSome](), as Lean's `Option`.
- For *α* in `Type u`, <code>[Option]()[*α*]</code> is in `Type u` too.

## Basic Examples

The type of [Option]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Option]]
```

<!-- => Type u → Type u -->

---

Some natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome[3]]]
```

<!-- => Option[ℕ] -->

## Scope

Options nest; [Typed]() gives the type of the inner [OptionNone]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[OptionSome[OptionNone], Option[Option[Naturals]]]]]
```

<!-- => Option[Option[ℕ]] -->

## Applications

The first element of a list, if it has one, defined with the recursor of [Lists]():

```wl
heads = TypeTheoryEnvironment[{TypeTheoryDefinition[FirstOfList, Function[{Typed[l, Lists[Naturals]]},
    InductiveRecursor[Lists][Function[{Typed[t, Lists[Naturals]]}, Option[Naturals]], OptionNone, Function[{Typed[x, Naturals], Typed[rest, Lists[Naturals]], Typed[r, Option[Naturals]]}, OptionSome[x]], l]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

The list of 5 and 7 has the first element 5:

```wl
WeakHeadNormalForm[TypeTheoryTerm[FirstOfList[ListPrepend[5, ListPrepend[7, EmptyList]]], heads]]
```

<!-- => OptionSome[5] -->

The empty list has none:

```wl
WeakHeadNormalForm[TypeTheoryTerm[FirstOfList[EmptyList], heads]]
```

<!-- => OptionNone -->

## Properties and Relations

Every option is [OptionNone]() or a value: `"Cases"` gives a goal for each constructor:

```wl
TypeTheoryProof[ForAll[{Typed[o, Option[Naturals]]}, Or[o == OptionNone, Exists[{Typed[x, Naturals]}, o == OptionSome[x]]]], {
    TypeTheoryTactic["Introduce", o],
    TypeTheoryTactic["Cases", o],
    TypeTheoryTactic["Exact", OrIntroductionLeft[EqualityReflexivity[OptionNone]]],
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Exact", OrIntroductionRight[ExistsIntroduction[x, EqualityReflexivity[OptionSome[x]]]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

[Option]() takes a type, and a proposition such as [True]() is not in `Type u`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Option[True]]]
```

<!-- => Failure["TypeMismatch", ...] -->
