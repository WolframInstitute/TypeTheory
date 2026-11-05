---
Template: Symbol
Name: Option
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Option
Keywords: [option, optional value, maybe, prelude, inductive type]
SeeAlso: [DisjointUnionType, List]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Option]()[*α*]</code> is the type of optional values of *α*: none, or some element of *α*.

## Details & Options

- [Option]() is an inductive type of the prelude, with the constructors `"none"` and `"some"`, as Lean's `Option`.
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
TypeTheoryCheck[TypeTheoryTerm["some"[3]]]
```

<!-- => Option[ℕ] -->

## Scope

Options nest; [Typed]() gives the type of the inner `"none"`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed["some"["none"], Option[Option[Naturals]]]]]
```

<!-- => Option[Option[ℕ]] -->

## Applications

The first element of a list, if it has one, defined with the recursor of [List]():

```wl
heads = TypeTheoryEnvironment[{TypeTheoryDefinition[FirstOfList, Function[{Typed[l, {Naturals}]},
    InductiveRecursor[List][Typed[t, {Naturals}] |-> Option[Naturals], "none", {Typed[x, Naturals], Typed[rest, {Naturals}], Typed[r, Option[Naturals]]} |-> "some"[x], l]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

The list of 5 and 7 has the first element 5:

```wl
WeakHeadNormalForm[TypeTheoryTerm[FirstOfList[Prepend[5][Prepend[7][{}]]], heads]]
```

<!-- => OptionSome[5] -->

The empty list has none:

```wl
WeakHeadNormalForm[TypeTheoryTerm[FirstOfList[{}], heads]]
```

<!-- => OptionNone -->

## Properties and Relations

Every option is `"none"` or a value: `"Cases"` gives a goal for each constructor:

```wl
TypeTheoryProof[ForAll[{Typed[o, Option[Naturals]]}, Or[o == "none", Exists[{Typed[x, Naturals]}, o == "some"[x]]]], {
    TypeTheoryTactic["Introduce", o],
    TypeTheoryTactic["Cases", o],
    TypeTheoryTactic["Exact", "orIntroductionLeft"["equalityReflexivity"["none"]]],
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Exact", "orIntroductionRight"["existsIntroduction"[x, "equalityReflexivity"["some"[x]]]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

[Option]() takes a type, and a proposition such as [True]() is not in `Type u`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Option[True]]]
```

<!-- => Failure["TypeMismatch", ...] -->
