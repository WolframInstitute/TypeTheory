---
Template: Symbol
Name: Option
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Option
Keywords: [option, optional value, maybe, partial function, lookup, default value, prelude, inductive type]
SeeAlso: [DisjointUnionType, CartesianProductType, List, InductiveRecursor, NormalForm]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Option]()[*α*]</code> is the type of optional values of *α*: none, or some element of *α*.

## Details & Options

- [Option]() is an inductive type of the prelude, with the constructors `"none"` and `"some"`, as Lean's `Option`.
- Both constructors take *α* implicitly. `"some"[x]` finds it from `x`; `"none"` has nothing to find it from, so it needs the type it is expected to have, as <code>[Typed]()["none", [Option]()[[Naturals]()]]</code> gives.
- An [Option]()-valued function is a partial function: it gives `"none"` where it has no answer, as a lookup that finds no key, or a subtraction that would go below 0.
- Its recursor, <code>[InductiveRecursor]()[[Option]()]</code>, takes the result for `"none"` and a function of the value for `"some"`: a default value, or a map over the value.
- `"some"` is injective and never `"none"`, as the recursor proves. `"Decide"` does not decide equations of options, since the prelude has no instance of [Decidable]() for them.
- For *α* in `Type u`, <code>[Option]()[*α*]</code> is in `Type u` too.

## Basic Examples

The type of [Option]():

```wl
TypeTheoryType[Option]
```

<!-- => Type u → Type u -->

---

Some natural number:

```wl
TypeTheoryType["some"[3]]
```

<!-- => Option[ℕ] -->

---

No natural number, which needs its type:

```wl
TypeTheoryType[Typed["none", Option[Naturals]]]
```

<!-- => Option[ℕ] -->

## Scope

Options nest; [Typed]() gives the type of the inner `"none"`:

```wl
TypeTheoryType[Typed["some"["none"], Option[Option[Naturals]]]]
```

<!-- => Option[Option[ℕ]] -->

---

A value with a default, by the recursor: the default for `"none"`, the value itself for `"some"`:

```wl
withDefault = TypeTheoryTerm[{Typed[d, Naturals], Typed[o, Option[Naturals]]} |-> InductiveRecursor[Option][Typed[t, Option[Naturals]] |-> Naturals, d, Typed[x, Naturals] |-> x, o]]
```

<!-- => (d ∶ ℕ) (o ∶ Option[ℕ]) ↦ (Option_rec)[(t ∶ Option[ℕ]) ↦ ℕ, d, (x ∶ ℕ) ↦ x, o] -->

The default 0 for no value:

```wl
WeakHeadNormalForm[TypeTheoryTerm[withDefault[0, Typed["none", Option[Naturals]]]]]
```

<!-- => 0 -->

The value 7 for some 7:

```wl
WeakHeadNormalForm[TypeTheoryTerm[withDefault[0, "some"[7]]]]
```

<!-- => 7 -->

---

A function applied to the value, if there is one, here adding 1 to 4:

```wl
NormalForm[TypeTheoryTerm[InductiveRecursor[Option][Typed[t, Option[Naturals]] |-> Option[Naturals], "none", Typed[x, Naturals] |-> "some"[x + 1], "some"[4]]]]
```

<!-- => some[5] -->

---

Options of types are in `Type 1`:

```wl
TypeTheoryType[Option[TypeUniverse[1]]]
```

<!-- => Type 1 -->

## Applications

The first element of a list, if it has one, defined with the recursor of [List]():

```wl
heads = TypeTheoryEnvironment[{TypeTheoryDefinition[FirstOfList, Function[{Typed[l, {Naturals}]},
    InductiveRecursor[List][Typed[t, {Naturals}] |-> Option[Naturals], "none", {Typed[x, Naturals], Typed[rest, {Naturals}], Typed[r, Option[Naturals]]} |-> "some"[x], l]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

The list of 5 and 7 has the first element 5:

```wl
WeakHeadNormalForm[TypeTheoryTerm[FirstOfList[{5, 7}], heads]]
```

<!-- => some[5] -->

The empty list has none:

```wl
WeakHeadNormalForm[TypeTheoryTerm[FirstOfList[{}], heads]]
```

<!-- => none -->

---

Subtraction that gives none instead of stopping at 0, by cases on the Boolean that decides `n <= m`:

```wl
checked = TypeTheoryEnvironment[{TypeTheoryDefinition[CheckedSubtract, Typed[
    {Typed[m, Naturals], Typed[n, Naturals]} |-> InductiveRecursor[Booleans][Typed[b, Booleans] |-> Option[Naturals], "none", "some"[m - n], Decide[n <= m]],
    TypeSpecifier[{Naturals, Naturals} -> Option[Naturals]]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

7 less 3:

```wl
NormalForm[TypeTheoryTerm[CheckedSubtract[7, 3], checked]]
```

<!-- => some[4] -->

3 less 7 has no answer:

```wl
NormalForm[TypeTheoryTerm[CheckedSubtract[3, 7], checked]]
```

<!-- => none -->

---

The value of a key in a list of pairs, if the key is there:

```wl
lookups = TypeTheoryEnvironment[{TypeTheoryDefinition[LookupNumber, Typed[
    {Typed[key, Naturals], Typed[l, {CartesianProductType[Naturals, Naturals]}]} |-> InductiveRecursor[List][
        Typed[t, {CartesianProductType[Naturals, Naturals]}] |-> Option[Naturals],
        "none",
        {Typed[x, CartesianProductType[Naturals, Naturals]], Typed[rest, {CartesianProductType[Naturals, Naturals]}], Typed[r, Option[Naturals]]} |->
            InductiveRecursor[Booleans][Typed[b, Booleans] |-> Option[Naturals], r, "some"[x[[2]]], Decide[x[[1]] == key]],
        l
    ],
    TypeSpecifier[{Naturals, {CartesianProductType[Naturals, Naturals]}} -> Option[Naturals]]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

The key 2 has the value 20:

```wl
NormalForm[TypeTheoryTerm[LookupNumber[2, {"pair"[1, 10], "pair"[2, 20]}], lookups]]
```

<!-- => some[20] -->

The key 3 is not there:

```wl
NormalForm[TypeTheoryTerm[LookupNumber[3, {"pair"[1, 10], "pair"[2, 20]}], lookups]]
```

<!-- => none -->

## Properties and Relations

Every option is `"none"` or a value: `"Cases"` gives a goal for each constructor:

```wl
TypeTheoryProof[ForAll[{Typed[o, Option[Naturals]]}, Or[o == "none", Exists[{Typed[x, Naturals]}, o == "some"[x]]]], {
    "Introduce"[o],
    "Cases"[o],
    "Exact"["orIntroductionLeft"["equalityReflexivity"["none"]]],
    "Introduce"[x],
    "Exact"["orIntroductionRight"["existsIntroduction"[x, "equalityReflexivity"["some"[x]]]]]
}]
```

<!-- => Proof complete -->

---

`"some"` is injective: equal options have equal values, by congruence with the value and a default:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, "some"[x] == "some"[y]]}, x == y], {
    "Introduce"[x, y, h],
    "Exact"["equalityCongruence"[Typed[o, Option[Naturals]] |-> InductiveRecursor[Option][Typed[t, Option[Naturals]] |-> Naturals, 0, Typed[z, Naturals] |-> z, o], h]]
}]
```

<!-- => Proof complete -->

---

`"none"` is no value: the recursor of [Equal]() carries a proof of [True]() along the equation to the proposition that is [True]() at `"none"` and [False]() at a value:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals]}, Not[Typed["none", Option[Naturals]] == "some"[x]]], {
    "Introduce"[x, h],
    "Exact"[InductiveRecursor[Equal][
        {Typed[y, Option[Naturals]], Typed[t, "none" == y]} |-> InductiveRecursor[Option][Typed[q, Option[Naturals]] |-> TypeUniverse[0], True, Typed[z, Naturals] |-> False, y],
        "trueIntroduction",
        h
    ]]
}]
```

<!-- => Proof complete -->

## Possible Issues

[Option]() takes a type, and a proposition such as [True]() is not in `Type u`:

```wl
TypeTheoryType[Option[True]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

Two `"none"` alone do not say what they are options of:

```wl
TypeTheoryType["none" == "none"]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

---

Subtraction that gives none instead of stopping at 0:

```wl
checked = TypeTheoryEnvironment[{TypeTheoryDefinition[CheckedSubtract, Typed[
    {Typed[m, Naturals], Typed[n, Naturals]} |-> InductiveRecursor[Booleans][Typed[b, Booleans] |-> Option[Naturals], "none", "some"[m - n], Decide[n <= m]],
    TypeSpecifier[{Naturals, Naturals} -> Option[Naturals]]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

[WeakHeadNormalForm]() computes only as far as the constructor, and leaves the value inside as it is; [NormalForm]() computes it too:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CheckedSubtract[7, 3], checked]]
```

<!-- => some[7 - 3] -->

---

`"Decide"` does not decide an equation of options, which the prelude has no decision for; the recursor of [Equal]() proves it, as above:

```wl
TypeTheoryProof[Not[Typed["none", Option[Naturals]] == "some"[3]], {"Decide"}]
```

<!-- => Failure["NotDecidable", ...] -->
