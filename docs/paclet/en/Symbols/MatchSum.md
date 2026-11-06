---
Template: Symbol
Name: MatchSum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchSum
Keywords: [Wolfram Language, pattern matching, Match, alternatives, order, several results, Join, monad]
SeeAlso: [Match, MatchValue, MatchBind, MatchFirst, Alternatives, Join]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchSum]()[*m1*, *m2*]</code> is the match whose results are those of *m1*, then those of *m2*.

## Details & Options

- <code>[MatchSum]()[*m1*, *m2*]</code> has the type <code>[Match]()[*A*]</code> when *m1* and *m2* have it. It is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, the [Join]() of the two lists of results.
- [MatchSum]() is where a match gets several results: the alternatives of a pattern, the rules tried in turn, and the ways a sequence or an [Orderless]() head matches. [MatchValue]() holds one value, and `{}` is the match with no result, the unit of [MatchSum]().
- The alternatives keep their order, and a result that both give is there twice. [MatchFirst]() takes a result of *m1* before any of *m2*, as the Wolfram Language applies the first rule that matches.
- [MatchSum]() takes two matches; more alternatives are sums of sums.

## Basic Examples

The type of [MatchSum]():

```wl
TypeTheoryType[MatchSum, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} Match[A] → Match[A] → Match[A] -->

---

Two alternatives, in order:

```wl
NormalForm[TypeTheoryTerm[MatchSum[MatchValue[1], MatchValue[2]], "WolframLanguage"]]
```

<!-- => {1, 2} -->

---

The first result is the left one:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], "WolframLanguage"]]
```

<!-- => some[1] -->

## Scope

A match with several results, then one with one:

```wl
NormalForm[TypeTheoryTerm[MatchSum[Typed[{1, 2}, Match[NonNegativeIntegers]], MatchValue[3]], "WolframLanguage"]]
```

<!-- => {1, 2, 3} -->

---

Three alternatives are a sum of sums:

```wl
NormalForm[TypeTheoryTerm[MatchSum[MatchValue[1], MatchSum[MatchValue[2], MatchValue[3]]], "WolframLanguage"]]
```

<!-- => {1, 2, 3} -->

---

The order of the alternatives is kept:

```wl
NormalForm[TypeTheoryTerm[MatchSum[MatchValue[2], MatchValue[1]], "WolframLanguage"]]
```

<!-- => {2, 1} -->

---

A result that both alternatives give is there twice:

```wl
NormalForm[TypeTheoryTerm[MatchSum[MatchValue[1], MatchValue[1]], "WolframLanguage"]]
```

<!-- => {1, 1} -->

---

The [Alternatives]() of a pattern are tried in order:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, "a", b], f[___, x : (_Integer | _String), ___] :> x], "WolframLanguage"]]
```

<!-- => {1, "a"} -->

---

So are the rules of a list:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1], {f[x_] :> {x}, f[y_] :> y}], "WolframLanguage"]]
```

<!-- => {{1}, 1} -->

## Properties and Relations

The definition of [MatchSum]():

```wl
TypeTheoryEnvironment["WolframLanguage"][MatchSum]
```

<!-- => definition MatchSum : ∀_{A ∶ Type u} Match[A] → Match[A] → Match[A] := {A ∶ Type u} (m ∶ Match[A]) (n ∶ Match[A]) ↦ Join[m, n] -->

---

[MatchSum]() of two matches is the [Join]() of their lists, by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchSum[Typed[{1}, Match[NonNegativeIntegers]], Typed[{2, 3}, Match[NonNegativeIntegers]]], "WolframLanguage"], TypeTheoryTerm[Join[{1}, {2, 3}], "WolframLanguage"]]
```

<!-- => True -->

---

A match with no result on the left leaves the other's, for every match:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Typed[m, Match[NonNegativeIntegers]] |-> MatchSum[Typed[{}, Match[NonNegativeIntegers]], m], "WolframLanguage"],
    TypeTheoryTerm[Typed[m, Match[NonNegativeIntegers]] |-> m, "WolframLanguage"]
]
```

<!-- => True -->

---

So does a match with no result on the right, for a match written out:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchSum[MatchValue[3], Typed[{}, Match[NonNegativeIntegers]]], "WolframLanguage"], TypeTheoryTerm[MatchValue[3], "WolframLanguage"]]
```

<!-- => True -->

---

[MatchBind]() continues each alternative in turn:

```wl
NormalForm[TypeTheoryTerm[MatchBind[MatchSum[MatchValue[1], MatchValue[2]], Typed[x, NonNegativeIntegers] |-> MatchValue[x + 10]], "WolframLanguage"]]
```

<!-- => {11, 12} -->

---

Where the left alternative has no result, the first result is the right one's:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchSum[Typed[{}, Match[NonNegativeIntegers]], MatchValue[2]]], "WolframLanguage"]]
```

<!-- => some[2] -->

## Possible Issues

[MatchSum]() takes two matches:

```wl
TypeTheoryType[MatchSum[MatchValue[1], MatchValue[2], MatchValue[3]], "WolframLanguage"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

Its alternatives are matches, not values:

```wl
TypeTheoryType[MatchSum[1, 2], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The two alternatives have results of one type:

```wl
TypeTheoryType[MatchSum[MatchValue[1], MatchValue["true"]], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->
