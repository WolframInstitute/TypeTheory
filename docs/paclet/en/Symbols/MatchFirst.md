---
Template: Symbol
Name: MatchFirst
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchFirst
Keywords: [Wolfram Language, expressions, pattern matching, Match, first result, Option, rules, Replace, DownValues]
SeeAlso: [Match, MatchValue, MatchSum, MatchBind, Option, TypeTheoryFormalize, Replace]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchFirst]()[*m*]</code> is the first result of the match *m*, `"some"` of it, or `"none"` where *m* has none.

## Details & Options

- For *m* of the type <code>[Match]()[*A*]</code>, <code>[MatchFirst]()[*m*]</code> has the type <code>[Option]()[*A*]</code>. It is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, by the recursor of lists.
- The first result is the rule that the Wolfram Language applies, and none is an expression that no rule matches, which stays as it is. [Replace]() is the first result of its rules, or the expression where they have none.
- [MatchSum]() keeps its alternatives in order, so [MatchFirst]() of it takes the left one first.
- The rules of a symbol, from <code>[TypeTheoryFormalize]()[*f*, *env*, "Meaning" -> "Rules"]</code>, are [MatchFirst]() of the [MatchSum]() of the matches of each rule.

## Basic Examples

The type of [MatchFirst]():

```wl
TypeTheoryType[MatchFirst, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} Match[A] → Option[A] -->

---

The left alternative first:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], "WolframLanguage"]]
```

<!-- => some[1] -->

---

A match with no result has none:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[Typed[{}, Match[NonNegativeIntegers]]], "WolframLanguage"]]
```

<!-- => none -->

## Scope

The first of one result:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchValue[3]], "WolframLanguage"]]
```

<!-- => some[3] -->

---

Its type is an option:

```wl
TypeTheoryType[MatchFirst[MatchValue[3]], "WolframLanguage"]
```

<!-- => Option[ℕ] -->

---

The first result of a sequence of values:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchValue[Sequence[1, 2]]], "WolframLanguage"]]
```

<!-- => some[[1, 2]] -->

---

The first result of a match at a part:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[MatchPart[f[1, 2], 2, MatchValue]], "WolframLanguage"]]
```

<!-- => some[2] -->

---

The first rule that matches:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]]], "WolframLanguage"]]
```

<!-- => some[{2, 1}] -->

---

None where no rule matches:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[Typed[{f[x_, y_] :> {y, x}}, Expressions -> Match[Expressions]][f[1]]], "WolframLanguage"]]
```

<!-- => none -->

---

[Replace]() rewrites by the first rule that matches:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_] :> {y, x}], "WolframLanguage"]]
```

<!-- => {2, 1} -->

---

Where no rule matches, [Replace]() leaves the expression as it is:

```wl
NormalForm[TypeTheoryTerm[Replace[g[1, 2], f[x_, y_] :> {y, x}], "WolframLanguage"]]
```

<!-- => g[1, 2] -->

## Applications

The rules of a function, read by [TypeTheoryFormalize]():

```wl
swapped[x_, y_] := {y, x};
swapped[x_, y__] := {{y}, x};
swapping = TypeTheoryEnvironment["WolframLanguage", TypeTheoryFormalize[swapped, "WolframLanguage", "Meaning" -> "Rules"]]
```

<!-- => TypeTheoryEnvironment summary box: 226 constants -->

They are the first result of the sum of the rules:

```wl
swapping["DownValues[swapped]"]
```

<!-- => definition DownValues[swapped] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchSum[...]] -->

Two arguments match the first rule:

```wl
NormalForm[TypeTheoryTerm["DownValues[swapped]"[swapped[1, 2]], swapping]]
```

<!-- => some[{2, 1}] -->

Three match only the second:

```wl
NormalForm[TypeTheoryTerm["DownValues[swapped]"[swapped[1, 2, 3]], swapping]]
```

<!-- => some[{{2, 3}, 1}] -->

One matches neither, and the expression stays as it is:

```wl
NormalForm[TypeTheoryTerm["DownValues[swapped]"[swapped[1]], swapping]]
```

<!-- => none -->

## Properties and Relations

The definition of [MatchFirst]():

```wl
TypeTheoryEnvironment["WolframLanguage"][MatchFirst]
```

<!-- => definition MatchFirst : ∀_{A ∶ Type u} Match[A] → Option[A] := {A ∶ Type u} (m ∶ Match[A]) ↦ List_rec[(t ∶ {A}) ↦ Option[A], none, (x ∶ A) (rest ∶ {A}) (r ∶ Option[A]) ↦ some[x], m] -->

---

Where the left alternative has no result, the first is the right one's:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchSum[Typed[{}, Match[NonNegativeIntegers]], MatchValue[2]]], "WolframLanguage"]]
```

<!-- => some[2] -->

---

The recursor of [Option]() takes the result, or a default where there is none:

```wl
NormalForm[TypeTheoryTerm[InductiveRecursor[Option][Typed[o, Option[NonNegativeIntegers]] |-> NonNegativeIntegers, 0, Typed[r, NonNegativeIntegers] |-> r, MatchFirst[MatchValue[5]]], "WolframLanguage"]]
```

<!-- => 5 -->

## Possible Issues

The first result is an option, not the value itself:

```wl
TypeTheoryType[MatchFirst[MatchValue[3]] + 1, "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->
