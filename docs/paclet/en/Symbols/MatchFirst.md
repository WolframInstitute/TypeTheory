---
Template: Symbol
Name: MatchFirst
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchFirst
Keywords: [Wolfram Language, expressions, pattern matching, Match, first result, Option, rules, Replace, DownValues, Longest]
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

The first result of a match is an option:

```wl
TypeTheoryType[MatchFirst, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} Match[A] → Option[A] -->

---

Both rules match `f[1, 2]`, and the first result is the first rule's:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]]], "WolframLanguage"]]
```

<!-- => some[{2, 1}] -->

---

Where no rule matches there is none:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[Typed[f[x_, y_] :> {y, x}, Expressions -> Match[Expressions]][f[1]]], "WolframLanguage"]]
```

<!-- => none -->

## Scope

Of the ways a sequence pattern matches, the first is the one with the shortest first sequence:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[Typed[f[x__, y__] :> {{x}, {y}}, Expressions -> Match[Expressions]][f[1, 2, 3]]], "WolframLanguage"]]
```

<!-- => some[{{1}, {2, 3}}] -->

---

[Longest]() puts the longest first, so [Replace]() takes it:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2, 3], f[Longest[x__], y__] :> {{x}, {y}}], "WolframLanguage"]]
```

<!-- => {{1, 2}, {3}} -->

---

[Replace]() applies the first rule that matches, even where a later one matches too:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2], {f[x__] :> {x}, f[x_, y_] :> {y, x}}], "WolframLanguage"]]
```

<!-- => {1, 2} -->

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

[Replace]() takes the first result of its rules, or the expression where there is none, by the recursor of [Option]():

```wl
TypeTheoryEnvironment["WolframLanguage"][Replace]
```

<!-- => definition Replace : Expressions → (Expressions → Match[Expressions]) → Expressions := (e ∶ Expressions) (rules ∶ Expressions → Match[Expressions]) ↦ (Option_rec)[(o ∶ Option[Expressions]) ↦ Expressions, e, (r ∶ Expressions) ↦ r, MatchFirst[rules[e]]] -->

---

Whatever the right alternative, the first result of a sum is the left one's where it has one:

```wl
TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[m, Match[NonNegativeIntegers]]}, MatchFirst[MatchSum[MatchValue[a], m]] == "some"[a]], "WolframLanguage", {"Introduce"[a, m], "Reflexivity"}]
```

<!-- => Proof complete -->

## Possible Issues

The first result is an option, not the expression itself, so a function of expressions does not take it:

```wl
TypeTheoryType[Head[MatchFirst[ReplaceList[f[1, 2], f[x_, y_] :> {y, x}]]], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->

[Replace]() gives the expression:

```wl
NormalForm[TypeTheoryTerm[Head[Replace[f[1, 2], f[x_, y_] :> {y, x}]], "WolframLanguage"]]
```

<!-- => List -->
