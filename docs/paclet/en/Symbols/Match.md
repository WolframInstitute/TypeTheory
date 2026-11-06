---
Template: Symbol
Name: Match
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Match
Keywords: [Wolfram Language, pattern matching, Match, monad, list monad, nondeterminism, list of results, Condition, MatchQ, ReplaceList, rules, Orderless, sequence patterns]
SeeAlso: [MatchValue, MatchSum, MatchBind, MatchPart, MatchFirst, Expressions, Condition, MatchQ, ReplaceList]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[Match]()[*A*]</code> is the type of the matches with results in *A*: the list of their results, none, one, or several in the order they are tried.

## Details & Options

- [Match]() is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, of the type `Type u -> Type u`: <code>[Match]()[*A*]</code> is `{A}`, the type of the lists of elements of *A*, so a match is a list and computes as one.
- A match has no result where the pattern does not match, one where it matches once, and several where it matches in several ways, as a pattern with an [Orderless]() head or a sequence pattern does.
- [MatchValue]() makes one result and `{}` none; [MatchSum]() puts alternatives in order, where every match with several results comes from; [MatchBind]() matches parts in turn; [MatchPart]() matches at a part of an expression; [MatchFirst]() takes the first result, the one the Wolfram Language applies.
- <code>[Condition]()[*m*, *b*]</code>, written <code>*m* /; *b*</code>, keeps the results of *m* where the Boolean *b* is `"true"`, and <code>[MatchQ]()[*m*]</code> is whether *m* has a result. Both are definitions of the environment too.
- These are the operations of the monad of lists, the monad of nondeterminism, with its alternatives in order. They follow the match objects of the prototype paclet Wolfram/Patterns and of the Match IR of the WolframKernel project's compiler.
- Rules written as a term where a function of the type `Expressions -> Match[Expressions]` is expected, `lhs -> rhs`, `lhs :> rhs` or a list of them, are that function: the match of every way each rule matches, in order. [ReplaceList]() gives that match, [Replace]() its first result, and [ReplaceAll]() and [ReplaceRepeated]() are definitions over such functions too, all of which the kernel computes.
- The rules of a symbol, <code>[TypeTheoryFormalize]()[*f*, *env*, "Meaning" -> "Rules"]</code>, are a function from [Expressions]() to `Option[Expressions]` written with these constants.

## Basic Examples

A match is the list of its results:

```wl
TypeTheoryEnvironment["WolframLanguage"][Match]
```

<!-- => definition Match : Type u → Type u := (A ∶ Type u) ↦ {A} -->

---

Both rules match `f[1, 2]`, so the match has two results, in the order of the rules:

```wl
NormalForm[TypeTheoryTerm[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]], "WolframLanguage"]]
```

<!-- => {{2, 1}, {1, 2}} -->

---

A pattern of two sequences matches `f[1, 2, 3]` in two ways, the shorter first sequence first:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], "WolframLanguage"]]
```

<!-- => {{{1}, {2, 3}}, {{1, 2}, {3}}} -->

## Scope

The pairs of neighbours in a list of arguments, one result for each place the pattern matches:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3, 4], f[___, x_, y_, ___] :> {x, y}], "WolframLanguage"]]
```

<!-- => {{1, 2}, {2, 3}, {3, 4}} -->

---

The arguments of an [Orderless]() head match in every order:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[HoldForm[a + b], x_ + y_ :> {x, y}], "WolframLanguage"]]
```

<!-- => {{a, b}, {b, a}} -->

---

A rule that does not match gives the match with no result:

```wl
NormalForm[TypeTheoryTerm[Typed[f[x_, y_] :> {y, x}, Expressions -> Match[Expressions]][g[1, 2]], "WolframLanguage"]]
```

<!-- => {} -->

---

[MatchQ]() of the match of a rule is whether its pattern matches, here whether the first argument is an integer:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchQ[Typed[f[_Integer, ___] :> 0, Expressions -> Match[Expressions]][f[1, "a"]]], "WolframLanguage"]]
```

<!-- => true -->

Here it is a string:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchQ[Typed[f[_Integer, ___] :> 0, Expressions -> Match[Expressions]][f["a", 1]]], "WolframLanguage"]]
```

<!-- => false -->

---

[Condition]() keeps the results that a Boolean holds of:

```wl
NormalForm[TypeTheoryTerm[MatchBind[{1, 2, 3, 4}, Typed[n, NonNegativeIntegers] |-> (MatchValue[n] /; Decide[3 <= n])], "WolframLanguage"]]
```

<!-- => {3, 4} -->

## Properties and Relations

[ReplaceList]() gives the match of the rules, the same by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], "WolframLanguage"],
    TypeTheoryTerm[Typed[f[x__, y__] :> {{x}, {y}}, Expressions -> Match[Expressions]][f[1, 2, 3]], "WolframLanguage"]
]
```

<!-- => True -->

---

[Replace]() rewrites by the first result:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], "WolframLanguage"]]
```

<!-- => {{1}, {2, 3}} -->

---

A match is a list, so its [Length]() is the number of ways a pattern matches, here the four ways to split five arguments in two:

```wl
NormalForm[TypeTheoryTerm[Length[ReplaceList[f[1, 2, 3, 4, 5], f[x__, y__] :> 0]], "WolframLanguage"]]
```

<!-- => 4 -->

## Possible Issues

[Match]() is a constant of the Wolfram Language environment, not of the prelude:

```wl
TypeTheoryType[Match[NonNegativeIntegers], "Prelude"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The match with no result does not say the type of its results:

```wl
TypeTheoryType[TypeTheoryTerm[{}, "WolframLanguage"]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

[Typed]() gives it, and the type is the one it is given, `Match[Expressions]`, the type of lists of expressions:

```wl
TypeTheoryType[Typed[{}, Match[Expressions]], "WolframLanguage"]
```

<!-- => Match[Expressions] -->
