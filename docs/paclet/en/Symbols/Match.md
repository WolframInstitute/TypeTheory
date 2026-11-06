---
Template: Symbol
Name: Match
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Match
Keywords: [Wolfram Language, pattern matching, Match, monad, list monad, nondeterminism, list of results, Condition, MatchQ, ReplaceList, rules]
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
- Rules written as a term where a function of the type `Expressions -> Match[Expressions]` is expected, `lhs -> rhs`, `lhs :> rhs` or a list of them, are that function: the match of every way each rule matches, in order. [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated]() are definitions over such functions, which the kernel computes.
- The rules of a symbol, <code>[TypeTheoryFormalize]()[*f*, *env*, "Meaning" -> "Rules"]</code>, are a function from [Expressions]() to `Option[Expressions]` written with these constants.

## Basic Examples

The type of [Match]():

```wl
TypeTheoryType[Match, "WolframLanguage"]
```

<!-- => Type u → Type u -->

---

The type of the matches of natural numbers:

```wl
TypeTheoryType[Match[NonNegativeIntegers], "WolframLanguage"]
```

<!-- => Type -->

---

It is the type of the lists of natural numbers:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Match[NonNegativeIntegers], "WolframLanguage"]]
```

<!-- => {ℕ} -->

---

A match is the list of its results:

```wl
NormalForm[TypeTheoryTerm[MatchSum[MatchValue[1], MatchValue[2]], "WolframLanguage"]]
```

<!-- => {1, 2} -->

## Scope

The match with no result is the empty list:

```wl
NormalForm[TypeTheoryTerm[Typed[{}, Match[NonNegativeIntegers]], "WolframLanguage"]]
```

<!-- => {} -->

---

A match of expressions:

```wl
TypeTheoryType[MatchValue[Typed[f[1], Expressions]], "WolframLanguage"]
```

<!-- => Match[Expressions] -->

---

A match whose results are each a sequence of values:

```wl
TypeTheoryType[MatchValue[Sequence[1, "true"]], "WolframLanguage"]
```

<!-- => Match[[ℕ, 𝔹]] -->

---

A match of matches:

```wl
TypeTheoryType[MatchValue[MatchValue[1]], "WolframLanguage"]
```

<!-- => Match[Match[ℕ]] -->

---

[Condition]() keeps the results of a match where a Boolean holds:

```wl
TypeTheoryType[Condition, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} Match[A] → 𝔹 → Match[A] -->

---

A condition that holds keeps the result:

```wl
NormalForm[TypeTheoryTerm[MatchValue[1] /; "true", "WolframLanguage"]]
```

<!-- => {1} -->

---

A condition that fails leaves no result:

```wl
NormalForm[TypeTheoryTerm[MatchValue[1] /; Decide[1 == 2], "WolframLanguage"]]
```

<!-- => {} -->

---

[MatchQ]() is whether a match has a result:

```wl
TypeTheoryType[MatchQ, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} Match[A] → 𝔹 -->

---

A match with a result matches:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchQ[MatchValue[1]], "WolframLanguage"]]
```

<!-- => true -->

---

A match with none does not:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchQ[Typed[{}, Match[NonNegativeIntegers]]], "WolframLanguage"]]
```

<!-- => false -->

---

Rules are a function from an expression to its matches:

```wl
TypeTheoryType[Typed[{f[x_, y_] :> {y, x}, f[x_] :> x}, Expressions -> Match[Expressions]], "WolframLanguage"]
```

<!-- => Expressions → Match[Expressions] -->

---

Applied to an expression, the rules give the results of each rule that matches, in order:

```wl
NormalForm[TypeTheoryTerm[Typed[{f[x_] :> x, f[y_] :> {y}}, Expressions -> Match[Expressions]][f[1]], "WolframLanguage"]]
```

<!-- => {1, {1}} -->

---

[ReplaceList]() gives the list of every result:

```wl
TypeTheoryType[ReplaceList, "WolframLanguage"]
```

<!-- => Expressions → (Expressions → Match[Expressions]) → {Expressions} -->

---

A sequence pattern matches in several ways, the shortest first:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], "WolframLanguage"]]
```

<!-- => {{{1}, {2, 3}}, {{1, 2}, {3}}} -->

---

The arguments of an [Orderless]() head match in every order:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[HoldForm[a + b], x_ + y_ :> {x, y}], "WolframLanguage"]]
```

<!-- => {{a, b}, {b, a}} -->

## Properties and Relations

The definition of [Match]():

```wl
TypeTheoryEnvironment["WolframLanguage"][Match]
```

<!-- => definition Match : Type u → Type u := (A ∶ Type u) ↦ {A} -->

---

[Match]() of a type is the type of lists of it, by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Match[NonNegativeIntegers], "WolframLanguage"], TypeTheoryTerm[{NonNegativeIntegers}, "WolframLanguage"]]
```

<!-- => True -->

---

[MatchBind]() continues each result by a match, as the bind of the monad of lists:

```wl
NormalForm[TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> {x, x}], "WolframLanguage"]]
```

<!-- => {1, 1, 2, 2} -->

---

[MatchFirst]() takes the first result:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], "WolframLanguage"]]
```

<!-- => some[1] -->

---

A match with no result has no first result:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[Typed[{}, Match[NonNegativeIntegers]]], "WolframLanguage"]]
```

<!-- => none -->

## Possible Issues

[Match]() is a constant of the Wolfram Language environment, not of the prelude:

```wl
TypeTheoryType[Match[NonNegativeIntegers], TypeTheoryEnvironment["Prelude"]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

[Match]() takes a type:

```wl
TypeTheoryType[Match[3], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The match with no result does not say the type of its results, so [Typed]() gives it:

```wl
TypeTheoryType[TypeTheoryTerm[{}, "WolframLanguage"]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->
