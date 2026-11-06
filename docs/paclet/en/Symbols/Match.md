---
Template: Symbol
Name: Match
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Match
Keywords: [Wolfram Language, pattern matching, Match, monad, list monad, nondeterminism, list of results, Condition, MatchQ, ReplaceList, rules, Orderless, sequence patterns, prelude]
SeeAlso: [MatchValue, MatchSum, MatchBind, MatchPart, MatchFirst, Expressions, Condition, MatchQ, ReplaceList]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[Match]()[*A*]</code> is the type of the matches with results in *A*: the list of their results, none, one, or several in the order they are tried.

## Details & Options

- [Match]() is a definition of the prelude, of the type `Type u -> Type u`: <code>[Match]()[*A*]</code> is `{A}`, the type of the lists of elements of *A*, so a match is a list and computes as one.
- A match has no result where the pattern does not match, one where it matches once, and several where it matches in several ways, as a pattern with an [Orderless]() head or a sequence pattern does.
- [MatchValue]() makes one result and `{}` none; [MatchSum]() puts alternatives in order, where every match with several results comes from; [MatchBind]() matches parts in turn; [MatchPart]() matches at a part of an expression; [MatchFirst]() takes the first result, the one the Wolfram Language applies.
- <code>[Condition]()[*m*, *b*]</code>, written <code>*m* /; *b*</code>, keeps the results of *m* where the Boolean *b* is `"true"`, and <code>[MatchQ]()[*m*]</code> is whether *m* has a result, a Boolean. Both are definitions of the prelude too. A condition is a Boolean, not a proposition: <code>[Decide]()[*p*]</code> decides a proposition *p*.
- These are the operations of the monad of lists, the monad of nondeterminism, with its alternatives in order. They follow the match objects of the prototype paclet Wolfram/Patterns and of the Match IR of the WolframKernel project's compiler.
- Rules written as a term where a function of the type `Expressions -> Match[Expressions]` is expected, `lhs -> rhs`, `lhs :> rhs` or a list of them, are that function: the match of every way each rule matches, in order. [ReplaceList]() gives that match, [Replace]() its first result, and [ReplaceAll]() and [ReplaceRepeated]() are definitions over such functions too, all of which the kernel computes.
- The rules of a symbol, <code>[TypeTheoryFormalize]()[*f*, "Meaning" -> "Rules"]</code>, are a function from [Expressions]() to `Option[Expressions]` written with these constants.

## Basic Examples

[Match]() takes a type to the type of matches with results in it:

```wl
TypeTheoryType[Match]
```

<!-- => Type u → Type u -->

---

A match is the list of its results:

```wl
TypeTheoryEnvironment["Prelude"][Match]
```

<!-- => definition Match : Type u → Type u := (A ∶ Type u) ↦ {A} -->

---

Rules written as a term are a function from an expression to the match of every way they match it:

```wl
TypeTheoryType[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]]]
```

<!-- => Expressions → Match[Expressions] -->

Applied to `f[1, 2]`, they give a match of expressions:

```wl
TypeTheoryType[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]]]
```

<!-- => Match[Expressions] -->

Both rules match `f[1, 2]`, so the match has two results, in the order of the rules:

```wl
NormalForm[TypeTheoryTerm[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]]]]
```

<!-- => {{2, 1}, {1, 2}} -->

## Scope

[ReplaceList]() gives the match of rules, a list of expressions:

```wl
TypeTheoryType[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}]]
```

<!-- => {Expressions} -->

A pattern of two sequences matches `f[1, 2, 3]` in two ways, the shorter first sequence first:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}]]]
```

<!-- => {{{1}, {2, 3}}, {{1, 2}, {3}}} -->

---

The arguments of an [Orderless]() head match in every order:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[HoldForm[a + b], x_ + y_ :> {x, y}]]]
```

<!-- => {{a, b}, {b, a}} -->

---

[Replace]() rewrites by the first result, so it gives an expression, not a match:

```wl
TypeTheoryType[Replace[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}]]
```

<!-- => Expressions -->

---

A match can have results of any type, here natural numbers:

```wl
TypeTheoryType[Typed[{1, 2}, Match[NonNegativeIntegers]]]
```

<!-- => Match[ℕ] -->

---

[MatchQ]() says whether a match has a result, a Boolean:

```wl
TypeTheoryType[MatchQ]
```

<!-- => ∀_{A ∶ Type u} Match[A] → 𝔹 -->

A rule that does not match gives the match with no result, so [MatchQ]() of it is `"false"`, by computation:

```wl
TypeTheoryProof[MatchQ[Typed[f[x_, y_] :> {y, x}, Expressions -> Match[Expressions]][g[1, 2]]] == "false", {"Reflexivity"}]
```

<!-- => Proof complete -->

---

[Condition]() keeps the results of a match where a Boolean is `"true"`:

```wl
TypeTheoryType[Condition]
```

<!-- => ∀_{A ∶ Type u} Match[A] → 𝔹 → Match[A] -->

Its definition gives the match where the Boolean is `"true"` and no result where it is `"false"`:

```wl
TypeTheoryEnvironment["Prelude"][Condition]
```

<!-- => definition Condition : ∀_{A ∶ Type u} Match[A] → 𝔹 → Match[A] := {A ∶ Type u} (m ∶ Match[A]) (c ∶ 𝔹) ↦ 𝔹_rec[(b ∶ 𝔹) ↦ {A}, {}, m, c] -->

A condition on each result of a match, the numbers that are at least 3, decided by [Decide]():

```wl
TypeTheoryType[MatchBind[{1, 2, 3, 4}, n |-> (MatchValue[n] /; Decide[3 <= n])]]
```

<!-- => Match[ℕ] -->

## Properties and Relations

[ReplaceList]() gives the match of the rules, the same by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}]],
    TypeTheoryTerm[Typed[f[x__, y__] :> {{x}, {y}}, Expressions -> Match[Expressions]][f[1, 2, 3]]]
]
```

<!-- => True -->

---

A match is a list, so its [Length]() is the number of ways a pattern matches, here the four ways to split five arguments in two, by computation:

```wl
TypeTheoryProof[Length[ReplaceList[f[1, 2, 3, 4, 5], f[x__, y__] :> 0]] == 4, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

The rules of a symbol are a function from an expression to the option of the expression it rewrites to:

```wl
area[w_, h_] := w h;
TypeTheoryType["DownValues[area]", TypeTheoryEnvironment[TypeTheoryFormalize[area, "Meaning" -> "Rules"]]]
```

<!-- => Expressions → Option[Expressions] -->

## Possible Issues

A condition is a Boolean, so a proposition does not go after `/;`; <code>[Decide]()[3 <= n]</code> is the Boolean that decides it:

```wl
TypeTheoryType[MatchBind[{1, 2, 3, 4}, n |-> (MatchValue[n] /; 3 <= n)]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The match with no result does not say the type of its results:

```wl
TypeTheoryType[TypeTheoryTerm[{}]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

[Typed]() gives it, and the type is the one it is given, `Match[Expressions]`, the type of lists of expressions:

```wl
TypeTheoryType[Typed[{}, Match[Expressions]]]
```

<!-- => Match[Expressions] -->
