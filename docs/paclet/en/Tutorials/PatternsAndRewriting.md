---
Template: TechNote
Name: PatternsAndRewriting
Title: Patterns and Rewriting
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/PatternsAndRewriting
Keywords: [patterns, rules, rewriting, Replace, ReplaceList, ReplaceAll, ReplaceRepeated, Match, sequences, Orderless, Optional, Longest, Wolfram Language]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration, TypeTheoryIntroduction]
---

In the prelude, a pattern is a function from an expression to its matches, the [Match]() of every way it matches, in the order the Wolfram Language tries them. Rules are such functions, and [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated]() are definitions over them. An atom is data, a symbol by its name, so heads, literals and [SameQ]() compute, and the kernel rewrites as the Wolfram Language does. Every pattern translates but [KeyValuePattern](), and a condition or a pattern test is the one part that only the Wolfram Language evaluates.

## Rules and Replace

[Replace]() is a definition of the prelude: it takes an expression and rules, a function from an expression to its matches, and gives an expression:

```wl
TypeTheoryType[Replace]
```

<!-- => Expressions → (Expressions → Match[Expressions]) → Expressions -->

[ReplaceList]() gives the list of every result instead:

```wl
TypeTheoryType[ReplaceList]
```

<!-- => Expressions → (Expressions → Match[Expressions]) → {Expressions} -->

A rewrite is a term like any other, of the type of its result:

```wl
TypeTheoryType[Replace[f[1, 2], f[x_, y_] :> {y, x}]]
```

<!-- => Expressions -->

[Replace]() rewrites an expression by the first rule that matches it, and [NormalForm]() computes the result. `f` names nothing in the environment, so where an expression is expected `f[1, 2]` stands for itself, as a symbol without a value does in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_] :> {y, x}]]]
```

<!-- => {2, 1} -->

An expression that no rule matches stays as it is:

```wl
NormalForm[TypeTheoryTerm[Replace[g[1, 2], f[x_, y_] :> {y, x}]]]
```

<!-- => g[1, 2] -->

The rules are a function from an expression to its matches:

```wl
TypeTheoryType[Typed[{f[x_, y_] :> {y, x}, f[x_] :> x}, Expressions -> Match[Expressions]]]
```

<!-- => Expressions → Match[Expressions] -->

[ReplaceList]() gives every result, in order: here every split of the arguments into two sequences, the shortest first:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}]]]
```

<!-- => {{{1}, {2, 3}}, {{1, 2}, {3}}} -->

## Patterns, Construct by Construct

Each pattern is translated to matches: a blank by a test of a head, a sequence by every split, alternatives by a [MatchSum](), an [Orderless]() head by every order. A blank with a head, and a literal:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, "a"], f[x_Integer, y_String] :> {y, x}]]]
```

<!-- => {"a", 1} -->

A name met twice matches the same expression twice:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 1, 2], f[x_, x_, y_] :> y]]]
```

<!-- => {2} -->

A sequence takes a run of arguments, each split tried, the shortest first, and [Longest]() the longest first:

```wl
{
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y___] :> {{x}, {y}}]]],
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[Longest[x__], y___] :> {{x}, {y}}]]]
}
```

<!-- => {{{{1}, {2, 3}}, {{1, 2}, {3}}, {{1, 2, 3}, {}}}, {{{1, 2, 3}, {}}, {{1, 2}, {3}}, {{1}, {2, 3}}}} -->

[Repeated]() takes a run whose every element matches:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2, a], f[x : Repeated[_Integer], y___] :> {{x}, {y}}]]]
```

<!-- => {{1}, {2, a}} -->

[Alternatives]() are tried in order, and [Except]() matches what its pattern does not:

```wl
{
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, "a", b], f[___, x : (_Integer | _String), ___] :> x]]],
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, "a", b], f[___, x : Except[_Integer], ___] :> x]]]
}
```

<!-- => {{1, "a"}, {"a", b}} -->

An [Optional]() argument is given or left out for its default:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[f[1], f[x_, y_ : 0] :> {x, y}]]],
    NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_ : 0] :> {x, y}]]]
}
```

<!-- => {{1, 0}, {1, 2}} -->

[PatternSequence]() matches a run of arguments in turn, and [OrderlessPatternSequence]() in any order:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[f[1, 2, 3], f[PatternSequence[a_, b_], c___] :> {{a, b}, {c}}]]],
    NormalForm[TypeTheoryTerm[Replace[f["a", 1], f[OrderlessPatternSequence[x_Integer, y_String]] :> {x, y}]]]
}
```

<!-- => {{{1, 2}, {3}}, {1, "a"}} -->

The arguments of an [Orderless]() head match in every order, and those of a [Flat]() head in runs wrapped in the head, as [Plus]() has both. [Plus]() is a constant of the environment, the addition of natural numbers, so the expression is quoted with [Unevaluated]() to keep it from computing:

```wl
NormalForm[TypeTheoryTerm[Replace[Unevaluated[a + b + 1], x_ + 1 :> x]]]
```

<!-- => a + b -->

[Verbatim]() matches a pattern as an expression, and [HoldPattern]() matches by the pattern inside it:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[f[_], f[Verbatim[_]] :> "blank"]]],
    NormalForm[TypeTheoryTerm[Replace[f[1], f[Verbatim[_]] :> "blank"]]]
}
```

<!-- => {"blank", f[1]} -->

A condition, `x_ /; test`, and a pattern test, `x_?test`, are [SameQ]() of the [ExpressionEvaluate]() of the test and `True`, which only the Wolfram Language evaluates: a rewriting by one computes in the kernel up to that test.

## ReplaceAll and ReplaceRepeated

[ReplaceAll]() rewrites each part by the first rule that matches it, from the whole expression down, the parts of a part rewritten no further:

```wl
NormalForm[TypeTheoryTerm[ReplaceAll[f[a, g[a]], a -> b]]]
```

<!-- => f[b, g[b]] -->

[ReplaceRepeated]() rewrites again until the expression no longer changes, at most 65536 times, the default of [MaxIterations](), so it is a total function:

```wl
NormalForm[TypeTheoryTerm[ReplaceRepeated[f[f[f[x]]], f[y_] :> y]]]
```

<!-- => x -->

The right side of a rule is quoted: the rules rewrite, and arithmetic in a right side stays as it is written, for the Wolfram Language to evaluate:

```wl
NormalForm[TypeTheoryTerm[ReplaceAll[Unevaluated[d[x^3]], d[x^n_] :> n x^(n - 1)]]]
```

<!-- => 3 x^(3 - 1) -->

## Expressions Where Expressions Are Expected

Where an expression is expected, a term is evaluated as the Wolfram Language evaluates one: a symbol that names nothing stands for itself, and a constant computes. `1 + 2` is the addition of natural numbers, 3, which the rule matches; [Unevaluated]() keeps it from computing, as it does in the Wolfram Language:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[1 + 2, 3 -> "three"]]],
    NormalForm[TypeTheoryTerm[Replace[Unevaluated[1 + 2], 3 -> "three"]]]
}
```

<!-- => {"three", 1 + 2} -->

## The Rules of a Symbol

The rules of a function, its [DownValues](), are its own match function, read by [TypeTheoryFormalize]() with `"Meaning" -> "Rules"`: the first rule that matches, in the order the Wolfram Language tries them, [MatchFirst]() of the [MatchSum]() of the rules:

```wl
swapped[x_, y_] := {y, x};
swapped[x_, y__] := {{y}, x};
swapping = TypeTheoryEnvironment[TypeTheoryFormalize[swapped, "Meaning" -> "Rules"]];
swapping["DownValues[swapped]"]
```

<!-- => definition DownValues[swapped] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchSum[...]] -->

The kernel computes which rule applies:

```wl
{
    NormalForm[TypeTheoryTerm["DownValues[swapped]"[swapped[1, 2]], swapping]],
    NormalForm[TypeTheoryTerm["DownValues[swapped]"[swapped[1, 2, 3]], swapping]],
    NormalForm[TypeTheoryTerm["DownValues[swapped]"[swapped[1]], swapping]]
}
```

<!-- => {some[{2, 1}], some[{{2, 3}, 1}], none} -->

## Possible Issues

An [Association]() is an atom, so [KeyValuePattern]() does not translate:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1], KeyValuePattern["a" -> x_] :> x]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
