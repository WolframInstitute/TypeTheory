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

In [TypeTheoryEnvironment]()["WolframLanguage"], a pattern is a function from an expression to its matches, the [Match]() of every way it matches, in the order the Wolfram Language tries them. Rules are such functions, and [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated]() are definitions over them. An atom is data, a symbol by its name, so heads, literals and [SameQ]() compute, and the kernel rewrites as the Wolfram Language does. Every pattern translates but [KeyValuePattern](), and a condition or a pattern test is the one part that only the Wolfram Language evaluates.

## Rules and Replace

The environment of expressions:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"]
```

<!-- => TypeTheoryEnvironment summary box -->

[Replace]() rewrites an expression by the first rule that matches it, and [NormalForm]() computes the result. `f` names nothing in the environment, so where an expression is expected `f[1, 2]` stands for itself, as a symbol without a value does in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_] :> {y, x}], wolfram]]
```

<!-- => HoldForm[{2, 1}] -->

An expression that no rule matches stays as it is:

```wl
NormalForm[TypeTheoryTerm[Replace[g[1, 2], f[x_, y_] :> {y, x}], wolfram]]
```

<!-- => HoldForm[g[1, 2]] -->

The rules are a function from an expression to its matches:

```wl
TypeTheoryType[Typed[{f[x_, y_] :> {y, x}, f[x_] :> x}, Expressions -> Match[Expressions]], wolfram]
```

<!-- => Expressions → Match[Expressions] -->

[ReplaceList]() gives every result, in order: here every split of the arguments into two sequences, the shortest first:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], wolfram]]
```

<!-- => {HoldForm[{{1}, {2, 3}}], HoldForm[{{1, 2}, {3}}]} -->

## Patterns, Construct by Construct

Each pattern is translated to matches: a blank by a test of a head, a sequence by every split, alternatives by a [MatchSum](), an [Orderless]() head by every order. A blank with a head, and a literal:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, "a"], f[x_Integer, y_String] :> {y, x}], wolfram]]
```

<!-- => HoldForm[{"a", 1}] -->

A name met twice matches the same expression twice:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 1, 2], f[x_, x_, y_] :> y], wolfram]]
```

<!-- => {HoldForm[2]} -->

A sequence takes a run of arguments, each split tried, the shortest first, and [Longest]() the longest first:

```wl
{
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y___] :> {{x}, {y}}], wolfram]],
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[Longest[x__], y___] :> {{x}, {y}}], wolfram]]
}
```

<!-- => {{HoldForm[{{1}, {2, 3}}], HoldForm[{{1, 2}, {3}}], HoldForm[{{1, 2, 3}, {}}]}, {HoldForm[{{1, 2, 3}, {}}], HoldForm[{{1, 2}, {3}}], HoldForm[{{1}, {2, 3}}]}} -->

[Repeated]() takes a run whose every element matches:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2, a], f[x : Repeated[_Integer], y___] :> {{x}, {y}}], wolfram]]
```

<!-- => HoldForm[{{1}, {2, a}}] -->

[Alternatives]() are tried in order, and [Except]() matches what its pattern does not:

```wl
{
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, "a", b], f[___, x : (_Integer | _String), ___] :> x], wolfram]],
    NormalForm[TypeTheoryTerm[ReplaceList[f[1, "a", b], f[___, x : Except[_Integer], ___] :> x], wolfram]]
}
```

<!-- => {{HoldForm[1], HoldForm["a"]}, {HoldForm["a"], HoldForm[b]}} -->

An [Optional]() argument is given or left out for its default:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[f[1], f[x_, y_ : 0] :> {x, y}], wolfram]],
    NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_ : 0] :> {x, y}], wolfram]]
}
```

<!-- => {HoldForm[{1, 0}], HoldForm[{1, 2}]} -->

[PatternSequence]() matches a run of arguments in turn, and [OrderlessPatternSequence]() in any order:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[f[1, 2, 3], f[PatternSequence[a_, b_], c___] :> {{a, b}, {c}}], wolfram]],
    NormalForm[TypeTheoryTerm[Replace[f["a", 1], f[OrderlessPatternSequence[x_Integer, y_String]] :> {x, y}], wolfram]]
}
```

<!-- => {HoldForm[{{1, 2}, {3}}], HoldForm[{1, "a"}]} -->

The arguments of an [Orderless]() head match in every order, and those of a [Flat]() head in runs wrapped in the head, as [Plus]() has both. [Plus]() is a constant of the environment, the addition of natural numbers, so the expression is quoted with [HoldForm]() to keep it from computing:

```wl
NormalForm[TypeTheoryTerm[Replace[HoldForm[a + b + 1], x_ + 1 :> x], wolfram]]
```

<!-- => HoldForm[a + b] -->

[Verbatim]() matches a pattern as an expression, and [HoldPattern]() matches by the pattern inside it:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[f[_], f[Verbatim[_]] :> "blank"], wolfram]],
    NormalForm[TypeTheoryTerm[Replace[f[1], f[Verbatim[_]] :> "blank"], wolfram]]
}
```

<!-- => {HoldForm["blank"], HoldForm[f[1]]} -->

A condition, `x_ /; test`, and a pattern test, `x_?test`, are [SameQ]() of the [ExpressionValue]() of the test and `True`, which only the Wolfram Language evaluates: a rewriting by one computes in the kernel up to that test.

## ReplaceAll and ReplaceRepeated

[ReplaceAll]() rewrites each part by the first rule that matches it, from the whole expression down, the parts of a part rewritten no further:

```wl
NormalForm[TypeTheoryTerm[ReplaceAll[f[a, g[a]], a -> b], wolfram]]
```

<!-- => HoldForm[f[b, g[b]]] -->

[ReplaceRepeated]() rewrites again until the expression no longer changes, at most 65536 times, the default of [MaxIterations](), so it is a total function:

```wl
NormalForm[TypeTheoryTerm[ReplaceRepeated[f[f[f[x]]], f[y_] :> y], wolfram]]
```

<!-- => HoldForm[x] -->

The right side of a rule is quoted: the rules rewrite, and arithmetic in a right side stays as it is written, for the Wolfram Language to evaluate:

```wl
NormalForm[TypeTheoryTerm[ReplaceAll[HoldForm[d[x^3]], d[x^n_] :> n x^(n - 1)], wolfram]]
```

<!-- => HoldForm[3 x^(3 - 1)] -->

## Expressions Where Expressions Are Expected

Where an expression is expected, a term is evaluated as the Wolfram Language evaluates one: a symbol that names nothing stands for itself, and a constant computes. `1 + 2` is the addition of natural numbers, 3, which the rule matches; [HoldForm]() keeps it from computing, as it does in the Wolfram Language:

```wl
{
    NormalForm[TypeTheoryTerm[Replace[1 + 2, 3 -> "three"], wolfram]],
    NormalForm[TypeTheoryTerm[Replace[HoldForm[1 + 2], 3 -> "three"], wolfram]]
}
```

<!-- => {HoldForm["three"], HoldForm[1 + 2]} -->

## The Rules of a Symbol

The rules of a function, its [DownValues](), are its own match function, read by [TypeTheoryFormalize]() with `"Meaning" -> "Rules"`: the first rule that matches, in the order the Wolfram Language tries them, [MatchFirst]() of the [MatchSum]() of the rules:

```wl
swapped[x_, y_] := {y, x};
swapped[x_, y__] := {{y}, x};
swapping = TypeTheoryEnvironment[wolfram, TypeTheoryFormalize[swapped, wolfram, "Meaning" -> "Rules"]];
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

<!-- => {some[HoldForm[{2, 1}]], some[HoldForm[{{2, 3}, 1}]], none} -->

## Possible Issues

An [Association]() is an atom, so [KeyValuePattern]() does not translate:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1], KeyValuePattern["a" -> x_] :> x], wolfram]]
```

<!-- => Failure["ElaborationFailed", ...] -->
