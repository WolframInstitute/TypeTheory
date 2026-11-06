---
Template: Symbol
Name: MatchFirst
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchFirst
Keywords: [Wolfram Language, expressions, pattern matching, Match, first result, Option, rules, Replace, DownValues, Longest, prelude]
SeeAlso: [Match, MatchValue, MatchSum, MatchBind, Option, TypeTheoryFormalize, Replace]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchFirst]()[*m*]</code> is the first result of the match *m*, `"some"` of it, or `"none"` where *m* has none.

## Details & Options

- For *m* of the type <code>[Match]()[*A*]</code>, <code>[MatchFirst]()[*m*]</code> has the type <code>[Option]()[*A*]</code>. It is a definition of the prelude, by the recursor of lists.
- The first result is the rule that the Wolfram Language applies, and none is an expression that no rule matches, which stays as it is. [Replace]() is the first result of its rules, or the expression where they have none, so it gives an expression, not an option.
- [MatchSum]() keeps its alternatives in order, so [MatchFirst]() of it takes the left one first.
- The rules of a symbol, from <code>[TypeTheoryFormalize]()[*f*, "Meaning" -> "Rules"]</code>, are [MatchFirst]() of the [MatchSum]() of the matches of each rule.

## Basic Examples

The first result of a match is an option:

```wl
TypeTheoryType[MatchFirst]
```

<!-- => ∀_{A ∶ Type u} Match[A] → Option[A] -->

---

The first result of the matches of rules is an option of an expression:

```wl
TypeTheoryType[MatchFirst[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]]]]
```

<!-- => Option[Expressions] -->

Both rules match `f[1, 2]`, and the first result is the first rule's:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]]]]]
```

<!-- => some[{2, 1}] -->

## Scope

A match of natural numbers has a natural number first:

```wl
TypeTheoryType[MatchFirst[Typed[{1, 2}, Match[NonNegativeIntegers]]]]
```

<!-- => Option[ℕ] -->

---

[Replace]() takes the first result, or the expression where there is none, so it gives an expression:

```wl
TypeTheoryType[Replace]
```

<!-- => Expressions → (Expressions → Match[Expressions]) → Expressions -->

---

Of the ways a sequence pattern matches, the shortest first sequence comes first; [Longest]() puts the longest first, so [Replace]() takes it:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2, 3], f[Longest[x__], y__] :> {{x}, {y}}]]]
```

<!-- => {{1, 2}, {3}} -->

## Applications

The rules of a function, read by [TypeTheoryFormalize]():

```wl
swapped[x_, y_] := {y, x};
swapped[x_, y__] := {{y}, x};
swapping = TypeTheoryEnvironment[TypeTheoryFormalize[swapped, "Meaning" -> "Rules"]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

They are the first result of the sum of the rules, an option of an expression:

```wl
swapping["DownValues[swapped]"]
```

<!-- => definition DownValues[swapped] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchSum[...]] -->

An expression with one argument matches neither rule, so it stays as it is:

```wl
NormalForm[TypeTheoryTerm["DownValues[swapped]"[swapped[1]], swapping]]
```

<!-- => none -->

## Properties and Relations

The definition of [MatchFirst]():

```wl
TypeTheoryEnvironment["Prelude"][MatchFirst]
```

<!-- => definition MatchFirst : ∀_{A ∶ Type u} Match[A] → Option[A] := {A ∶ Type u} (m ∶ Match[A]) ↦ List_rec[(t ∶ {A}) ↦ Option[A], none, (x ∶ A) (rest ∶ {A}) (r ∶ Option[A]) ↦ some[x], m] -->

---

[Replace]() takes the first result of its rules, or the expression where there is none, by the recursor of [Option]():

```wl
TypeTheoryEnvironment["Prelude"][Replace]
```

<!-- => definition Replace : Expressions → (Expressions → Match[Expressions]) → Expressions := (e ∶ Expressions) (rules ∶ Expressions → Match[Expressions]) ↦ (Option_rec)[(o ∶ Option[Expressions]) ↦ Expressions, e, (r ∶ Expressions) ↦ r, MatchFirst[rules[e]]] -->

---

Whatever the right alternative, the first result of a sum is the left one's where it has one:

```wl
TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[m, Match[NonNegativeIntegers]]}, MatchFirst[MatchSum[MatchValue[a], m]] == "some"[a]], {"Introduce"[a, m], "Reflexivity"}]
```

<!-- => Proof complete -->

## Possible Issues

The first result is an option, not the expression itself, so a function of expressions does not take it:

```wl
TypeTheoryType[Head[MatchFirst[ReplaceList[f[1, 2], f[x_, y_] :> {y, x}]]]]
```

<!-- => Failure["TypeMismatch", ...] -->

[Replace]() gives the expression:

```wl
TypeTheoryType[Head[Replace[f[1, 2], f[x_, y_] :> {y, x}]]]
```

<!-- => Expressions -->
