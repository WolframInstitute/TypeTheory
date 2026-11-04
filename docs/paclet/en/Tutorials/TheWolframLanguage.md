---
Template: TechNote
Name: TheWolframLanguage
Title: The Wolfram Language
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TheWolframLanguage
Keywords: [Wolfram Language, expressions, Sequence, pattern matching, Match, MatchSum, MatchProduct, monad, nondeterminism, Option, Wolfram/Patterns, Match IR]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, ThePrelude, TypeTheoryIntroduction]
---

[TypeTheoryEnvironment]()["WolframLanguage"] is the prelude with the expressions of the Wolfram Language as an inductive type, and with the monad of pattern matching. A pattern is a function from expressions to its matches, and a definition is the first match of its rules, so a Wolfram Language function has a meaning in the type theory: a total function, whose value is an [Option]() that is none where no rule matches and the expression stays as it is.

## Expressions

An expression is an atom, a symbol, a number or a string, which has no parts, or a head applied to a [Sequence]() of expressions, its arguments. The atoms are opaque, and [SameQ]() and [Head]() of an atom are axioms that the Wolfram Language computes. A natural number is an expression where one is expected:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeOf[TypeTheoryTerm[ExpressionNormal[7, {1, 2}], wolfram]]
```

<!-- => Expressions -->

[Arguments]() gives the [Sequence]() of an expression's arguments:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Arguments[ExpressionNormal[7, {1, 2}]], wolfram], TypeTheoryTerm[Typed[{1, 2}, Sequence], wolfram]]
```

<!-- => True -->

## The Monad of Matches

`Match[A]` is the list of the results of a match, in the order they are tried: none, one, or several, as a pattern with an [Orderless]() head or a sequence matches in several ways. It types the match objects of the paclet Wolfram/Patterns, whose symbols `Match`, `MatchValues`, `MatchSum`, `MatchProduct` and `MatchPart` name its constants. The compiler of the WolframKernel project built its Match IR from the same objects:

| | Wolfram/Patterns | the Match IR | in the type theory |
|---|---|---|---|
| one result | `MatchValues` | `Values` | `MatchValues[a] : Match[A]` |
| no result | | `Sum[]` | `EmptyList` |
| alternatives, in order | `MatchSum` | `Sum` | `MatchSum : Match[A] -> Match[A] -> Match[A]` |
| independent parts | `MatchProduct` | `Product` | `MatchProduct : Match[A] -> Match[B] -> Match[A × B]` |
| parts in turn | | `Product` | [MatchBind]()` : Match[A] -> (A -> Match[B]) -> Match[B]` |
| a match at a position | `MatchPart` | `Part` | `MatchPart : Expressions -> ℕ -> (Expressions -> Match[A]) -> Match[A]` |
| a condition | | `Guard` | [Condition]()` : Match[A] -> Booleans -> Match[A]` |
| the rule applied | the first result | the leftmost result | [MatchFirst]()` : Match[A] -> Option[A]` |

These are the operations of the monad of lists, the monad of nondeterminism, with its alternatives in order. The environment puts the context of Wolfram/Patterns at the end of the context path, so its symbols are written without it.

The alternatives keep their order, so the first result is the left one, as the Wolfram Language applies the first rule that matches:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchFirst[MatchSum[MatchValues[1], MatchValues[2]]], wolfram], TypeTheoryTerm[OptionSome[1], wolfram]]
```

<!-- => True -->

A match with no result gives none, the expression left as it is:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchFirst[Typed[EmptyList, Match[NonNegativeIntegers]]], wolfram], TypeTheoryTerm[Typed[OptionNone, Option[NonNegativeIntegers]], wolfram]]
```

<!-- => True -->

A product pairs every result of one match with every result of another, in order, as the independent parts of a pattern combine:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchProduct[{1, 2}, {3}], wolfram], TypeTheoryTerm[{Pair[1, 3], Pair[2, 3]}, wolfram]]
```

<!-- => True -->

`MatchPart` matches at the part of an expression at a position, its head at 0, with no result out of range, where [Part]() fails:

```wl
{
    DefinitionallyEqualQ[TypeTheoryTerm[MatchPart[ExpressionNormal[7, {1, 2}], 2, MatchValues], wolfram], TypeTheoryTerm[MatchValues[Typed[2, Expressions]], wolfram]],
    DefinitionallyEqualQ[TypeTheoryTerm[MatchPart[ExpressionNormal[7, {1}], 5, MatchValues], wolfram], TypeTheoryTerm[Typed[EmptyList, Match[Expressions]], wolfram]]
}
```

<!-- => {True, True} -->
