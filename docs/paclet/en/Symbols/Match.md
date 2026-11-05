---
Template: Symbol
Name: Match
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Match
Keywords: [Wolfram Language, pattern matching, Match, monad, nondeterminism, list of results]
SeeAlso: [MatchValue, MatchSum, MatchBind, MatchPart, MatchFirst, Expressions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[Match]()[*A*] is the type of the matches with results in *A*: the list of their results, none, one or several, in the order they are tried.

## Details & Options

- [Match]() is a constant of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, defined as `{A}`, the type of lists, so a match is a list and computes as one.
- A match has no result where the pattern does not match, one where it matches once, and several where it matches in several ways, as a pattern with an [Orderless]() head or a sequence pattern does.
- [MatchValue]() makes one result and `{}` none; [MatchSum]() puts alternatives in order, where every match with several results comes from; [MatchBind]() matches parts in turn; [Condition]() keeps the results where a Boolean holds; [MatchPart]() matches at a part of an expression; [MatchFirst]() takes the first result, the one the Wolfram Language applies.
- These are the operations of the monad of lists, the monad of nondeterminism, with its alternatives in order. They follow the match objects of the prototype paclet Wolfram/Patterns and of the Match IR of the WolframKernel project's compiler.
- The rules of a symbol, <code>[TypeTheoryFormalize]()[*f*, *env*, "Meaning" -> "Rules"]</code>, are a function from [Expressions]() to `Option[Expressions]` written with these constants.

## Basic Examples

The type of matches of natural numbers:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType[Match[NonNegativeIntegers], wolfram]
```

<!-- => Type -->

---

A match is the list of its results:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchSum[MatchValue[1], MatchValue[2]], wolfram], TypeTheoryTerm[{1, 2}, wolfram]]
```

<!-- => True -->

## Possible Issues

[Match]() is a constant of the Wolfram Language environment only, not of the prelude:

```wl
TypeTheoryType[Match[NonNegativeIntegers]]
```

<!-- => Failure["ElaborationFailed", ...] -->
