---
Template: Symbol
Name: MatchSum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchSum
Keywords: [Wolfram Language, pattern matching, Match, alternatives, order, several results]
SeeAlso: [Match, MatchValue, MatchBind, MatchFirst]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[MatchSum]()[*m1*, *m2*] is the match whose results are those of *m1*, then those of *m2*.

## Details & Options

- <code>[MatchSum]()[*m1*, *m2*]</code> has the type <code>[Match]()[*A*]</code> when *m1* and *m2* have it. It is a constant of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, the [Join]() of the two lists of results.
- [MatchSum]() is where a match gets several results: the alternatives of a pattern, and the ways a sequence or an [Orderless]() head matches. [MatchValue]() holds one value, and `{}` is the match with no result, the unit of [MatchSum]().
- The alternatives keep their order, so [MatchFirst]() takes a result of *m1* before any of *m2*, as the Wolfram Language applies the first rule that matches.

## Basic Examples

Two alternatives, in order:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchSum[MatchValue[1], MatchValue[2]], wolfram], TypeTheoryTerm[{1, 2}, wolfram]]
```

<!-- => True -->

---

The first result is the left one:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], wolfram]]
```

<!-- => some[1] -->

## Properties and Relations

A match with no result leaves the other's:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchSum[Typed[{}, Match[NonNegativeIntegers]], MatchValue[3]], wolfram], TypeTheoryTerm[MatchValue[3], wolfram]]
```

<!-- => True -->
