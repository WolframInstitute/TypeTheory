---
Template: Symbol
Name: MatchBind
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchBind
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Match, MatchValue, MatchSum, MatchPart, MatchFirst, Expressions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[MatchBind]()[*m*, *f*] is the match whose results are those of *f* applied to each result of the match *m*, in order.

## Details & Options

- A match, <code>[Match]()[*A*]</code>, is the list of its results in the order they are tried, the monad of pattern matching of [TypeTheoryEnvironment]()["WolframLanguage"]; [MatchBind]() is its bind, the parts of a pattern matched in turn, and [MatchValue]() its unit.
- Two independent matches combine by a [MatchBind]() in each, keeping the two results as one value, such as <code>[MatchValue]()[[Sequence]()[*a*, *b*]]</code>.

## Basic Examples

Each result continued by a match of two results:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> {x, x}], wolfram], TypeTheoryTerm[{1, 1, 2, 2}, wolfram]]
```

<!-- => True -->
