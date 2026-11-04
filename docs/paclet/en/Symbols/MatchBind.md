---
Template: Symbol
Name: MatchBind
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchBind
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [MatchFirst, Expressions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[MatchBind]()[*m*, *f*] is the match whose results are those of *f* applied to each result of the match *m*, in order.

## Details & Options

- A match, `Match[A]`, is the list of its results in the order they are tried, the monad of pattern matching of [TypeTheoryEnvironment]()["WolframLanguage"]; [MatchBind]() is its bind, the parts of a pattern matched in turn.
- `MatchProduct`, which pairs the results of two independent matches, is a [MatchBind]() in each.

## Basic Examples

Each result continued by a match of two results:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> {x, x}], wolfram], TypeTheoryTerm[{1, 1, 2, 2}, wolfram]]
```

<!-- => True -->
