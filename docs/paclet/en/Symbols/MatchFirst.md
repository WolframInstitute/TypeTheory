---
Template: Symbol
Name: MatchFirst
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchFirst
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [MatchBind, Option]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[MatchFirst]()[*m*] is the first result of the match *m*, [OptionSome]() of it, or [OptionNone]() where *m* has none.

## Details & Options

- The first result is the rule that the Wolfram Language applies, and none is an expression that no rule matches, which stays as it is.
- `MatchSum` keeps its alternatives in order, so [MatchFirst]() of it takes the left one first.

## Basic Examples

The left alternative first:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"]
```

<!-- => TypeTheoryEnvironment summary box -->

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchFirst[MatchSum[MatchValues[1], MatchValues[2]]], wolfram], TypeTheoryTerm[OptionSome[1], wolfram]]
```

<!-- => True -->
