---
Template: Symbol
Name: MatchPart
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchPart
Keywords: [Wolfram Language, pattern matching, Match, part, position, head, arguments]
SeeAlso: [Match, MatchValue, MatchBind, Expressions, Arguments]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[MatchPart]()[*e*, *k*, *f*] is the match *f* of the part of the expression *e* at the position *k*: 0 its head, and *k* its *k*-th argument.

## Details & Options

- *e* is an [Expressions](), *k* a natural number and *f* a function from [Expressions]() to <code>[Match]()[*A*]</code>; the result is a <code>[Match]()[*A*]</code>. It is a constant of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>.
- Where *e* has no part at *k*, an atom past 0 or an expression with fewer arguments, the match has no result, where [Part]() fails.
- The rules of a symbol match each part of the left side with [MatchPart](), one inside another for a part of a part, as the instructions of a match program reach parts by their paths.

## Basic Examples

The second argument of an expression, as one result:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchPart["construct"[7, 1, 2], 2, MatchValue], wolfram], TypeTheoryTerm[MatchValue[Typed[2, Expressions]], wolfram]]
```

<!-- => True -->

---

Position 0 is the head:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchPart["construct"[7, 1], 0, MatchValue], wolfram], TypeTheoryTerm[MatchValue[Typed[7, Expressions]], wolfram]]
```

<!-- => True -->

## Possible Issues

A position out of range gives no result:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchPart["construct"[7, 1], 5, MatchValue], wolfram], TypeTheoryTerm[Typed[{}, Match[Expressions]], wolfram]]
```

<!-- => True -->
