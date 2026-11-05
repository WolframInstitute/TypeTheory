---
Template: Symbol
Name: MatchValue
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchValue
Keywords: [Wolfram Language, pattern matching, Match, one result, value, Sequence]
SeeAlso: [Match, MatchSum, MatchBind, MatchFirst]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[MatchValue]()[*a*] is the match with one result, the value *a*.

## Details & Options

- <code>[MatchValue]()[*a*]</code> has the type <code>[Match]()[*A*]</code> when *a* has the type *A*. It is a constant of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, the list `{a}`.
- A match holds a single value. A sequence of values is one value, written <code>[MatchValue]()[[Sequence]()[*a*, *b*, ...]]</code>, of the type <code>[Match]()[[Sequence]()[*A*, *B*, ...]]</code>. Several results are a [MatchSum]() of matches.
- [MatchValue]() is the unit of the monad of matches: <code>[MatchBind]()[[MatchValue]()[*a*], *f*]</code> is <code>*f*[*a*]</code>.
- The rules of a symbol give the right side of the rule that matches as <code>[MatchValue]()[[HoldForm]()[*rhs*]]</code>, the expression it rewrites to.

## Basic Examples

One result:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType[MatchValue[3], wolfram]
```

<!-- => Match[ℕ] -->

---

The first result of one result is it:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchValue[3]], wolfram]]
```

<!-- => some[3] -->

## Scope

A sequence of values is one result:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType[MatchValue[Sequence[1, "true"]], wolfram]
```

<!-- => Match[[ℕ, 𝔹]] -->

---

Several results are a sum:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchSum[MatchValue[1], MatchValue[2]], wolfram], TypeTheoryTerm[{1, 2}, wolfram]]
```

<!-- => True -->

## Properties and Relations

[MatchBind]() of one result applies the function to it:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[MatchBind[MatchValue[2], Typed[x, NonNegativeIntegers] |-> MatchValue[x + 1]], wolfram], TypeTheoryTerm[MatchValue[3], wolfram]]
```

<!-- => True -->
