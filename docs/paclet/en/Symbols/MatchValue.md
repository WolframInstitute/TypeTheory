---
Template: Symbol
Name: MatchValue
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchValue
Keywords: [Wolfram Language, pattern matching, Match, one result, value, unit, monad, Sequence]
SeeAlso: [Match, MatchSum, MatchBind, MatchFirst, Sequence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchValue]()[*a*]</code> is the match with one result, the value *a*.

## Details & Options

- <code>[MatchValue]()[*a*]</code> has the type <code>[Match]()[*A*]</code> when *a* has the type *A*. It is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, the list `{a}`.
- A match holds a single value. A sequence of values is one value, written <code>[MatchValue]()[[Sequence]()[*a*, *b*, ...]]</code>, of the type <code>[Match]()[[Sequence]()[*A*, *B*, ...]]</code>, and a list is one value too. Several results are a [MatchSum]() of matches.
- [MatchValue]() is the unit of the monad of matches: <code>[MatchBind]()[[MatchValue]()[*a*], *f*]</code> gives the results of <code>*f*[*a*]</code>, and <code>[MatchBind]()[*m*, [MatchValue]()]</code> those of *m*.
- The rules of a symbol give the right side of the rule that matches as <code>[MatchValue]()[[HoldForm]()[*rhs*]]</code>, the expression it rewrites to.

## Basic Examples

The type of [MatchValue]():

```wl
TypeTheoryType[MatchValue, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} A → Match[A] -->

---

One result:

```wl
TypeTheoryType[MatchValue[3], "WolframLanguage"]
```

<!-- => Match[ℕ] -->

---

It is the list of the one result:

```wl
NormalForm[TypeTheoryTerm[MatchValue[3], "WolframLanguage"]]
```

<!-- => {3} -->

---

The first result of one result is it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchValue[3]], "WolframLanguage"]]
```

<!-- => some[3] -->

## Scope

One expression:

```wl
NormalForm[TypeTheoryTerm[MatchValue[Typed[f[1], Expressions]], "WolframLanguage"]]
```

<!-- => {f[1]} -->

---

One quoted expression, as the rules of a symbol give it:

```wl
NormalForm[TypeTheoryTerm[MatchValue[HoldForm[1 + 2]], "WolframLanguage"]]
```

<!-- => {1 + 2} -->

---

One string:

```wl
TypeTheoryType[MatchValue["ab"], "WolframLanguage"]
```

<!-- => Match[Strings] -->

---

A sequence of values is one result:

```wl
TypeTheoryType[MatchValue[Sequence[1, "true"]], "WolframLanguage"]
```

<!-- => Match[[ℕ, 𝔹]] -->

---

It shows in brackets:

```wl
NormalForm[TypeTheoryTerm[MatchValue[Sequence[1, 2]], "WolframLanguage"]]
```

<!-- => {[1, 2]} -->

---

The values of a sequence can have three different types:

```wl
TypeTheoryType[MatchValue[Sequence[1, Typed[f[1], Expressions], "a"]], "WolframLanguage"]
```

<!-- => Match[[ℕ, Expressions, Strings]] -->

---

A sequence of any number of expressions is one result too, as a sequence pattern binds it:

```wl
TypeTheoryType[MatchValue[Typed[Unevaluated[1, 2], Expressions...]], "WolframLanguage"]
```

<!-- => Match[Expressions...] -->

## Properties and Relations

The definition of [MatchValue]():

```wl
TypeTheoryEnvironment["WolframLanguage"][MatchValue]
```

<!-- => definition MatchValue : ∀_{A ∶ Type u} A → Match[A] := {A ∶ Type u} (a ∶ A) ↦ {a} -->

---

[MatchValue]() of a value is the list of it, by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchValue[3], "WolframLanguage"], TypeTheoryTerm[{3}, "WolframLanguage"]]
```

<!-- => True -->

---

[MatchBind]() of one result applies the function to it:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchBind[MatchValue[2], Typed[x, NonNegativeIntegers] |-> MatchValue[x + 1]], "WolframLanguage"], TypeTheoryTerm[MatchValue[3], "WolframLanguage"]]
```

<!-- => True -->

---

[MatchBind]() of a match with [MatchValue]() gives its results back:

```wl
NormalForm[TypeTheoryTerm[MatchBind[Typed[{1, 2}, Match[NonNegativeIntegers]], MatchValue], "WolframLanguage"]]
```

<!-- => {1, 2} -->

---

Several results are a sum:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchSum[MatchValue[1], MatchValue[2]], "WolframLanguage"], TypeTheoryTerm[{1, 2}, "WolframLanguage"]]
```

<!-- => True -->

---

One result is a match:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchQ[MatchValue[1]], "WolframLanguage"]]
```

<!-- => true -->

## Possible Issues

[MatchValue]() takes one value:

```wl
TypeTheoryType[MatchValue[1, 2], "WolframLanguage"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A list is one value, so [MatchValue]() of it is one result, not several:

```wl
NormalForm[TypeTheoryTerm[MatchValue[{1, 2}], "WolframLanguage"]]
```

<!-- => {{1, 2}} -->
