---
Template: Symbol
Name: MatchBind
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchBind
Keywords: [Wolfram Language, expressions, pattern matching, Match, bind, monad, parts in turn, several results]
SeeAlso: [Match, MatchValue, MatchSum, MatchPart, MatchFirst, Expressions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchBind]()[*m*, *f*]</code> is the match whose results are those of *f* applied to each result of the match *m*, in order.

## Details & Options

- For *m* of the type <code>[Match]()[*A*]</code> and *f* a function from *A* to <code>[Match]()[*B*]</code>, <code>[MatchBind]()[*m*, *f*]</code> has the type <code>[Match]()[*B*]</code>. It is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, by the recursor of lists: the [Join]() of the results of *f* for each result of *m*.
- A match is the list of its results in the order they are tried, the monad of pattern matching: [MatchBind]() is its bind, the parts of a pattern matched in turn, and [MatchValue]() its unit.
- A result of *m* for which *f* gives no result is left out, so a [Condition]() in *f* keeps the results that pass it, and one for which *f* gives several results gives them all, in order.
- Two matches combine by a [MatchBind]() in each, keeping the two results as one value, such as <code>[MatchValue]()[[Sequence]()[*a*, *b*]]</code>.

## Basic Examples

The type of [MatchBind]():

```wl
TypeTheoryType[MatchBind, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} Match[A] → (A → Match[B]) → Match[B] -->

---

Each result continued by a match of two results:

```wl
NormalForm[TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> {x, x}], "WolframLanguage"]]
```

<!-- => {1, 1, 2, 2} -->

---

One result continued by one result:

```wl
NormalForm[TypeTheoryTerm[MatchBind[MatchValue[2], Typed[x, NonNegativeIntegers] |-> MatchValue[x + 1]], "WolframLanguage"]]
```

<!-- => {3} -->

## Scope

A match with no result gives none:

```wl
NormalForm[TypeTheoryTerm[MatchBind[Typed[{}, Match[NonNegativeIntegers]], Typed[x, NonNegativeIntegers] |-> MatchValue[x + 1]], "WolframLanguage"]]
```

<!-- => {} -->

---

Nor does a continuation with no result:

```wl
NormalForm[TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> Typed[{}, Match[NonNegativeIntegers]]], "WolframLanguage"]]
```

<!-- => {} -->

---

A condition in the continuation keeps the results that pass it:

```wl
NormalForm[TypeTheoryTerm[MatchBind[{1, 2, 3}, Typed[x, NonNegativeIntegers] |-> (MatchValue[x] /; Decide[x == 2])], "WolframLanguage"]]
```

<!-- => {2} -->

---

The results can be of another type:

```wl
NormalForm[TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> MatchValue[Decide[x == 1]]], "WolframLanguage"]]
```

<!-- => {true, false} -->

---

Two matches combine, each pair of results one value:

```wl
NormalForm[TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> MatchBind[{3, 4}, Typed[y, NonNegativeIntegers] |-> MatchValue[Sequence[x, y]]]], "WolframLanguage"]]
```

<!-- => {[1, 3], [1, 4], [2, 3], [2, 4]} -->

---

Each pair is a sequence of two natural numbers:

```wl
TypeTheoryType[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> MatchBind[{3, 4}, Typed[y, NonNegativeIntegers] |-> MatchValue[Sequence[x, y]]]], "WolframLanguage"]
```

<!-- => Match[[ℕ, ℕ]] -->

---

The parts of an expression matched in turn:

```wl
NormalForm[TypeTheoryTerm[MatchBind[MatchPart[f[1, 2], 1, MatchValue], Typed[x, Expressions] |-> MatchPart[f[1, 2], 2, Typed[y, Expressions] |-> MatchValue[Sequence[x, y]]]], "WolframLanguage"]]
```

<!-- => {[1, 2]} -->

## Properties and Relations

The definition of [MatchBind]():

```wl
TypeTheoryEnvironment["WolframLanguage"][MatchBind]
```

<!-- => definition MatchBind : ∀_{A ∶ Type u} ∀_{B ∶ Type v} Match[A] → (A → Match[B]) → Match[B] := {A ∶ Type u} {B ∶ Type v} (m ∶ Match[A]) (f ∶ A → Match[B]) ↦ List_rec[(t ∶ {A}) ↦ {B}, {}, (x ∶ A) (rest ∶ {A}) (r ∶ {B}) ↦ Join[f[x], r], m] -->

---

[MatchValue]() is a unit on the left:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchBind[MatchValue[2], Typed[x, NonNegativeIntegers] |-> MatchValue[x + 1]], "WolframLanguage"], TypeTheoryTerm[MatchValue[3], "WolframLanguage"]]
```

<!-- => True -->

---

And on the right:

```wl
NormalForm[TypeTheoryTerm[MatchBind[Typed[{1, 2}, Match[NonNegativeIntegers]], MatchValue], "WolframLanguage"]]
```

<!-- => {1, 2} -->

---

Binds associate:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[MatchBind[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> {x, x + 10}], Typed[y, NonNegativeIntegers] |-> MatchValue[2 y]], "WolframLanguage"],
    TypeTheoryTerm[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> MatchBind[{x, x + 10}, Typed[y, NonNegativeIntegers] |-> MatchValue[2 y]]], "WolframLanguage"]
]
```

<!-- => True -->

---

A bind of a sum continues each alternative:

```wl
NormalForm[TypeTheoryTerm[MatchBind[MatchSum[MatchValue[1], MatchValue[2]], Typed[x, NonNegativeIntegers] |-> MatchValue[x + 10]], "WolframLanguage"]]
```

<!-- => {11, 12} -->

## Possible Issues

The continuation gives a match, not a value:

```wl
TypeTheoryType[MatchBind[{1, 2}, Typed[x, NonNegativeIntegers] |-> x + 1], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->
