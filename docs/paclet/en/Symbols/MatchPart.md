---
Template: Symbol
Name: MatchPart
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchPart
Keywords: [Wolfram Language, pattern matching, Match, part, position, head, arguments, Part, match program]
SeeAlso: [Match, MatchValue, MatchBind, Expressions, Arguments, Part]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchPart]()[*e*, *k*, *f*]</code> is the match *f* of the part of the expression *e* at the position *k*: 0 its head, and *k* its *k*-th argument.

## Details & Options

- *e* is an [Expressions](), *k* a natural number and *f* a function from [Expressions]() to <code>[Match]()[*A*]</code>; the result is a <code>[Match]()[*A*]</code>. It is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, which the kernel computes.
- The part at 0 is <code>[Head]()[*e*]</code>, and the part at *k* is the *k*-th element of <code>{[Arguments]()[*e*]}</code>.
- Where *e* has no part at *k*, an atom past 0 or an expression with fewer arguments, the match has no result, where [Part]() fails.
- The rules of a symbol match each part of the left side with [MatchPart](), one inside another for a part of a part, as the instructions of a match program reach parts by their paths.

## Basic Examples

The type of [MatchPart]():

```wl
TypeTheoryType[MatchPart, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} Expressions → ℕ → (Expressions → Match[A]) → Match[A] -->

---

The second argument of an expression, as one result:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 2, MatchValue], "WolframLanguage"]]
```

<!-- => {2} -->

---

Position 0 is the head:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 0, MatchValue], "WolframLanguage"]]
```

<!-- => {f} -->

## Scope

The first argument:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 1, MatchValue], "WolframLanguage"]]
```

<!-- => {1} -->

---

The match of the part can compute with it:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 2, Typed[x, Expressions] |-> MatchValue[Head[x]]], "WolframLanguage"]]
```

<!-- => {Integer} -->

---

It can have several results:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 2, Typed[x, Expressions] |-> {x, x}], "WolframLanguage"]]
```

<!-- => {2, 2} -->

---

A part that passes a test:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 1, Typed[x, Expressions] |-> (MatchValue[x] /; SameQ[x, 1])], "WolframLanguage"]]
```

<!-- => {1} -->

---

A part that fails it gives no result:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 1, Typed[x, Expressions] |-> (MatchValue[x] /; SameQ[x, 2])], "WolframLanguage"]]
```

<!-- => {} -->

---

A part of a part:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[g[1]], 1, Typed[x, Expressions] |-> MatchPart[x, 1, MatchValue]], "WolframLanguage"]]
```

<!-- => {1} -->

---

The head of a list:

```wl
NormalForm[TypeTheoryTerm[MatchPart[{a, b}, 0, MatchValue], "WolframLanguage"]]
```

<!-- => {List} -->

---

A part of a quoted expression:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[a + b], 2, MatchValue], "WolframLanguage"]]
```

<!-- => {b} -->

---

An atom has a head:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[f], 0, MatchValue], "WolframLanguage"]]
```

<!-- => {Symbol} -->

---

A part of an expression built from a sequence:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[s, Expressions...]}, MatchPart[Construct[f, s], 3, MatchValue]][1, 2, 3], "WolframLanguage"]]
```

<!-- => {3} -->

## Properties and Relations

The part at 0 is the head, for every expression:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[e, Expressions] |-> MatchPart[e, 0, MatchValue], "WolframLanguage"], TypeTheoryTerm[Typed[e, Expressions] |-> MatchValue[Head[e]], "WolframLanguage"]]
```

<!-- => True -->

---

Two parts matched in turn with [MatchBind]():

```wl
NormalForm[TypeTheoryTerm[MatchBind[MatchPart[f[1, 2], 1, MatchValue], Typed[x, Expressions] |-> MatchPart[f[1, 2], 2, Typed[y, Expressions] |-> MatchValue[Sequence[x, y]]]], "WolframLanguage"]]
```

<!-- => {[1, 2]} -->

---

The first result is the part:

```wl
NormalForm[TypeTheoryTerm[MatchFirst[MatchPart[f[1, 2], 2, MatchValue]], "WolframLanguage"]]
```

<!-- => some[2] -->

## Possible Issues

A position out of range gives no result:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1], 5, MatchValue], "WolframLanguage"]]
```

<!-- => {} -->

---

An atom has no part past its head:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[f], 1, MatchValue], "WolframLanguage"]]
```

<!-- => {} -->

---

`1 + 2` computes to the atom 3, which has no first part; [HoldForm]() keeps the sum:

```wl
NormalForm[TypeTheoryTerm[MatchPart[1 + 2, 1, MatchValue], "WolframLanguage"]]
```

<!-- => {} -->

---

A position is a natural number:

```wl
TypeTheoryType[MatchPart[f[1, 2], -1, MatchValue], "WolframLanguage"]
```

<!-- => Failure["ElaborationFailed", ...] -->
