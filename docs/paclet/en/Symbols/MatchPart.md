---
Template: Symbol
Name: MatchPart
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchPart
Keywords: [Wolfram Language, pattern matching, Match, part, position, head, arguments, Part, match program, nested patterns]
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

[MatchPart]() matches at a position of an expression:

```wl
TypeTheoryType[MatchPart, "WolframLanguage"]
```

<!-- => ∀_{A ∶ Type u} Expressions → ℕ → (Expressions → Match[A]) → Match[A] -->

---

The second argument of a quoted sum, as one result:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[a + b c], 2, MatchValue], "WolframLanguage"]]
```

<!-- => {b c} -->

---

Position 0 is the head:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[a + b c], 0, MatchValue], "WolframLanguage"]]
```

<!-- => {Plus} -->

## Scope

A part of a part, as `e[[2, 1]]`:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[a + b c], 2, Typed[y, Expressions] |-> MatchPart[y, 1, MatchValue]], "WolframLanguage"]]
```

<!-- => {b} -->

---

A part that passes a test, here an integer, as `_Integer` tests it:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f["a", 1], 2, Typed[x, Expressions] |-> (MatchValue[x] /; SameQ[Head[x], HoldForm[Integer]])], "WolframLanguage"]]
```

<!-- => {1} -->

A part that fails it gives no result:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f["a", 1], 1, Typed[x, Expressions] |-> (MatchValue[x] /; SameQ[Head[x], HoldForm[Integer]])], "WolframLanguage"]]
```

<!-- => {} -->

---

A position past the last argument gives no result, where [Part]() fails:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1], 5, MatchValue], "WolframLanguage"]]
```

<!-- => {} -->

---

The first part of an expression built from a variable and a sequence computes to the variable:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[x, Expressions], Typed[s, Expressions...]}, MatchPart[Construct[f, x, s], 1, MatchValue]], "WolframLanguage"]]
```

<!-- => (x ∶ Expressions) (s ∶ Expressions...) ↦ {x} -->

## Properties and Relations

A nested pattern is a [MatchPart]() inside another, with a test of the inner head:

```wl
innerOf[g[x_]] := x;
Last[TypeTheoryFormalize[innerOf, "WolframLanguage", "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[innerOf] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (part1 ∶ Expressions) ↦ (MatchPart[part1, 1, (x ∶ Expressions) ↦ MatchValue[x]] /; (¬AtomQ[part1] ∧ Decide[Length[{Arguments[part1]}] == 1]) ∧ Head[part1] === g)] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]] -->

---

The part at 0 is the head, for every expression:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[e, Expressions] |-> MatchPart[e, 0, MatchValue], "WolframLanguage"], TypeTheoryTerm[Typed[e, Expressions] |-> MatchValue[Head[e]], "WolframLanguage"]]
```

<!-- => True -->

## Possible Issues

An atom has no part past its head:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[x], 1, MatchValue], "WolframLanguage"]]
```

<!-- => {} -->

---

`1 + 2` computes to the atom 3, which has no first part; [HoldForm]() keeps the sum:

```wl
NormalForm[TypeTheoryTerm[MatchPart[1 + 2, 1, MatchValue], "WolframLanguage"]]
```

<!-- => {} -->

---

A position is a natural number, so a part from the end is no position:

```wl
TypeTheoryType[MatchPart[f[1, 2], -1, MatchValue], "WolframLanguage"]
```

<!-- => Failure["ElaborationFailed", ...] -->
