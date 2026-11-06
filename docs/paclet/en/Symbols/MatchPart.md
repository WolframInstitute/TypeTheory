---
Template: Symbol
Name: MatchPart
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchPart
Keywords: [Wolfram Language, pattern matching, Match, part, position, head, arguments, Part, match program, nested patterns, prelude]
SeeAlso: [Match, MatchValue, MatchBind, Expressions, Arguments, Part]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchPart]()[*e*, *k*, *f*]</code> is the match *f* of the part of the expression *e* at the position *k*: 0 its head, and *k* its *k*-th argument.

## Details & Options

- *e* is an [Expressions](), *k* a natural number and *f* a function from [Expressions]() to <code>[Match]()[*A*]</code>; the result is a <code>[Match]()[*A*]</code>. It is a definition of the prelude, which the kernel computes.
- The part at 0 is <code>[Head]()[*e*]</code>, and the part at *k* is the *k*-th element of <code>{[Arguments]()[*e*]}</code>.
- Where *e* has no part at *k*, an atom past 0 or an expression with fewer arguments, the match has no result, where [Part]() fails.
- The rules of a symbol match each part of the left side with [MatchPart](), one inside another for a part of a part, as the instructions of a match program reach parts by their paths.

## Basic Examples

[MatchPart]() matches at a position of an expression:

```wl
TypeTheoryType[MatchPart]
```

<!-- => ∀_{A ∶ Type u} Expressions → ℕ → (Expressions → Match[A]) → Match[A] -->

---

With [MatchValue](), it is the match of the part itself, a match of expressions:

```wl
TypeTheoryType[MatchPart[HoldForm[a + b c], 2, MatchValue]]
```

<!-- => Match[Expressions] -->

The second argument of the quoted sum, as one result:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[a + b c], 2, MatchValue]]]
```

<!-- => {b c} -->

## Scope

The match of the part can have results of any type, here whether the part is an atom:

```wl
TypeTheoryType[MatchPart[HoldForm[a + b c], 2, Typed[x, Expressions] |-> MatchValue[AtomQ[x]]]]
```

<!-- => Match[𝔹] -->

---

A part of a part, as `e[[2, 1]]`:

```wl
NormalForm[TypeTheoryTerm[MatchPart[HoldForm[a + b c], 2, Typed[y, Expressions] |-> MatchPart[y, 1, MatchValue]]]]
```

<!-- => {b} -->

---

A position past the last argument gives no result, where [Part]() fails, for every argument:

```wl
TypeTheoryProof[ForAll[{Typed[x, Expressions]}, MatchPart[Construct[f, x], 2, MatchValue] == Typed[{}, Match[Expressions]]], {"Introduce"[x], "Reflexivity"}]
```

<!-- => Proof complete -->

---

The first part of an expression built from a variable and a sequence is the variable, by computation:

```wl
TypeTheoryProof[ForAll[{Typed[x, Expressions], Typed[s, Expressions...]}, MatchPart[Construct[f, x, s], 1, MatchValue] == MatchValue[x]], {"Introduce"[x, s], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

[MatchPart]() is [MatchBind]() of the match of the head, at 0, or of an element of the list of the arguments:

```wl
TypeTheoryEnvironment["Prelude"][MatchPart]
```

<!-- => definition MatchPart : ∀_{A ∶ Type u} Expressions → ℕ → (Expressions → Match[A]) → Match[A] := {A ∶ Type u} (e ∶ Expressions) (k ∶ ℕ) (f ∶ Expressions → Match[A]) ↦ MatchBind[ℕ_rec[(j ∶ ℕ) ↦ Match[Expressions], MatchValue[Head[e]], (j ∶ ℕ) (s ∶ Match[Expressions]) ↦ matchElement[{Arguments[e]}, j], k], f] -->

---

The part at 0 is the head, for every expression:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[e, Expressions] |-> MatchPart[e, 0, MatchValue]], TypeTheoryTerm[Typed[e, Expressions] |-> MatchValue[Head[e]]]]
```

<!-- => True -->

---

A nested pattern is a [MatchPart]() inside another, with a test of the inner head:

```wl
innerOf[g[x_]] := x;
Last[TypeTheoryFormalize[innerOf, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[innerOf] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (part1 ∶ Expressions) ↦ (MatchPart[part1, 1, (x ∶ Expressions) ↦ MatchValue[x]] /; (¬AtomQ[part1] ∧ Decide[Length[{Arguments[part1]}] == 1]) ∧ Head[part1] === g)] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]] -->

## Possible Issues

An atom has no part past its head, whatever atom it is:

```wl
TypeTheoryProof[ForAll[{Typed[a, Atoms]}, MatchPart["atom"[a], 1, MatchValue] == Typed[{}, Match[Expressions]]], {"Introduce"[a], "Reflexivity"}]
```

<!-- => Proof complete -->

---

`1 + 2` computes to the atom 3, which has no first part; [HoldForm]() keeps the sum:

```wl
NormalForm[TypeTheoryTerm[MatchPart[1 + 2, 1, MatchValue]]]
```

<!-- => {} -->

---

A position is a natural number, so a part from the end is no position:

```wl
TypeTheoryType[MatchPart[f[1, 2], -1, MatchValue]]
```

<!-- => Failure["ElaborationFailed", ...] -->
