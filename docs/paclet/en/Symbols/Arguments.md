---
Template: Symbol
Name: Arguments
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Arguments
Keywords: [Wolfram Language, expressions, arguments, sequence, Head, Construct, Apply, Length, Reverse, Map, pattern matching, Match]
SeeAlso: [Expressions, Atoms, MatchPart, MatchBind, NormalForm]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[Arguments]()[*e*]</code> is the sequence of the arguments of the expression *e*, the empty sequence for an atom.

## Details & Options

- [Arguments]() is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, by the recursor of [Expressions](), which the kernel computes. Its type is `Expressions -> Expressions...`.
- A sequence is spliced where it stands among the arguments of a function or the elements of a list, so <code>[Construct]()[[Head]()[*e*], [Arguments]()[*e*]]</code> is *e* for an expression that is not an atom, and <code>{[Arguments]()[*e*]}</code> is the list of the arguments, as `List @@ e` is in the Wolfram Language. <code>[Length]()[{[Arguments]()[*e*]}]</code> is the number of the arguments, and `Sequence @@ l` makes a list `l` a sequence again.
- [Head](), of the type `Expressions -> Expressions`, gives the head of an expression: the head it was built with, or for an atom [Symbol](), [Integer](), [String]() or the head of another atom.
- A term given without an environment, while the default environment is the prelude, is read in the Wolfram Language environment when it names what only that environment declares, as [Arguments]() and [Head]() are.

## Basic Examples

The arguments of an expression are a sequence of expressions:

```wl
TypeTheoryType[Arguments, "WolframLanguage"]
```

<!-- => Expressions → Expressions... -->

---

The arguments of a quoted sum:

```wl
NormalForm[TypeTheoryTerm[Arguments[HoldForm[a + b + c]], "WolframLanguage"]]
```

<!-- => [a, b, c] -->

---

In a list, the sequence is the list of the arguments, as `List @@ e`:

```wl
NormalForm[TypeTheoryTerm[{Arguments[HoldForm[a + b + c]]}, "WolframLanguage"]]
```

<!-- => {a, b, c} -->

## Scope

The number of the arguments, as `Length[e]`:

```wl
NormalForm[TypeTheoryTerm[Length[{Arguments[HoldForm[a + b + c]]}], "WolframLanguage"]]
```

<!-- => 3 -->

---

The head of each argument, as `Head /@ List @@ e`:

```wl
NormalForm[TypeTheoryTerm[Map[Typed[e, Expressions] |-> Head[e], {Arguments[HoldForm[f[x, 1, "s"]]]}], "WolframLanguage"]]
```

<!-- => {Symbol, Integer, String} -->

---

An expression with its arguments reversed:

```wl
NormalForm[TypeTheoryTerm[Construct[Head[f[1, 2, 3]], Sequence @@ Reverse[{Arguments[f[1, 2, 3]]}]], "WolframLanguage"]]
```

<!-- => f[3, 2, 1] -->

---

An expression without its first argument, as `Rest[e]`:

```wl
NormalForm[TypeTheoryTerm[Construct[Head[f[1, 2, 3]], Sequence @@ Drop[{Arguments[f[1, 2, 3]]}, 1]], "WolframLanguage"]]
```

<!-- => f[2, 3] -->

---

The arguments spliced among the arguments of another expression:

```wl
NormalForm[TypeTheoryTerm[Construct[g, 0, Arguments[f[1, 2]]], "WolframLanguage"]]
```

<!-- => g[0, 1, 2] -->

---

The arguments of `f[1][2]` are those of the last application:

```wl
NormalForm[TypeTheoryTerm[Arguments[f[1][2]], "WolframLanguage"]]
```

<!-- => [2] -->

---

An atom has no arguments:

```wl
NormalForm[TypeTheoryTerm[Arguments[HoldForm[x]], "WolframLanguage"]]
```

<!-- => [] -->

## Properties and Relations

The arguments of [Construct]() of a head and a sequence are that sequence, for every head and every sequence:

```wl
TypeTheoryProof[ForAll[{Typed[h, Expressions], Typed[s, Expressions...]}, Arguments[Construct[h, s]] == s], "WolframLanguage", {"Introduce"[h, s], "Reflexivity"}]
```

<!-- => Proof complete -->

---

An expression that is not an atom is [Construct]() of its head and its arguments:

```wl
NormalForm[TypeTheoryTerm[Construct[Head[HoldForm[a + b c]], Arguments[HoldForm[a + b c]]], "WolframLanguage"]]
```

<!-- => a + b c -->

---

The rules of a symbol count the arguments of an expression with [Arguments]():

```wl
area[w_, h_] := w h;
Last[TypeTheoryFormalize[area, "WolframLanguage", "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[area] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (w ∶ Expressions) ↦ MatchPart[expression, 2, (h ∶ Expressions) ↦ MatchValue[w h]]] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 2]] -->

---

[Arguments]() is a definition, which rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Arguments[f[1]], "WolframLanguage"]]
```

<!-- => <||> -->

## Possible Issues

The arguments are a sequence, not a list, so a function of lists takes them in a list:

```wl
TypeTheoryType[Length[Arguments[f[1, 2]]], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

An atom is not [Construct]() of its head and its arguments, as in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[Construct[Head[HoldForm[3]], Arguments[HoldForm[3]]], "WolframLanguage"]]
```

<!-- => Integer[] -->

---

`1 + 2` computes to the atom 3 where an expression is expected, which has no arguments; [HoldForm]() keeps the sum:

```wl
NormalForm[TypeTheoryTerm[Arguments[1 + 2], "WolframLanguage"]]
```

<!-- => [] -->
