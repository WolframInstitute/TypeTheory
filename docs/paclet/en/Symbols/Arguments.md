---
Template: Symbol
Name: Arguments
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Arguments
Keywords: [Wolfram Language, expressions, arguments, sequence, Head, Construct, Apply, Length, Reverse, Map, pattern matching, Match, prelude]
SeeAlso: [Expressions, Atoms, MatchPart, MatchBind, NormalForm]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[Arguments]()[*e*]</code> is the sequence of the arguments of the expression *e*, the empty sequence for an atom.

## Details & Options

- [Arguments]() is a definition of the prelude, by the recursor of [Expressions](), which the kernel computes. Its type is `Expressions -> Expressions...`.
- A sequence is spliced where it stands among the arguments of a function or the elements of a list, so <code>[Construct]()[[Head]()[*e*], [Arguments]()[*e*]]</code> is *e* for an expression that is not an atom, and <code>{[Arguments]()[*e*]}</code> is the list of the arguments, as `List @@ e` is in the Wolfram Language. <code>[Length]()[{[Arguments]()[*e*]}]</code> is the number of the arguments, and `Sequence @@ l` makes a list `l` a sequence again.
- [Head](), of the type `Expressions -> Expressions`, gives the head of an expression: the head it was built with, or for an atom [Symbol](), [Integer](), [String]() or the head of another atom.
- The arguments of a curried application `f[1][2]` are those of the last application, `[2]`, and its head is `f[1]`.

## Basic Examples

The arguments of an expression are a sequence of expressions:

```wl
TypeTheoryType[Arguments]
```

<!-- => Expressions → Expressions... -->

---

The arguments of a quoted sum:

```wl
NormalForm[TypeTheoryTerm[Arguments[Unevaluated[a + b + c]]]]
```

<!-- => [a, b, c] -->

---

In a list, the sequence is the list of the arguments, as `List @@ e`:

```wl
TypeTheoryType[{Arguments[Unevaluated[a + b + c]]}]
```

<!-- => {Expressions} -->

## Scope

The number of the arguments, as `Length[e]`, is a natural number:

```wl
TypeTheoryType[Length[{Arguments[Unevaluated[a + b + c]]}]]
```

<!-- => ℕ -->

It is 3, by computation:

```wl
TypeTheoryProof[Length[{Arguments[Unevaluated[a + b + c]]}] == 3, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

A function that reverses the arguments of an expression, as `Reverse[e]` does, by [Construct]() of the head and the reversed list as a sequence:

```wl
TypeTheoryType[e |-> Construct[Head[e], Sequence @@ Reverse[{Arguments[e]}]]]
```

<!-- => Expressions → Expressions -->

It takes `f[1, 2, 3]` to `f[3, 2, 1]`, by computation:

```wl
TypeTheoryProof[(e |-> Construct[Head[e], Sequence @@ Reverse[{Arguments[e]}]])[f[1, 2, 3]] == f[3, 2, 1], {"Reflexivity"}]
```

<!-- => Proof complete -->

---

A function of the arguments of an expression maps over their list, here the head of each, as `Head /@ List @@ e`:

```wl
TypeTheoryType[Map[e |-> Head[e], {Arguments[f[x, 1, "s"]]}]]
```

<!-- => {Expressions} -->

---

The arguments of `f[1][2]` are those of the last application, so it has one argument, by computation:

```wl
TypeTheoryProof[Length[{Arguments[f[1][2]]}] == 1, {"Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

[Arguments]() is a definition by the recursor of [Expressions](), whose second motive, here [Booleans](), is that of the sequences of arguments:

```wl
TypeTheoryEnvironment["Prelude"][Arguments]
```

<!-- => definition Arguments : Expressions → Expressions... := (e ∶ Expressions) ↦ (Expressions_rec)[(x ∶ Expressions) ↦ Expressions..., (xs ∶ Expressions...) ↦ 𝔹, (a ∶ Atoms) ↦ [], (h ∶ Expressions) (arguments ∶ Expressions...) (hr ∶ Expressions...) (ar ∶ 𝔹) ↦ arguments, true, (x ∶ Expressions) (rest ∶ Expressions...) (xr ∶ Expressions...) (rr ∶ 𝔹) ↦ rr, e] -->

---

The arguments of [Construct]() of a head and a sequence are that sequence, for every head and every sequence:

```wl
TypeTheoryProof[ForAll[{Typed[h, Expressions], Typed[s, Expressions...]}, Arguments[Construct[h, s]] == s], {"Introduce"[h, s], "Reflexivity"}]
```

<!-- => Proof complete -->

---

An expression that is not an atom is [Construct]() of its head and its arguments, for every head and every sequence:

```wl
TypeTheoryProof[ForAll[{Typed[h, Expressions], Typed[s, Expressions...]}, Construct[Head[Construct[h, s]], Arguments[Construct[h, s]]] == Construct[h, s]], {"Introduce"[h, s], "Reflexivity"}]
```

<!-- => Proof complete -->

---

The rules of a symbol count the arguments of an expression with [Arguments]():

```wl
area[w_, h_] := w h;
Last[TypeTheoryFormalize[area, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[area] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (w ∶ Expressions) ↦ MatchPart[expression, 2, (h ∶ Expressions) ↦ MatchValue[w h]]] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 2]] -->

---

[Arguments]() is a definition, which rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Arguments[f[1]]]]
```

<!-- => <||> -->

## Possible Issues

The arguments are a sequence, not a list, so a function of lists does not take them:

```wl
TypeTheoryType[Length[Arguments[f[1, 2]]]]
```

<!-- => Failure["TypeMismatch", ...] -->

In a list it does:

```wl
TypeTheoryType[Length[{Arguments[f[1, 2]]}]]
```

<!-- => ℕ -->

---

An atom is not [Construct]() of its head and its arguments, as in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[Construct[Head[3], Arguments[3]]]]
```

<!-- => Integer[] -->

---

`1 + 2` computes to the atom 3 where an expression is expected, which has no arguments; [Unevaluated]() keeps the sum:

```wl
NormalForm[TypeTheoryTerm[Arguments[1 + 2]]]
```

<!-- => [] -->
