---
Template: Symbol
Name: Arguments
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Arguments
Keywords: [Wolfram Language, expressions, arguments, sequence, Head, Construct, Length, pattern matching, Match]
SeeAlso: [Expressions, Atoms, MatchPart, MatchBind, NormalForm]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[Arguments]()[*e*]</code> is the sequence of the arguments of the expression *e*, the empty sequence for an atom.

## Details & Options

- [Arguments]() is a definition of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, by the recursor of [Expressions](), which the kernel computes. Its type is `Expressions -> Expressions...`.
- A sequence is spliced where it stands among the arguments of a function or the elements of a list, so <code>[Construct]()[[Head]()[*e*], [Arguments]()[*e*]]</code> is *e* for an expression that is not an atom, and <code>{[Arguments]()[*e*]}</code> is the list of the arguments, as `List @@ e` is in the Wolfram Language. <code>[Length]()[{[Arguments]()[*e*]}]</code> is the number of the arguments.
- [Head](), of the type `Expressions -> Expressions`, gives the head of an expression: the head it was built with, or for an atom [Symbol](), [Integer](), [String]() or the head of another atom.
- A term given without an environment, while the default environment is the prelude, is read in the Wolfram Language environment when it names what only that environment declares, as [Arguments]() and [Head]() are.

## Basic Examples

The type of [Arguments]():

```wl
TypeTheoryType[Arguments, "WolframLanguage"]
```

<!-- => Expressions → Expressions... -->

---

The arguments of an expression, a sequence:

```wl
NormalForm[TypeTheoryTerm[Arguments[f[1, 2]], "WolframLanguage"]]
```

<!-- => [1, 2] -->

---

The sequence in a list is the list of the arguments:

```wl
NormalForm[TypeTheoryTerm[{Arguments[f[1, 2]]}, "WolframLanguage"]]
```

<!-- => {1, 2} -->

---

The arguments are a sequence of expressions:

```wl
TypeTheoryType[Arguments[f[1, 2]], "WolframLanguage"]
```

<!-- => Expressions... -->

## Scope

An atom has no arguments:

```wl
NormalForm[TypeTheoryTerm[Arguments[HoldForm[f]], "WolframLanguage"]]
```

<!-- => [] -->

---

Nor has a number, an atom by a coercion:

```wl
NormalForm[TypeTheoryTerm[Arguments[3], "WolframLanguage"]]
```

<!-- => [] -->

---

An expression with a head and no arguments:

```wl
NormalForm[TypeTheoryTerm[Arguments[f[]], "WolframLanguage"]]
```

<!-- => [] -->

---

The arguments are expressions themselves:

```wl
NormalForm[TypeTheoryTerm[Arguments[f[g[1], 2]], "WolframLanguage"]]
```

<!-- => [g[1], 2] -->

---

The arguments of an expression built with [Construct]():

```wl
NormalForm[TypeTheoryTerm[Arguments[Construct[7, 1, 2]], "WolframLanguage"]]
```

<!-- => [1, 2] -->

---

The arguments of a list are its elements:

```wl
NormalForm[TypeTheoryTerm[Arguments[{a, b}], "WolframLanguage"]]
```

<!-- => [a, b] -->

---

The arguments of a quoted sum:

```wl
NormalForm[TypeTheoryTerm[Arguments[HoldForm[1 + 2]], "WolframLanguage"]]
```

<!-- => [1, 2] -->

---

Quoted arguments stay as they are written:

```wl
NormalForm[TypeTheoryTerm[Arguments[HoldForm[{1 + 1, 2}]], "WolframLanguage"]]
```

<!-- => [1 + 1, 2] -->

---

The arguments spliced among the arguments of another expression:

```wl
NormalForm[TypeTheoryTerm[Construct[g, Arguments[f[1, 2]], 3], "WolframLanguage"]]
```

<!-- => g[1, 2, 3] -->

---

The number of the arguments:

```wl
NormalForm[TypeTheoryTerm[Length[{Arguments[f[a, b, c]]}], "WolframLanguage"]]
```

<!-- => 3 -->

---

The arguments of an expression built from a sequence are that sequence:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[s, Expressions...]}, Arguments[Construct[f, s]]][1, 2], "WolframLanguage"]]
```

<!-- => [1, 2] -->

## Properties and Relations

Without an environment, a term that names [Arguments]() is read in the Wolfram Language environment:

```wl
TypeTheoryType[Arguments]
```

<!-- => Expressions → Expressions... -->

---

[Head]() gives the head of an expression:

```wl
TypeTheoryType[Head, "WolframLanguage"]
```

<!-- => Expressions → Expressions -->

---

An expression is [Construct]() of its head and its arguments:

```wl
NormalForm[TypeTheoryTerm[Construct[Head[f[1, 2]], Arguments[f[1, 2]]], "WolframLanguage"]]
```

<!-- => f[1, 2] -->

---

The arguments of [Construct]() of a head and a sequence are that sequence, for every head and sequence:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[h, Expressions], Typed[s, Expressions...]}, Arguments[Construct[h, s]]], "WolframLanguage"],
    TypeTheoryTerm[Function[{Typed[h, Expressions], Typed[s, Expressions...]}, s], "WolframLanguage"]
]
```

<!-- => True -->

---

The list of the arguments is equal by computation to the list written out:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[{Arguments[Construct[7, 1, 2]]}, "WolframLanguage"], TypeTheoryTerm[Typed[{1, 2}, {Expressions}], "WolframLanguage"]]
```

<!-- => True -->

---

[MatchPart]() matches at one argument:

```wl
NormalForm[TypeTheoryTerm[MatchPart[f[1, 2], 2, MatchValue], "WolframLanguage"]]
```

<!-- => {2} -->

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
