---
Template: Symbol
Name: MatchValue
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchValue
Keywords: [Wolfram Language, pattern matching, Match, one result, value, unit, monad, monad laws, Sequence, right side of a rule, prelude]
SeeAlso: [Match, MatchSum, MatchBind, MatchFirst, Sequence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchValue]()[*a*]</code> is the match with one result, the value *a*.

## Details & Options

- <code>[MatchValue]()[*a*]</code> has the type <code>[Match]()[*A*]</code> when *a* has the type *A*. It is a definition of the prelude, the list `{a}`.
- A match holds a single value. A sequence of values is one value, written <code>[MatchValue]()[[Sequence]()[*a*, *b*, ...]]</code>, of the type <code>[Match]()[[Sequence]()[*A*, *B*, ...]]</code>, and a list is one value too. Several results are a [MatchSum]() of matches.
- [MatchValue]() is the unit of the monad of matches: <code>[MatchBind]()[[MatchValue]()[*a*], *f*]</code> gives the results of <code>*f*[*a*]</code>, and <code>[MatchBind]()[*m*, [MatchValue]()]</code> those of *m*.
- As a function, [MatchValue]() is the match that keeps a part as it is, as in <code>[MatchPart]()[*e*, *k*, [MatchValue]()]</code>.
- The rules of a symbol give the right side of the rule that matches as <code>[MatchValue]()[*rhs*]</code>, the expression it rewrites to, quoted.

## Basic Examples

[MatchValue]() makes a match of any value:

```wl
TypeTheoryType[MatchValue]
```

<!-- => ∀_{A ∶ Type u} A → Match[A] -->

---

One natural number as a match:

```wl
TypeTheoryType[MatchValue[3]]
```

<!-- => Match[ℕ] -->

---

The right side of a rule is the one result of a match:

```wl
square[x_] := x^2;
Last[TypeTheoryFormalize[square, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[square] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (x ∶ Expressions) ↦ MatchValue[x^2]] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]] -->

---

A rule that matches once gives [MatchValue]() of the expression it rewrites to:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Typed[f[x_] :> {x, x}, Expressions -> Match[Expressions]][f[1]]],
    TypeTheoryTerm[MatchValue[Unevaluated[{1, 1}]]]
]
```

<!-- => True -->

## Scope

As a function of expressions, [MatchValue]() is the match that keeps an expression as it is, the continuation [MatchPart]() takes:

```wl
TypeTheoryType[Typed[MatchValue, Expressions -> Match[Expressions]]]
```

<!-- => Expressions → Match[Expressions] -->

---

Two parts that a pattern binds are one result, a sequence of two expressions:

```wl
TypeTheoryType[{Typed[x, Expressions], Typed[y, Expressions]} |-> MatchValue[Sequence[x, y]]]
```

<!-- => Expressions → Expressions → Match[[Expressions, Expressions]] -->

---

The values of a sequence can have different types:

```wl
TypeTheoryType[MatchValue[Sequence[1, "true"]]]
```

<!-- => Match[[ℕ, 𝔹]] -->

---

A sequence held with [Unevaluated](), of any length, is one value too:

```wl
TypeTheoryType[TypeTheoryTerm[MatchValue[Unevaluated[1, 2]]]]
```

<!-- => Match[ℕ...] -->

## Properties and Relations

[MatchValue]() of a value is the list of it:

```wl
TypeTheoryEnvironment["Prelude"][MatchValue]
```

<!-- => definition MatchValue : ∀_{A ∶ Type u} A → Match[A] := {A ∶ Type u} (a ∶ A) ↦ {a} -->

---

[MatchBind]() of one result gives the results of the continuation applied to it, here 2 and 3:

```wl
NormalForm[TypeTheoryTerm[MatchBind[MatchValue[2], x |-> {x, x + 1}]]]
```

<!-- => {2, 3} -->

---

[MatchValue]() is a unit on the right of [MatchBind]() for every match, by induction on the list of its results:

```wl
TypeTheoryProof[ForAll[{Typed[m, Match[NonNegativeIntegers]]}, MatchBind[m, MatchValue] == m], {
    "Introduce"[m],
    "Induction"[m],
    "Reflexivity",
    "Introduce"[x, l, h],
    "Simplify"[{MatchBind, h}]
}]
```

<!-- => Proof complete -->

---

One result is a match, whatever the value:

```wl
TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers]}, MatchQ[MatchValue[a]] == "true"], {"Introduce"[a], "Reflexivity"}]
```

<!-- => Proof complete -->

## Possible Issues

[MatchValue]() takes one value:

```wl
TypeTheoryType[MatchValue[1, 2]]
```

<!-- => Failure["ElaborationFailed", ...] -->

Two values are one sequence:

```wl
TypeTheoryType[MatchValue[Sequence[1, 2]]]
```

<!-- => Match[[ℕ, ℕ]] -->

---

A list is one value, so [MatchValue]() of it is one result, a list, not a match of two numbers:

```wl
TypeTheoryType[MatchValue[{1, 2}]]
```

<!-- => Match[{ℕ}] -->

The list is itself the match of its two elements:

```wl
TypeTheoryType[Typed[{1, 2}, Match[NonNegativeIntegers]]]
```

<!-- => Match[ℕ] -->
