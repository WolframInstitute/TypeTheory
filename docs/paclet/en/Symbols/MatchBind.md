---
Template: Symbol
Name: MatchBind
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchBind
Keywords: [Wolfram Language, expressions, pattern matching, Match, bind, monad, parts in turn, several results, match program, prelude]
SeeAlso: [Match, MatchValue, MatchSum, MatchPart, MatchFirst, Expressions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchBind]()[*m*, *f*]</code> is the match whose results are those of *f* applied to each result of the match *m*, in order.

## Details & Options

- For *m* of the type <code>[Match]()[*A*]</code> and *f* a function from *A* to <code>[Match]()[*B*]</code>, <code>[MatchBind]()[*m*, *f*]</code> has the type <code>[Match]()[*B*]</code>. It is a definition of the prelude, by the recursor of lists: the [Join]() of the results of *f* for each result of *m*.
- A match is the list of its results in the order they are tried, the monad of pattern matching: [MatchBind]() is its bind, the parts of a pattern matched in turn, and [MatchValue]() its unit.
- A result of *m* for which *f* gives no result is left out, so a [Condition]() in *f* keeps the results that pass it, and one for which *f* gives several results gives them all, in order.
- Two matches combine by a [MatchBind]() in each, keeping the two results as one value, such as <code>[MatchValue]()[[Sequence]()[*a*, *b*]]</code>.

## Basic Examples

[MatchBind]() continues each result of a match by another match:

```wl
TypeTheoryType[MatchBind]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} Match[A] → (A → Match[B]) → Match[B] -->

---

The two arguments of `f[1, 2]` matched in turn, the two parts kept as one result, a sequence of two expressions:

```wl
TypeTheoryType[MatchBind[MatchPart[f[1, 2], 1, MatchValue], x |-> MatchPart[f[1, 2], 2, y |-> MatchValue[Sequence[x, y]]]]]
```

<!-- => Match[[Expressions, Expressions]] -->

---

Of the two ways to split `f[1, 2, 3]`, a condition after the match keeps the one whose first part has two arguments:

```wl
NormalForm[TypeTheoryTerm[MatchBind[
    Typed[f[x__, y__] :> {x}, Expressions -> Match[Expressions]][f[1, 2, 3]],
    e |-> (MatchValue[e] /; Decide[Length[{Arguments[e]}] == 2])
]]]
```

<!-- => {{1, 2}} -->

## Scope

The continuation can change the type of the results, here from natural numbers to expressions:

```wl
TypeTheoryType[MatchBind[Typed[{1, 2}, Match[NonNegativeIntegers]], n |-> MatchValue[Construct[f, n]]]]
```

<!-- => Match[Expressions] -->

---

Every result of one match with every result of another, in order:

```wl
NormalForm[TypeTheoryTerm[MatchBind[
    Typed[f[___, x_, ___] :> x, Expressions -> Match[Expressions]][f[a, b]],
    x |-> MatchBind[Typed[g[___, y_, ___] :> y, Expressions -> Match[Expressions]][g[1, 2]], y |-> MatchValue[HoldForm[{x, y}]]]
]]]
```

<!-- => {{a, 1}, {a, 2}, {b, 1}, {b, 2}} -->

---

A rule whose pattern binds a sequence binds it in turn:

```wl
restOf[x_, y__] := {y};
Last[TypeTheoryFormalize[restOf, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[restOf] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (x ∶ Expressions) ↦ MatchBind[MatchValue[[Sequence @@ Drop[{Arguments[expression]}, 1]]], (y ∶ Expressions...) ↦ MatchValue[{y}]]] /; ¬AtomQ[expression] ∧ Decide[2 <= Length[{Arguments[expression]}]]] -->

## Applications

A match program for `f[x_Integer, y_] :> {y, x}`, which tests the head of the first argument before it matches the second:

```wl
program = TypeTheoryTerm[e |-> MatchBind[
    MatchPart[e, 1, x |-> (MatchValue[x] /; SameQ[Head[x], HoldForm[Integer]])],
    x |-> MatchPart[e, 2, y |-> MatchValue[HoldForm[{y, x}]]]
]]
```

<!-- => e ↦ MatchBind[MatchPart[e, 1, x ↦ (MatchValue[x] /; Head[x] === Integer)], x ↦ MatchPart[e, 2, y ↦ MatchValue[{y, x}]]] -->

It is a function from an expression to its matches, as the rule is:

```wl
TypeTheoryType[program]
```

<!-- => Expressions → Match[Expressions] -->

It gives the same match as the rule on `f[1, "a"]`, by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[program[f[1, "a"]]], TypeTheoryTerm[Typed[f[x_Integer, y_] :> {y, x}, Expressions -> Match[Expressions]][f[1, "a"]]]]
```

<!-- => True -->

With a string first, the test fails and the second argument is never matched:

```wl
NormalForm[TypeTheoryTerm[program[f["a", 1]]]]
```

<!-- => {} -->

## Properties and Relations

The definition of [MatchBind]():

```wl
TypeTheoryEnvironment["Prelude"][MatchBind]
```

<!-- => definition MatchBind : ∀_{A ∶ Type u} ∀_{B ∶ Type v} Match[A] → (A → Match[B]) → Match[B] := {A ∶ Type u} {B ∶ Type v} (m ∶ Match[A]) (f ∶ A → Match[B]) ↦ List_rec[(t ∶ {A}) ↦ {B}, {}, (x ∶ A) (rest ∶ {A}) (r ∶ {B}) ↦ Join[f[x], r], m] -->

---

Binds associate, as the binds of a monad do:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[MatchBind[MatchBind[{1, 2}, x |-> {x, x + 10}], y |-> MatchValue[2 y]]],
    TypeTheoryTerm[MatchBind[{1, 2}, x |-> MatchBind[{x, x + 10}, y |-> MatchValue[2 y]]]]
]
```

<!-- => True -->

## Possible Issues

The continuation gives a match, not a value:

```wl
TypeTheoryType[MatchBind[{1, 2}, x |-> x + 1]]
```

<!-- => Failure["TypeMismatch", ...] -->

[MatchValue]() makes the value a match:

```wl
TypeTheoryType[MatchBind[{1, 2}, x |-> MatchValue[x + 1]]]
```

<!-- => Match[ℕ] -->
