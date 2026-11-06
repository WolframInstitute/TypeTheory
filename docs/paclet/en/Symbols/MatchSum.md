---
Template: Symbol
Name: MatchSum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MatchSum
Keywords: [Wolfram Language, pattern matching, Match, alternatives, order, several results, rules in turn, Join, monad, prelude]
SeeAlso: [Match, MatchValue, MatchBind, MatchFirst, Alternatives, Join, ReplaceList]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[MatchSum]()[*m1*, *m2*]</code> is the match whose results are those of *m1*, then those of *m2*.

## Details & Options

- <code>[MatchSum]()[*m1*, *m2*]</code> has the type <code>[Match]()[*A*]</code> when *m1* and *m2* have it. It is a definition of the prelude, the [Join]() of the two lists of results.
- [MatchSum]() is where a match gets several results: the alternatives of a pattern, the rules tried in turn, and the ways a sequence or an [Orderless]() head matches. [MatchValue]() holds one value, and `{}` is the match with no result, the unit of [MatchSum]().
- The alternatives keep their order, and a result that both give is there twice. [MatchFirst]() takes a result of *m1* before any of *m2*, as the Wolfram Language applies the first rule that matches.
- [MatchSum]() takes two matches; more alternatives are sums of sums.

## Basic Examples

[MatchSum]() puts two matches of one type together:

```wl
TypeTheoryType[MatchSum]
```

<!-- => ∀_{A ∶ Type u} Match[A] → Match[A] → Match[A] -->

---

A list of rules is the sum of the matches of each rule, the same by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Typed[{f[x_, y_] :> {y, x}, f[x__] :> {x}}, Expressions -> Match[Expressions]][f[1, 2]]],
    TypeTheoryTerm[MatchSum[
        Typed[f[x_, y_] :> {y, x}, Expressions -> Match[Expressions]][f[1, 2]],
        Typed[f[x__] :> {x}, Expressions -> Match[Expressions]][f[1, 2]]
    ]]
]
```

<!-- => True -->

---

So [ReplaceList]() gives the results of the first rule, then those of the second:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2], {f[x_, y_] :> {y, x}, f[x__] :> {x}}]]]
```

<!-- => {{2, 1}, {1, 2}} -->

## Scope

The [Alternatives]() of a pattern are a sum, tried at each argument in turn:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, "a", b], f[___, x : (_Integer | _String), ___] :> x]]]
```

<!-- => {1, "a"} -->

---

A result that two rules give is there twice, as in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[a, a], {f[x_, _] :> x, f[_, y_] :> y}]]]
```

<!-- => {a, a} -->

---

The rules of a function with two definitions:

```wl
swapped[x_, y_] := {y, x};
swapped[x_, y__] := {{y}, x};
swapping = TypeTheoryEnvironment[TypeTheoryFormalize[swapped, "Meaning" -> "Rules"]]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

They are the first result of the sum of the matches of the two rules:

```wl
swapping["DownValues[swapped]"]
```

<!-- => definition DownValues[swapped] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchSum[...]] -->

## Properties and Relations

The definition of [MatchSum]():

```wl
TypeTheoryEnvironment["Prelude"][MatchSum]
```

<!-- => definition MatchSum : ∀_{A ∶ Type u} Match[A] → Match[A] → Match[A] := {A ∶ Type u} (m ∶ Match[A]) (n ∶ Match[A]) ↦ Join[m, n] -->

---

The match with no result is a unit on the left for every match, by computation:

```wl
TypeTheoryProof[ForAll[{Typed[m, Match[NonNegativeIntegers]]}, MatchSum[{}, m] == m], {"Introduce"[m], "Reflexivity"}]
```

<!-- => Proof complete -->

On the right it is one by induction on the list of results:

```wl
TypeTheoryProof[ForAll[{Typed[m, Match[NonNegativeIntegers]]}, MatchSum[m, {}] == m], {
    "Introduce"[m],
    "Induction"[m],
    "Reflexivity",
    "Introduce"[x, l, h],
    "Change"[Prepend[MatchSum[l, {}], x] == Prepend[l, x]],
    "Rewrite"[h]
}]
```

<!-- => Proof complete -->

---

The first result of a sum is the left alternative's where it has one, whatever the right one:

```wl
TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[m, Match[NonNegativeIntegers]]}, MatchFirst[MatchSum[MatchValue[a], m]] == "some"[a]], {"Introduce"[a, m], "Reflexivity"}]
```

<!-- => Proof complete -->

## Possible Issues

[MatchSum]() takes two matches:

```wl
TypeTheoryType[MatchSum[MatchValue[1], MatchValue[2], MatchValue[3]]]
```

<!-- => Failure["ElaborationFailed", ...] -->

Three alternatives are a sum of sums:

```wl
TypeTheoryType[MatchSum[MatchValue[1], MatchSum[MatchValue[2], MatchValue[3]]]]
```

<!-- => Match[ℕ] -->

---

The two alternatives have results of one type:

```wl
TypeTheoryType[MatchSum[MatchValue[1], MatchValue["true"]]]
```

<!-- => Failure["TypeMismatch", ...] -->
