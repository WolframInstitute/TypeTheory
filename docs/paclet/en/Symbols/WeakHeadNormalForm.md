---
Template: Symbol
Name: WeakHeadNormalForm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/WeakHeadNormalForm
Keywords: [reduction, weak head normal form, computation, beta reduction, unfolding, recursor, head]
SeeAlso: [NormalForm, DefinitionallyEqualQ, TypeTheoryCheck, TypeTheoryTerm, TypeTheoryDefinition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation]
---

## Usage

<code>[WeakHeadNormalForm]()[*term*]</code> reduces the [TypeTheoryTerm]() *term* until its head can no longer reduce.

## Details & Options

- Reduction applies functions to their arguments, unfolds definitions and local definitions, applies a recursor to a constructor, takes a field of a constructed structure, and computes the operations on natural number literals. Theorems never unfold.
- Only the head is reduced: the arguments of a constructor, and the body of a function, stay as they are. [NormalForm]() reduces every part.
- A [TypeTheoryTerm]() without an environment is in the default environment, the prelude unless [SetTypeTheoryEnvironment]() set another.
- The kernel reduces a term to its weak head normal form to compare it with another, as [DefinitionallyEqualQ]() and [TypeTheoryCheck]() do.

## Basic Examples

Addition of literals:

```wl
WeakHeadNormalForm[TypeTheoryTerm[2 + 3]]
```

<!-- => 5 -->

---

A function applied to an argument:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, Naturals]}, x + 1][41]]]
```

<!-- => 42 -->

---

Only the head reduces, here the list's first constructor, and its elements stay:

```wl
WeakHeadNormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {1 + 1, 2 3} -->

## Scope

A definition unfolds:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

---

A recursor applied to a constructor:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[And][
    Function[{Typed[t, And[True, True]]}, Naturals],
    Function[{Typed[p, True], Typed[q, True]}, 7],
    "andIntroduction"["trueIntroduction", "trueIntroduction"]
]]]
```

<!-- => 7 -->

---

A recursor applied to a literal:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Naturals][Typed[k, Naturals] |-> Naturals, 1, {Typed[k, Naturals], Typed[r, Naturals]} |-> 2 r, 5]]]
```

<!-- => 32 -->

---

A local definition unfolds:

```wl
WeakHeadNormalForm[TypeTheoryTerm[With[{x = 2}, x + 1]]]
```

<!-- => 3 -->

---

A field of a constructed pair:

```wl
WeakHeadNormalForm[TypeTheoryTerm["pair"[1, 2][[2]]]]
```

<!-- => 2 -->

---

A Boolean decided:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2 == 2]]]
```

<!-- => true -->

---

A definition of your own:

```wl
doubled = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Typed[n, Naturals] |-> n + n]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

It unfolds, and the sum computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Doubled[21], doubled]]
```

<!-- => 42 -->

---

The argument of a function is not reduced before the function is applied:

```wl
WeakHeadNormalForm[TypeTheoryTerm[(Typed[l, {Naturals}] |-> Prepend[l, 1 + 1])[{2 + 2}]]]
```

<!-- => {1 + 1, 2 + 2} -->

---

An expression of the Wolfram Language environment compared by computation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[f], HoldForm[f]], "WolframLanguage"]]
```

<!-- => true -->

---

The first result of a match:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], "WolframLanguage"]]
```

<!-- => some[1] -->

---

A type that is a definition unfolds:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Match[NonNegativeIntegers], "WolframLanguage"]]
```

<!-- => {ℕ} -->

## Properties and Relations

The arguments of a constructor stay as they are:

```wl
WeakHeadNormalForm[TypeTheoryTerm["some"[1 + 1]]]
```

<!-- => some[1 + 1] -->

[NormalForm]() reduces them:

```wl
NormalForm[TypeTheoryTerm["some"[1 + 1]]]
```

<!-- => some[2] -->

---

A function is in weak head normal form, its body as it is:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n + 0 -->

[NormalForm]() reduces the body:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n -->

---

So is a quantifier:

```wl
WeakHeadNormalForm[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]]]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

---

A theorem, which does not unfold:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Its proof stays a name:

```wl
WeakHeadNormalForm[TypeTheoryTerm[TwoPlusTwo, arithmetic]]
```

<!-- => TwoPlusTwo -->

## Possible Issues

[WeakHeadNormalForm]() takes a [TypeTheoryTerm](); an expression on its own evaluates and stays as it is:

```wl
WeakHeadNormalForm[2 + 3]
```

<!-- => WeakHeadNormalForm[5] -->

---

`Not[True]` could be a proposition or a Boolean:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Not[True]]]
```

<!-- => Failure["Ambiguous", ...] -->

[Typed]() says which:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[Not[True], TypeUniverse[0]]]]
```

<!-- => True ⇒ False -->
