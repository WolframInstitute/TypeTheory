---
Template: Symbol
Name: Expressions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Expressions
Keywords: [Wolfram Language, expressions, Construct, atom, head, arguments, sequences, Unevaluated, HoldForm, nested inductive type, pattern matching, Match, rewriting, derivative]
SeeAlso: [Atoms, Arguments, Strings, ExpressionEvaluate, Match, MatchPart, NormalForm, TypeTheoryFormalize]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

[Expressions]() is the type of the expressions of the Wolfram Language: an atom, <code>"atom"[*a*]</code>, or a head applied to the sequence of its arguments, <code>[Construct]()[*h*, *a*, *b*, ...]</code>, which is <code>*h*[*a*, *b*, ...]</code>.

## Details & Options

- [Expressions]() is an inductive type of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code> with two constructors: `"atom"`, of the type `Atoms -> Expressions`, and the one written and shown as [Construct](), of the type `Expressions -> Expressions... -> Expressions`, which takes the arguments of an expression as one sequence. It is a nested inductive type: its recursor has a second motive, for the sequences of arguments.
- `A...` is the type of the sequences of any number of elements of `A`, as the pattern `p...` takes any number of expressions. A sequence is written held, `Unevaluated[a, b, ...]`, as the Wolfram Language holds the arguments it passes on, and shows in brackets, `[a, b, ...]`. Among its elements, a sequence `Unevaluated[...]`, and `Sequence @@ l` and `Unevaluated @@ l` of a list `l`, are spliced in, and <code>[Prepend]()[*s*, *x*]</code> puts *x* in front of a sequence *s*.
- The last explicit binder of a function, if its type is `A...`, takes the arguments that are left as one sequence, each an `A` or a sequence spliced in, as the Wolfram Language gives a function its arguments: `Construct[h, a, b]` gives `h` the sequence of `a` and `b`, and `Construct[h]` the empty one, `h[]`.
- [Construct]() of a term that is no expression applies it, as [Construct]() does in the Wolfram Language.
- Where an expression is expected, a term evaluates as in the Wolfram Language: a symbol that names nothing stands for itself, a head that names nothing applied to arguments is that expression, `f[1][2]` is the expression with the head `f[1]`, `{a, b}` is the expression `List[a, b]`, and a natural number or a string is its atom, by a coercion. A declared constant computes, so `1 + 2` is the expression `3`, and <code>[HoldForm]()[*e*]</code> quotes *e*, so that nothing in it computes. [NormalForm]() shows an expression bare, without the [HoldForm]().
- [Head](), [Arguments](), [AtomQ]() and [SameQ]() are definitions by the recursor of [Expressions](), which the kernel computes, and so are [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated](). [ExpressionEvaluate](), the expression the Wolfram Language evaluates an expression to, is an axiom.
- The Wolfram Language strips [Unevaluated]() from an argument of a function with rules, even one that holds its arguments, so a sequence on its own is written inside a term: <code>[TypeTheoryTerm]()[Unevaluated[1, 2], "WolframLanguage"]</code>.
- [TypeTheoryFormalize]() gives a function that does not translate, and that it is given no type for, the type `Expressions -> ... -> Expressions`, one [Expressions]() for each argument.

## Basic Examples

[Expressions]() has two constructors, one for an atom and one for a head applied to a sequence of arguments:

```wl
TypeTheoryEnvironment["WolframLanguage"][Expressions]
```

<!-- => inductive Expressions : Type | atom : Atoms → Expressions | Construct : Expressions → Expressions... → Expressions -->

---

`f` names nothing, so `f[1, 2]` is the expression itself, and a rule rewrites it:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_] :> {y, x}], "WolframLanguage"]]
```

<!-- => {2, 1} -->

---

The head of a quoted sum is [Plus]():

```wl
NormalForm[TypeTheoryTerm[Head[HoldForm[a + b c]], "WolframLanguage"]]
```

<!-- => Plus -->

---

[Construct]() puts the arguments of a sum under another head, as [Apply]() does:

```wl
NormalForm[TypeTheoryTerm[Construct[HoldForm[Times], Arguments[HoldForm[a + b + c]]], "WolframLanguage"]]
```

<!-- => a b c -->

## Scope

[Construct]() of a head alone gives it no arguments:

```wl
NormalForm[TypeTheoryTerm[Construct[f], "WolframLanguage"]]
```

<!-- => f[] -->

---

The head of `f[1][2]` is `f[1]`:

```wl
NormalForm[TypeTheoryTerm[Head[f[1][2]], "WolframLanguage"]]
```

<!-- => f[1] -->

---

A variable in a quotation is the expression it stands for, so a function fills in a template:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[x, Expressions]}, HoldForm[x^2 + x]][HoldForm[a + b]], "WolframLanguage"]]
```

<!-- => (a + b)^2 + (a + b) -->

---

`Sequence @@ l` of a list `l` among the arguments is spliced in:

```wl
NormalForm[TypeTheoryTerm[Construct[f, Sequence @@ {1, 2}, 3], "WolframLanguage"]]
```

<!-- => f[1, 2, 3] -->

---

A function whose last binder has the type `Expressions...` takes any number of arguments, as `g[0, ##] &` does:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[s, Expressions...]}, Construct[g, 0, s]][1, 2], "WolframLanguage"]]
```

<!-- => g[0, 1, 2] -->

---

[Construct]() of a function that is no expression applies it:

```wl
NormalForm[TypeTheoryTerm[Construct[Typed[n, NonNegativeIntegers] |-> n + 1, 2], "WolframLanguage"]]
```

<!-- => 3 -->

## Applications

A derivative by two rules, one for a sum and one for a power, applied by [ReplaceRepeated]() until neither applies:

```wl
NormalForm[TypeTheoryTerm[ReplaceRepeated[HoldForm[d[x^2 + x^3]], {d[u_ + v_] :> d[u] + d[v], d[x^n_] :> n x^(n - 1)}], "WolframLanguage"]]
```

<!-- => 2 x^(2 - 1) + 3 x^(3 - 1) -->

---

A statement that the rule for a power rewrites `d[x^n]` for every exponent *n*:

```wl
powerRule = TypeTheoryTerm[ForAll[{Typed[n, Expressions]}, Replace[HoldForm[d[x^n]], d[x^m_] :> m x^(m - 1)] == HoldForm[n x^(n - 1)]], "WolframLanguage"]
```

<!-- => ∀_n∶Expressions Replace[d[x^n], d[x^m_] :> m x^(m - 1)] == n x^(n - 1) -->

The kernel proves it by computation, with *n* a variable:

```wl
TypeTheoryProof[powerRule, {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

The head of [Construct]() of a head and a sequence is that head, for every head and every sequence:

```wl
TypeTheoryProof[ForAll[{Typed[h, Expressions], Typed[s, Expressions...]}, Head[Construct[h, s]] == h], "WolframLanguage", {"Introduce"[h, s], "Reflexivity"}]
```

<!-- => Proof complete -->

---

[SameQ]() compares two expressions part by part, by computation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[Construct[f, 1, 2], f[1, 2]], "WolframLanguage"]]
```

<!-- => true -->

---

A function that [TypeTheoryFormalize]() does not translate takes an [Expressions]() for each argument:

```wl
styled[x_] := Style[x, Bold];
Last[TypeTheoryFormalize[styled, "WolframLanguage"]]
```

<!-- => axiom styled : Expressions → Expressions -->

## Possible Issues

A declared constant computes where an expression is expected, so `1 + 2` is the atom 3, and [HoldForm]() keeps it as it is written:

```wl
NormalForm[TypeTheoryTerm[Construct[f, 1 + 2, HoldForm[1 + 2]], "WolframLanguage"]]
```

<!-- => f[3, 1 + 2] -->

---

Nothing evaluates a quoted expression, so the arguments of a quoted [Plus]() are not sorted, and two sums in another order are different expressions:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[a + b], HoldForm[b + a]], "WolframLanguage"]]
```

<!-- => false -->

---

On its own, `Unevaluated[1, 2]` loses its wrapper as the Wolfram Language passes it on, and is read as `Sequence[1, 2]`, a sequence of exactly two elements:

```wl
TypeTheoryType[Unevaluated[1, 2], "WolframLanguage"]
```

<!-- => [ℕ, ℕ] -->

Inside [TypeTheoryTerm]() it stays a sequence of any length:

```wl
TypeTheoryType[TypeTheoryTerm[Unevaluated[1, 2], "WolframLanguage"]]
```

<!-- => ℕ... -->

---

[Expressions]() is a constant of the Wolfram Language environment, not of the prelude:

```wl
TypeTheoryType[Expressions, "Prelude"]
```

<!-- => Failure["ElaborationFailed", ...] -->
