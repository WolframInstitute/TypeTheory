---
Template: Symbol
Name: Expressions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Expressions
Keywords: [Wolfram Language, expressions, Construct, atom, head, arguments, sequences, Unevaluated, HoldForm, nested inductive type, pattern matching, Match]
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
- Where an expression is expected, a term evaluates as in the Wolfram Language: a symbol that names nothing stands for itself, a head that names nothing applied to arguments is that expression, `{a, b}` is the expression `List[a, b]`, and a natural number or a string is its atom, by a coercion. A declared constant computes, so `1 + 2` is the expression `3`, and <code>[HoldForm]()[*e*]</code> quotes *e*, so that nothing in it computes. [NormalForm]() shows an expression bare, without the [HoldForm]().
- [Head](), [Arguments](), [AtomQ]() and [SameQ]() are definitions by the recursor of [Expressions](), which the kernel computes. [ExpressionEvaluate](), the expression the Wolfram Language evaluates an expression to, is an axiom.
- The Wolfram Language strips [Unevaluated]() from an argument of a function with rules, even one that holds its arguments, so a sequence on its own is written inside a term: <code>[TypeTheoryTerm]()[Unevaluated[1, 2], *env*]</code>, or <code>[Typed]()[Unevaluated[1, 2], NonNegativeIntegers...]</code>.
- [TypeTheoryFormalize]() gives a function that does not translate, and that it is given no type for, the type `Expressions -> ... -> Expressions`, one [Expressions]() for each argument.

## Basic Examples

The type of [Expressions]():

```wl
TypeTheoryType[Expressions, "WolframLanguage"]
```

<!-- => Type -->

---

The type of [Construct](), whose arguments are a sequence:

```wl
TypeTheoryType[Construct, "WolframLanguage"]
```

<!-- => Expressions → Expressions... → Expressions -->

---

The type of the other constructor, which makes an expression of an atom:

```wl
TypeTheoryType["atom", "WolframLanguage"]
```

<!-- => Atoms → Expressions -->

---

`f` names nothing, so [Construct]() of it, 1 and 2 is the expression `f[1, 2]`:

```wl
NormalForm[TypeTheoryTerm[Construct[f, 1, 2], "WolframLanguage"]]
```

<!-- => f[1, 2] -->

---

Any expression can be a head:

```wl
TypeTheoryType[Construct[7, 1, 2], "WolframLanguage"]
```

<!-- => Expressions -->

## Scope

[Construct]() of a head alone gives it the empty sequence of arguments:

```wl
NormalForm[TypeTheoryTerm[Construct[f], "WolframLanguage"]]
```

<!-- => f[] -->

---

A head that names nothing, applied to arguments, is that expression:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[f[1, 2], Expressions], "WolframLanguage"], TypeTheoryTerm[Construct[f, 1, 2], "WolframLanguage"]]
```

<!-- => True -->

---

Expressions nest:

```wl
NormalForm[TypeTheoryTerm[Construct[f, Construct[g, 1], 2], "WolframLanguage"]]
```

<!-- => f[g[1], 2] -->

---

A list is the expression with the head [List]():

```wl
NormalForm[TypeTheoryTerm[Head[{a, b}], "WolframLanguage"]]
```

<!-- => List -->

---

A natural number is an expression, its atom, by a coercion:

```wl
NormalForm[TypeTheoryTerm[Head[3], "WolframLanguage"]]
```

<!-- => Integer -->

---

So is a string:

```wl
NormalForm[TypeTheoryTerm[Head["text"], "WolframLanguage"]]
```

<!-- => String -->

---

A sequence among the arguments of [Construct]() is spliced in:

```wl
NormalForm[TypeTheoryTerm[Construct[f, Unevaluated[1, 2], 3], "WolframLanguage"]]
```

<!-- => f[1, 2, 3] -->

---

So is `Sequence @@ l` of a list `l`:

```wl
NormalForm[TypeTheoryTerm[Construct[f, Sequence @@ {1, 2}, 3], "WolframLanguage"]]
```

<!-- => f[1, 2, 3] -->

---

A sequence of natural numbers has the type `ℕ...`:

```wl
TypeTheoryType[TypeTheoryTerm[Unevaluated[1, 2], "WolframLanguage"]]
```

<!-- => ℕ... -->

---

A sequence shows in brackets, and [Prepend]() puts an element in front of one, as in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[Prepend[Unevaluated[1, 2, 3], 0], "WolframLanguage"]]
```

<!-- => [0, 1, 2, 3] -->

---

A sequence among the elements of a sequence is spliced in, as is `Unevaluated @@ l` of a list `l`:

```wl
NormalForm[TypeTheoryTerm[Unevaluated[Unevaluated[1, 2], 3, Unevaluated @@ {4, 5}], "WolframLanguage"]]
```

<!-- => [1, 2, 3, 4, 5] -->

---

A sequence of expressions of every kind:

```wl
NormalForm[TypeTheoryTerm[Typed[Unevaluated[1, "a", f[x]], Expressions...], "WolframLanguage"]]
```

<!-- => [1, "a", f[x]] -->

---

A function whose last binder has the type `Expressions...` takes the arguments that are left as one sequence:

```wl
TypeTheoryType[Function[{Typed[s, Expressions...]}, Construct[g, s]], "WolframLanguage"]
```

<!-- => Expressions... → Expressions -->

A variable of the type `Expressions...` is spliced where it stands among the arguments:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[s, Expressions...]}, Construct[g, 0, s]][1, 2], "WolframLanguage"]]
```

<!-- => g[0, 1, 2] -->

---

In a quotation, a variable in scope is the expression it stands for:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[x, Expressions]}, HoldForm[f[x, x]]][1], "WolframLanguage"]]
```

<!-- => f[1, 1] -->

---

[Construct]() of a function that is no expression applies it:

```wl
NormalForm[TypeTheoryTerm[Construct[Typed[n, NonNegativeIntegers] |-> n + 1, 2], "WolframLanguage"]]
```

<!-- => 3 -->

## Properties and Relations

The declaration of [Expressions]():

```wl
TypeTheoryEnvironment["WolframLanguage"][Expressions]
```

<!-- => inductive Expressions : Type | atom : Atoms → Expressions | Construct : Expressions → Expressions... → Expressions -->

---

[Head]() gives the head of an expression:

```wl
TypeTheoryType[Head, "WolframLanguage"]
```

<!-- => Expressions → Expressions -->

---

The head of [Construct]() of a head and a sequence is that head, for every head and sequence:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[h, Expressions], Typed[s, Expressions...]}, Head[Construct[h, s]]], "WolframLanguage"],
    TypeTheoryTerm[Function[{Typed[h, Expressions], Typed[s, Expressions...]}, h], "WolframLanguage"]
]
```

<!-- => True -->

---

An expression that is not an atom is [Construct]() of its head and its arguments:

```wl
NormalForm[TypeTheoryTerm[Construct[Head[f[1, 2]], Arguments[f[1, 2]]], "WolframLanguage"]]
```

<!-- => f[1, 2] -->

---

[AtomQ]() computes whether an expression is an atom:

```wl
WeakHeadNormalForm[TypeTheoryTerm[AtomQ[f[1]], "WolframLanguage"]]
```

<!-- => false -->

---

[SameQ]() computes whether two expressions are the same, part by part:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[Construct[f, 1, 2], f[1, 2]], "WolframLanguage"]]
```

<!-- => true -->

---

Two expressions with their arguments in another order are not the same:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[f[1, 2], f[2, 1]], "WolframLanguage"]]
```

<!-- => false -->

---

A function that [TypeTheoryFormalize]() does not translate takes an [Expressions]() for each argument:

```wl
styled[x_] := Style[x, Bold];
Last[TypeTheoryFormalize[styled, TypeTheoryEnvironment["WolframLanguage"]]]
```

<!-- => axiom styled : Expressions → Expressions -->

## Possible Issues

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

The empty sequence on its own has no type to give its elements:

```wl
TypeTheoryType[TypeTheoryTerm[Unevaluated[], "WolframLanguage"]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

[Typed]() gives it one:

```wl
TypeTheoryType[Typed[Unevaluated[], Expressions...], "WolframLanguage"]
```

<!-- => Expressions... -->

---

A declared constant computes where an expression is expected, so `1 + 2` is the atom 3, and [HoldForm]() keeps it as it is written:

```wl
NormalForm[TypeTheoryTerm[Construct[f, 1 + 2, HoldForm[1 + 2]], "WolframLanguage"]]
```

<!-- => f[3, 1 + 2] -->

---

The quoted `1 + 2` is the expression `Plus[1, 2]`, not the same as 3:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[1 + 2], 3], "WolframLanguage"]]
```

<!-- => false -->

---

[Expressions]() is a constant of the Wolfram Language environment, not of the prelude:

```wl
TypeTheoryType[Expressions, TypeTheoryEnvironment["Prelude"]]
```

<!-- => Failure["ElaborationFailed", ...] -->
