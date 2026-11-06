---
Template: Symbol
Name: Expressions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Expressions
Keywords: [Wolfram Language, expressions, Construct, atom, head, arguments, sequences, Unevaluated, nested inductive type, recursor, pattern matching, Match, rewriting, derivative, prelude]
SeeAlso: [Atoms, Arguments, Strings, ExpressionEvaluate, Match, MatchPart, NormalForm, TypeTheoryFormalize]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

[Expressions]() is the type of the expressions of the Wolfram Language: an atom, <code>"atom"[*a*]</code>, or a head applied to the sequence of its arguments, <code>[Construct]()[*h*, *a*, *b*, ...]</code>, which is <code>*h*[*a*, *b*, ...]</code>.

## Details & Options

- [Expressions]() is an inductive type of the prelude with two constructors: `"atom"`, of the type `Atoms -> Expressions`, and the one written and shown as [Construct](), of the type `Expressions -> Expressions... -> Expressions`, which takes the arguments of an expression as one sequence. It is a nested inductive type: its recursor has a second motive, for the sequences of arguments.
- `A...` is the type of the sequences of any number of elements of `A`, as the pattern `p...` takes any number of expressions. A sequence is written held, `Unevaluated[a, b, ...]`, as the Wolfram Language holds the arguments it passes on, and shows in brackets, `[a, b, ...]`. Among its elements, a sequence `Unevaluated[...]`, and `Sequence @@ l` and `Unevaluated @@ l` of a list `l`, are spliced in, and <code>[Prepend]()[*s*, *x*]</code> puts *x* in front of a sequence *s*.
- The last explicit binder of a function, if its type is `A...`, takes the arguments that are left as one sequence, each an `A` or a sequence spliced in, as the Wolfram Language gives a function its arguments: `Construct[h, a, b]` gives `h` the sequence of `a` and `b`, and `Construct[h]` the empty one, `h[]`.
- [Construct]() of a term that is no expression applies it, as [Construct]() does in the Wolfram Language, so its type is the type of the result.
- Where an expression is expected, a term is read as the Wolfram Language evaluates it: a symbol that names nothing stands for itself, a head that names nothing applied to arguments is that expression, `f[1][2]` is the expression with the head `f[1]`, `{a, b}` is the expression `List[a, b]`, and a number or a string is its atom, a natural number and a string by a coercion. A declared function computes where its arguments are of its types, so `1 + 2` is the expression `3`, and is the expression it writes where an argument is an expression, so `a + b c` is that sum, as the Wolfram Language leaves it. A symbol of the Wolfram Language whose constants are no expressions, as [Plus]() or [True](), is the symbol, and a fraction of integers is the rational number.
- <code>[Unevaluated]()[*e*]</code> keeps *e* from computing, as the Wolfram Language passes *e* on unevaluated: `Unevaluated[1 + 2]` is the expression `1 + 2`. A variable of expressions in an expression is the expression it stands for. An expression shows bare, without the [Unevaluated](). [HoldForm]() is a head as any other.
- Where nothing says what is expected, the whole term of a query, as <code>[TypeTheoryType]()[f[1, 2]]</code> or <code>[TypeTheoryType]()[a + b c]</code>, is an expression too. Inside a term, as in the value of a declaration, a head that names nothing is an expression where it is applied to an expression, as `f[x]` of a variable `x` of expressions, a template, and is no term where it is applied to numbers alone, as a misspelled name, or the name being defined, which a definition may not use, most often is. A lone symbol that names nothing is no term anywhere, and <code>[Typed]()[*s*, [Expressions]()]</code> makes it one.
- Nothing in the kernel evaluates an expression as the Wolfram Language does: the arguments of `b + a` are not sorted, and [ExpressionEvaluate]() is the axiom for what the Wolfram Language evaluates an expression to.
- [Head](), [Arguments](), [AtomQ]() and [SameQ]() are definitions by the recursor of [Expressions](), which the kernel computes, and so are [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated](). [ExpressionEvaluate](), the expression the Wolfram Language evaluates an expression to, is an axiom.
- [Unevaluated]() of one expression is that one argument, as the Wolfram Language passes it on: quoted where an expression is expected, as among the arguments of [Construct](), and the element itself anywhere else. [Unevaluated]() of none or several is a sequence.
- [TypeTheoryTerm](), [TypeTheoryType]() and [TypeTheoryProof]() keep an [Unevaluated]() they are given, so a sequence on its own is <code>[TypeTheoryType]()[Unevaluated[1, 2]]</code>.
- The prelude, and the integers and the rationals that extend it, have [Expressions](); the constructive, homotopy and cubical environments do not.
- [TypeTheoryFormalize]() gives a function that does not translate, and that it is given no type for, the type `Expressions -> ... -> Expressions`, one [Expressions]() for each argument.

## Basic Examples

The expressions are a type of the prelude:

```wl
TypeTheoryType[Expressions]
```

<!-- => Type -->

---

[Expressions]() has two constructors, one for an atom and one for a head applied to a sequence of arguments:

```wl
TypeTheoryEnvironment["Prelude"][Expressions]
```

<!-- => inductive Expressions : Type | atom : Atoms → Expressions | Construct : Expressions → Expressions... → Expressions -->

---

[Construct]() makes an expression of a head and the sequence of its arguments:

```wl
TypeTheoryType[Construct]
```

<!-- => Expressions → Expressions... → Expressions -->

---

A sum of symbols that name nothing is an expression, as in the Wolfram Language:

```wl
TypeTheoryType[a + b c]
```

<!-- => Expressions -->

---

`f` names nothing, so `f[1, 2]` is an expression, and the kernel rewrites it by a rule:

```wl
NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_] :> {y, x}]]]
```

<!-- => {2, 1} -->

## Scope

An atom makes an expression:

```wl
TypeTheoryType["atom"]
```

<!-- => Atoms → Expressions -->

---

A natural number is an expression where one is expected, by a coercion to its atom:

```wl
TypeTheoryEnvironment["Prelude"]["NaturalExpressionCoercion"]
```

<!-- => coercion NaturalExpressionCoercion : ℕ → Expressions := (n ∶ ℕ) ↦ atom[naturalAtom[n]] -->

---

The head of an expression is an expression:

```wl
TypeTheoryType[Head]
```

<!-- => Expressions → Expressions -->

---

The arguments of a sum are a sequence of expressions:

```wl
TypeTheoryType[Arguments[a + b + c]]
```

<!-- => Expressions... -->

---

An expression with a variable of expressions in it is a template, a function of expressions:

```wl
TypeTheoryType[Typed[x, Expressions] |-> x^2 + x]
```

<!-- => Expressions → Expressions -->

The variable is the expression it is given, so the template filled in with `a + b` is `(a + b)^2 + (a + b)`, by computation:

```wl
TypeTheoryProof[(Typed[x, Expressions] |-> x^2 + x)[a + b] == (a + b)^2 + (a + b), {"Reflexivity"}]
```

<!-- => Proof complete -->

---

A function whose last binder has the type `Expressions...` takes the sequence of its arguments, as `g[0, ##] &` does:

```wl
TypeTheoryType[Typed[s, Expressions...] |-> Construct[g, 0, s]]
```

<!-- => Expressions... → Expressions -->

So it takes two arguments, or any other number:

```wl
TypeTheoryType[(Typed[s, Expressions...] |-> Construct[g, 0, s])[1, 2]]
```

<!-- => Expressions -->

---

[Construct]() of a function that is no expression applies it, so the result is a natural number:

```wl
TypeTheoryType[Construct[n |-> n + 1, 2]]
```

<!-- => ℕ -->

## Applications

Two rules for a derivative, one for a sum and one for a power, written as a term, are a function from an expression to its matches:

```wl
TypeTheoryType[Typed[{d[u_ + v_] :> d[u] + d[v], d[x^n_] :> n x^(n - 1)}, Expressions -> Match[Expressions]]]
```

<!-- => Expressions → Match[Expressions] -->

[ReplaceRepeated]() applies them in the kernel until neither applies:

```wl
NormalForm[TypeTheoryTerm[ReplaceRepeated[d[x^2 + x^3], {d[u_ + v_] :> d[u] + d[v], d[x^n_] :> n x^(n - 1)}]]]
```

<!-- => 2 x^(2 - 1) + 3 x^(3 - 1) -->

---

A statement that the rule for a power rewrites `d[x^n]` for every exponent *n*:

```wl
powerRule = TypeTheoryTerm[ForAll[{Typed[n, Expressions]}, Replace[d[x^n], d[x^m_] :> m x^(m - 1)] == n x^(n - 1)]]
```

<!-- => ∀_n∶Expressions Replace[d[x^n], d[x^m_] :> m x^(m - 1)] == n x^(n - 1) -->

The kernel proves it by computation, with *n* a variable:

```wl
TypeTheoryProof[powerRule, {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

[Expressions]() is a nested inductive type: its recursor has a motive for expressions and one for the sequences of their arguments:

```wl
TypeTheoryType[InductiveRecursor[Expressions]]
```

<!-- => ∀_m1∶Expressions → Sort u ∀_m2∶Expressions... → Sort u (∀_x∶Atoms m1[atom[x]]) → (∀_x∶Expressions ∀_x1∶Expressions... m1[x] → m2[x1] → m1[x[x1]]) → m2[[]] → (∀_x∶Expressions ∀_s∶Expressions... m1[x] → m2[s] → m2[[x, s]]) → ∀_t∶Expressions m1[t] -->

---

The head of [Construct]() of a head and a sequence is that head, for every head and every sequence:

```wl
TypeTheoryProof[ForAll[{Typed[h, Expressions], Typed[s, Expressions...]}, Head[Construct[h, s]] == h], {"Introduce"[h, s], "Reflexivity"}]
```

<!-- => Proof complete -->

---

[SameQ]() compares two expressions, a Boolean:

```wl
TypeTheoryType[SameQ]
```

<!-- => Expressions → Expressions → 𝔹 -->

[Construct]() of `f`, 1 and 2 is the expression `f[1, 2]`, by computation:

```wl
TypeTheoryProof[SameQ[Construct[f, 1, 2], f[1, 2]] == "true", {"Reflexivity"}]
```

<!-- => Proof complete -->

---

A function that [TypeTheoryFormalize]() does not translate takes an [Expressions]() for each argument:

```wl
styled[x_] := Style[x, Bold];
Last[TypeTheoryFormalize[styled]]
```

<!-- => axiom styled : Expressions → Expressions -->

## Possible Issues

On its own, a symbol that names nothing is no term, as it is most often a misspelled name:

```wl
TypeTheoryType[f]
```

<!-- => Failure["ElaborationFailed", ...] -->

An application of one is an expression, as in the Wolfram Language:

```wl
TypeTheoryType[f[1, 2]]
```

<!-- => Expressions -->

Where an expression is expected, it is that expression:

```wl
TypeTheoryType[Typed[f[1, 2], Expressions]]
```

<!-- => Expressions -->

---

A declared constant computes where an expression is expected, so `1 + 2` is the atom 3, and [Unevaluated]() keeps it as it is written:

```wl
NormalForm[TypeTheoryTerm[Construct[f, 1 + 2, Unevaluated[1 + 2]]]]
```

<!-- => f[3, 1 + 2] -->

---

Nothing evaluates a quoted expression, so the arguments of a quoted [Plus]() are not sorted, as the Wolfram Language's evaluation would sort them, and two sums in another order are different expressions:

```wl
TypeTheoryProof[SameQ[Unevaluated[a + b], Unevaluated[b + a]] == "false", {"Reflexivity"}]
```

<!-- => Proof complete -->

---

[TypeTheoryType]() keeps the [Unevaluated]() it is given, so `Unevaluated[1, 2]` is a sequence of any length, not `Sequence[1, 2]`, a sequence of exactly two elements:

```wl
TypeTheoryType[Unevaluated[1, 2]]
```

<!-- => ℕ... -->

---

The constructive environment does not extend the prelude, and has no expressions:

```wl
TypeTheoryType[Expressions, "Constructive"]
```

<!-- => Failure["ElaborationFailed", ...] -->
