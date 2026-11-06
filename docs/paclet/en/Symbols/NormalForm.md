---
Template: Symbol
Name: NormalForm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NormalForm
Keywords: [normal form, reduction, computation, evaluation, reduce, beta reduction, unfolding, under binders, #reduce]
SeeAlso: [WeakHeadNormalForm, DefinitionallyEqualQ, TypeTheoryTerm, TypeTheoryType, TypeTheoryDefinition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [PatternsAndRewriting, RulesAndComputation]
---

## Usage

<code>[NormalForm]()[*term*]</code> reduces the [TypeTheoryTerm]() *term* and every part of it, under its binders too, until nothing can reduce: its normal form.

## Details & Options

- [NormalForm]() is [WeakHeadNormalForm]() applied to the term, then to each of its parts, as Lean's `#reduce`: a function's body is reduced with its variable free, and the arguments of an application that is stuck are reduced.
- It applies functions to their arguments, unfolds definitions and local definitions, computes recursors on constructors and natural numbers as literals, and takes the fields of a structure, so a closed term of data reduces to its value. Theorems never unfold.
- A [TypeTheoryTerm]() without an environment is in the default environment, the prelude unless [SetTypeTheoryEnvironment]() set another. While it is the prelude, a term that names what only <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code> declares is read in that environment.
- An expression of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code> shows bare, without the [HoldForm]() that quotes it.
- Two terms are equal by computation when their normal forms are the same, which [DefinitionallyEqualQ]() decides without computing them in full.

## Basic Examples

A list whose elements compute:

```wl
NormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {2, 6} -->

---

A function applied to an argument:

```wl
NormalForm[TypeTheoryTerm[(Typed[n, Naturals] |-> n * n)[7]]]
```

<!-- => 49 -->

---

The body of a function reduces with its variable free:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n -->

## Scope

A Boolean decided:

```wl
NormalForm[TypeTheoryTerm[Decide[2 == 2]]]
```

<!-- => true -->

---

The operations on natural numbers compute on literals of any size:

```wl
NormalForm[TypeTheoryTerm[2^100]]
```

<!-- => 1267650600228229401496703205376 -->

---

A local definition unfolds:

```wl
NormalForm[TypeTheoryTerm[With[{x = 2}, x + 1]]]
```

<!-- => 3 -->

---

A field of a pair:

```wl
NormalForm[TypeTheoryTerm["pair"[1 + 1, 2][[1]]]]
```

<!-- => 2 -->

---

The arguments of a constructor reduce:

```wl
NormalForm[TypeTheoryTerm["some"[1 + 1]]]
```

<!-- => some[2] -->

---

A recursor applied to a literal:

```wl
NormalForm[TypeTheoryTerm[InductiveRecursor[Naturals][Typed[k, Naturals] |-> Naturals, 1, {Typed[k, Naturals], Typed[r, Naturals]} |-> 2 r, 5]]]
```

<!-- => 32 -->

---

Functions of lists compute:

```wl
NormalForm[TypeTheoryTerm[Join[{1}, {2, 3}]]]
```

<!-- => {1, 2, 3} -->

---

A proposition reduces too:

```wl
NormalForm[TypeTheoryTerm[2 + 2 == 4]]
```

<!-- => 4 == 4 -->

---

A definition unfolds:

```wl
NormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

---

Under a quantifier:

```wl
NormalForm[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]]]
```

<!-- => ∀_n∶ℕ n == n -->

---

Under two binders:

```wl
NormalForm[TypeTheoryTerm[Typed[f, Naturals -> Naturals] |-> (Typed[n, Naturals] |-> f[n + 0])]]
```

<!-- => (f ∶ ℕ → ℕ) (n ∶ ℕ) ↦ f[n] -->

---

The argument of a variable reduces:

```wl
NormalForm[TypeTheoryTerm[Typed[g, Naturals -> Naturals] |-> g[2 + 3]]]
```

<!-- => (g ∶ ℕ → ℕ) ↦ g[5] -->

---

A definition of your own:

```wl
doubled = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Typed[n, Naturals] |-> n + n]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

It unfolds:

```wl
NormalForm[TypeTheoryTerm[Doubled[21], doubled]]
```

<!-- => 42 -->

---

A rewriting of expressions reduces to the expressions it gives:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], "WolframLanguage"]]
```

<!-- => {{{1}, {2, 3}}, {{1, 2}, {3}}} -->

---

The sequence of the arguments of an expression:

```wl
NormalForm[TypeTheoryTerm[Arguments[f[1, 2]], "WolframLanguage"]]
```

<!-- => [1, 2] -->

---

A quoted expression shows bare:

```wl
NormalForm[TypeTheoryTerm[HoldForm[1 + 2], "WolframLanguage"]]
```

<!-- => 1 + 2 -->

---

A type reduces:

```wl
NormalForm[TypeTheoryTerm[Match[NonNegativeIntegers], "WolframLanguage"]]
```

<!-- => {ℕ} -->

## Properties and Relations

[WeakHeadNormalForm]() reduces only the head, here the list's first constructor:

```wl
WeakHeadNormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {1 + 1, 2 3} -->

---

[WeakHeadNormalForm]() leaves a function as it is:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n + 0 -->

---

Terms with the same normal form are equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[{1 + 1, 2 * 3}], TypeTheoryTerm[{2, 6}]]
```

<!-- => True -->

---

A theorem, which does not unfold:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Its proof stays a name:

```wl
NormalForm[TypeTheoryTerm[TwoPlusTwo, arithmetic]]
```

<!-- => TwoPlusTwo -->

## Possible Issues

A term with a free variable reduces only as far as it computes: addition recurs on its second argument, here the variable:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> 0 + n]]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 1, n] -->

---

[NormalForm]() takes a [TypeTheoryTerm](); an expression on its own evaluates and stays as it is:

```wl
NormalForm[1 + 1]
```

<!-- => NormalForm[2] -->

---

A term that does not type-check gives a [Failure]():

```wl
NormalForm[TypeTheoryTerm[1 + "true"]]
```

<!-- => Failure["TypeMismatch", ...] -->
