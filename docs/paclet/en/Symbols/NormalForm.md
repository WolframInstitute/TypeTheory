---
Template: Symbol
Name: NormalForm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NormalForm
Keywords: [normal form, reduction, computation, evaluation, reduce, beta reduction, unfolding, under binders, proof by computation, #reduce]
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
- Two terms are equal by computation when their normal forms are the same, which [DefinitionallyEqualQ]() decides without computing them in full, and `"Reflexivity"` proves an equation whose two sides are.

## Basic Examples

The elements of a list compute:

```wl
NormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {2, 6} -->

---

The body of a function reduces with its variable free:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n -->

---

The factorial, defined by the recursor of the natural numbers:

```wl
factorials = TypeTheoryEnvironment[{TypeTheoryDefinition[FactorialOf, Typed[n, Naturals] |->
    InductiveRecursor[Naturals][Typed[k, Naturals] |-> Naturals, 1, {Typed[k, Naturals], Typed[r, Naturals]} |-> (k + 1) r, n]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

The factorial of 20 computes:

```wl
NormalForm[TypeTheoryTerm[FactorialOf[20], factorials]]
```

<!-- => 2432902008176640000 -->

## Scope

A local definition unfolds, here of a function used twice:

```wl
NormalForm[TypeTheoryTerm[With[{square = Typed[n, Naturals] |-> n n}, square[square[3]]]]]
```

<!-- => 81 -->

---

[Not]() is a definition, which unfolds:

```wl
NormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

---

A rewriting of expressions reduces to the expression it gives, shown bare, here the logarithm of a product split into a sum:

```wl
NormalForm[TypeTheoryTerm[ReplaceRepeated[HoldForm[log[a b c]], log[x_ y_] :> log[x] + log[y]], "WolframLanguage"]]
```

<!-- => log[a] + (log[b] + log[c]) -->

## Applications

An equation whose two sides compute to the same number:

```wl
NormalForm[TypeTheoryTerm[2^10 == 1024]]
```

<!-- => 1024 == 1024 -->

So `"Reflexivity"` proves it:

```wl
TypeTheoryProof[2^10 == 1024, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

Under the quantifier, `n + 0` computes to `n`, since addition recurs on its second argument:

```wl
NormalForm[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]]]
```

<!-- => ∀_n∶ℕ n == n -->

So the statement is proved by computation, for every *n*:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

[WeakHeadNormalForm]() reduces only the head, here the list's first constructor:

```wl
WeakHeadNormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {1 + 1, 2 3} -->

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

A term with a free variable reduces only as far as it computes: addition recurs on its second argument, here the variable, so `0 + n` is stuck:

```wl
NormalForm[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, 0 + n == n]]]
```

<!-- => ∀_n∶ℕ ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 1, n] == n -->

So `"Reflexivity"` does not prove it, and the proof needs `"Induction"`:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

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
