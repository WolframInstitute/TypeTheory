---
Template: Symbol
Name: NormalForm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NormalForm
Keywords: [normal form, reduction, computation, evaluation, reduce, beta reduction, unfolding, under binders, proof by computation, #reduce]
SeeAlso: [WeakHeadNormalForm, DefinitionallyEqualQ, TypeTheoryExpression, TypeTheoryTerm, TypeTheoryType, TypeTheoryDefinition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [PatternsAndRewriting, RulesAndComputation]
---

## Usage

<code>[NormalForm]()[*term*]</code> reduces the [TypeTheoryTerm]() *term* and every part of it, under its binders too, until nothing can reduce: its normal form.

## Details & Options

- [NormalForm]() is [WeakHeadNormalForm]() applied to the term, then to each of its parts, as Lean's `#reduce`: a function's body is reduced with its variable free, and the arguments of an application that is stuck are reduced.
- It applies functions to their arguments, unfolds definitions and local definitions, computes recursors on constructors and natural numbers as literals, and takes the fields of a structure, so a closed term of data reduces to its value. Theorems and axioms never unfold.
- A [TypeTheoryTerm]() without an environment is in the default environment, the prelude unless [SetTypeTheoryEnvironment]() set another.
- An expression of the Wolfram Language, of the type [Expressions](), shows bare, without the [Unevaluated]() that quotes it.
- A value whose reading alone does not elaborate again, as a lone string, which on its own names a constant, the empty list, a value of a sum or `"none"`, comes back ascribed its type, <code>[Typed]()[*value*, *type*]</code>, so that the result elaborates to a term of the same type; its reading in the Wolfram Language, [TypeTheoryExpression](), is the same.
- Two terms are equal by computation when their normal forms are the same, which [DefinitionallyEqualQ]() decides without computing them in full, and `"Reflexivity"` proves an equation whose two sides are.

## Basic Examples

The body of a function reduces with its variable free:

```wl
NormalForm[TypeTheoryTerm[n |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n -->

---

The factorial, defined by the recursor of the natural numbers:

```wl
factorials = TypeTheoryEnvironment[{TypeTheoryDefinition[FactorialOf, n |-> InductiveRecursor[Naturals][Naturals &, 1, {k, r} |-> (k + 1) r, n]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The definition unfolds and the recursor computes on the literal, here the factorial of 20:

```wl
NormalForm[TypeTheoryTerm[FactorialOf[20], factorials]]
```

<!-- => 2432902008176640000 -->

---

A rewriting of expressions reduces to the expression it gives, shown bare, here the logarithm of a product split into a sum:

```wl
NormalForm[TypeTheoryTerm[ReplaceRepeated[log[a b c], log[x_ y_] :> log[x] + log[y]]]]
```

<!-- => log[a] + (log[b] + log[c]) -->

## Scope

A local definition unfolds under the binder, and the body keeps its variable:

```wl
NormalForm[TypeTheoryTerm[m |-> With[{pair = Typed[x, Naturals] |-> {x, x}}, pair[m]]]]
```

<!-- => (m ∶ ℕ) ↦ {m, m} -->

---

[Not]() is a definition, which unfolds:

```wl
NormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

---

An axiom does not unfold, but its argument reduces, here to 3:

```wl
NormalForm[TypeTheoryTerm[ExpressionEvaluate[1 + 2]]]
```

<!-- => ExpressionEvaluate[3] -->

## Applications

Under the quantifier, `n + 0` computes to `n`, since addition recurs on its second argument:

```wl
NormalForm[TypeTheoryTerm[ForAll[{n}, n + 0 == n]]]
```

<!-- => ∀_n∶ℕ n == n -->

So the statement is proved by computation, for every *n*:

```wl
TypeTheoryProof[ForAll[{n}, n + 0 == n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

[WeakHeadNormalForm]() reduces only the head, here the list's first constructor, and leaves its elements:

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

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its proof stays a name:

```wl
NormalForm[TypeTheoryTerm[TwoPlusTwo, arithmetic]]
```

<!-- => TwoPlusTwo -->

## Possible Issues

A term with a free variable reduces only as far as it computes: addition recurs on its second argument, here the variable, so `0 + n` is stuck:

```wl
NormalForm[TypeTheoryTerm[ForAll[{n}, 0 + n == n]]]
```

<!-- => ∀_n∶ℕ ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 1, n] == n -->

So `"Reflexivity"` does not prove it, and the proof needs `"Induction"`:

```wl
TypeTheoryProof[ForAll[{n}, 0 + n == n], {"Introduce"[n], "Reflexivity"}]
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
