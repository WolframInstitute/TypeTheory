---
Template: Symbol
Name: TypeTheoryAxiom
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryAxiom
Keywords: [axiom, declaration, assumption, postulate, excluded middle, classical logic, constructive, environment, conjecture, overloading, implementation, inconsistency]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, TypeTheoryRewriteRule, TypeTheoryAxiomClosure]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation]
---

## Usage

<code>[TypeTheoryAxiom]()[*name*, *type*]</code> declares *name* as an axiom of the given *type*, when added to a [TypeTheoryEnvironment]().

## Details & Options

- A declaration is inert until it is added to an environment with <code>[TypeTheoryEnvironment]()[*env*, {*declaration*}]</code> or <code>[Append]()[*env*, *declaration*]</code>, which check that *type* is a type.
- An axiom is assumed, not proved: it has a type and no value, so it never computes, and the kernel does not check that it is consistent with the environment. <code>[Information]()[*env*, "Axioms"]</code> lists the axioms of an environment, and [TypeTheoryAxiomClosure]() the axioms a term rests on.
- The prelude assumes `"propositionalExtensionality"`, `"quotientSoundness"` and `"choice"`, Lean's three axioms, and proves `"functionExtensionality"` and `"excludedMiddle"` from them. <code>[TypeTheoryEnvironment]()["Constructive"]</code> is the prelude without them and the theorems proved from them, a start for other axioms.
- An axiom may compute by rewrite rules, under rules that allow them: see [TypeTheoryRewriteRule]().
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear, and makes each level that nothing in the declaration decides one more, `"u_1"`, `"u_2"`, …, as Lean does.
- The option `"Implementation" -> f` names the Wolfram Language function `f`, a symbol, that computes the constant. The kernel never runs it, so the constant stays opaque to checking; <code>[Information]()[*term*, "Implementation"]</code> gives it, and a saved environment keeps only its name.
- The option `"Annotation" -> *data*` keeps *data* in the axiom's record as it is given: <code>[Information]()[[TypeTheoryTerm]()[*name*, *env*], "Annotation"]</code> gives it back, and [Normal]() and a saved environment keep it.
- The option `"Overloads" -> *operation*`, for [Plus](), [Times](), [Subtract](), [Power](), [Minus](), [LessEqual](), [Less](), [GreaterEqual]() or [Greater](), makes the constant one more meaning of the operation, chosen by the types of its arguments and the type expected, as the integers' and rationals' operations are, and the constant shows as the operation.

## Basic Examples

The prelude assumes three axioms:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Axioms"]
```

<!-- => {propositionalExtensionality, quotientSoundness, choice, ExpressionEvaluate} -->

---

Assume a natural number about which nothing is known:

```wl
mystery = TypeTheoryEnvironment[TypeTheoryAxiom[Mystery, Naturals]]
```

<!-- => TypeTheoryEnvironment summary box: 251 constants -->

Its declaration:

```wl
mystery[Mystery]
```

<!-- => axiom Mystery : ℕ -->

---

Assume the excluded middle in the constructive environment, which has no axioms:

```wl
classical = TypeTheoryEnvironment["Constructive", {
    TypeTheoryAxiom["excludedMiddle", ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->

Applied to a proposition, the axiom proves it or its negation:

```wl
TypeTheoryType["excludedMiddle"[2 + 2 == 5], classical]
```

<!-- => 2 + 2 == 5 ∨ ¬2 + 2 == 5 -->

## Scope

A predicate and a fact about it, both assumed:

```wl
primes = TypeTheoryEnvironment[{
    TypeTheoryAxiom[PrimeNumber, Naturals -> TypeUniverse[0]],
    TypeTheoryAxiom[TwoPrime, PrimeNumber[2]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 252 constants -->

The fact proves `PrimeNumber[1 + 1]`, which computes to its statement:

```wl
TypeTheoryProof[PrimeNumber[1 + 1], primes, {"Exact"[TwoPrime]}]
```

<!-- => Proof complete -->

---

An axiom of a function type, a function on the natural numbers:

```wl
measured = TypeTheoryEnvironment[TypeTheoryAxiom[Measure, TypeSpecifier[{Naturals} -> Naturals]]]
```

<!-- => TypeTheoryEnvironment summary box: 251 constants -->

[Format]() gives an axiom's symbol a display, which its declaration and every term use:

```wl
Format[Measure] := "\[Mu]";
measured[Measure]
```

<!-- => axiom μ : ℕ → ℕ -->

And a term that uses it:

```wl
TypeTheoryTerm[Typed[n, Naturals] |-> Measure[Measure[n]], measured]
```

<!-- => (n ∶ ℕ) ↦ μ[μ[n]] -->

---

A binder written without a type, here the type of the elements of a list, gets a universe parameter of its own, `"u_1"`:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom[Shuffle, ForAll[{A, Typed[list, {A}]}, {A}]]}][Shuffle]
```

<!-- => axiom Shuffle : ∀_A∶Type u_1 {A} → {A} -->

## Options

### UniverseParameters

The universe parameters named explicitly:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom[Shuffle, ForAll[{TypedImplicit[A, TypeUniverse[v + 1]]}, TypeSpecifier[{{A}} -> {A}]], "UniverseParameters" -> {v}]}][Shuffle]
```

<!-- => axiom Shuffle : ∀_{A∶Type v} {A} → {A} -->

---

A list of universe parameters must name every one the type uses:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom[Shuffle, ForAll[{TypedImplicit[A, TypeUniverse[v + 1]]}, TypeSpecifier[{{A}} -> {A}]], "UniverseParameters" -> {}]}]
```

<!-- => Failure["ElaborationFailed", ...] -->

### Annotation

A conjecture, assumed with a note of what it is:

```wl
goldbach = TypeTheoryEnvironment[{TypeTheoryAxiom[
    Goldbach,
    ForAll[{Typed[n, Naturals]}, Implies[n > 1, Exists[{Typed[p, Naturals], Typed[q, Naturals]}, 2 n == p + q]]],
    "Annotation" -> "Goldbach's conjecture, without primality"
]}]
```

<!-- => TypeTheoryEnvironment summary box: 251 constants -->

The annotation, as it was given:

```wl
Information[TypeTheoryTerm[Goldbach, goldbach], "Annotation"]
```

<!-- => "Goldbach's conjecture, without primality" -->

### Implementation

An axiom computed in the Wolfram Language by [PrimePi]():

```wl
counting = TypeTheoryEnvironment[{TypeTheoryAxiom[PrimeCounting, Naturals -> Naturals, "Implementation" -> PrimePi]}]
```

<!-- => TypeTheoryEnvironment summary box: 251 constants -->

The function that computes it:

```wl
Information[TypeTheoryTerm[PrimeCounting, counting], "Implementation"]
```

<!-- => PrimePi -->

The kernel never runs it, so the axiom does not compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[PrimeCounting[10], counting]]
```

<!-- => PrimeCounting[10] -->

### Overloads

A type of polynomials, with an addition that `+` stands for:

```wl
polynomials = TypeTheoryEnvironment[{
    TypeTheoryAxiom[Polynomial, TypeUniverse[1]],
    TypeTheoryAxiom[PolynomialAddition, TypeSpecifier[{Polynomial, Polynomial} -> Polynomial], "Overloads" -> Plus]
}]
```

<!-- => TypeTheoryEnvironment summary box: 252 constants -->

`f + g` adds two polynomials, chosen by the types of `f` and `g`:

```wl
TypeTheoryType[{Typed[f, Polynomial], Typed[g, Polynomial]} |-> f + g, polynomials]
```

<!-- => Polynomial → Polynomial → Polynomial -->

The sum of two numbers is still the natural numbers' addition:

```wl
TypeTheoryType[2 + 3, polynomials]
```

<!-- => ℕ -->

## Properties and Relations

An axiom has no value, so computation stops at it. Addition recurses on its second argument, so `0 + Mystery` stops at the recursor, waiting for a constructor that the axiom never gives:

```wl
WeakHeadNormalForm[TypeTheoryTerm[0 + Mystery, TypeTheoryEnvironment[TypeTheoryAxiom[Mystery, Naturals]]]]
```

<!-- => ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 1, Mystery] -->

---

A theorem proved from axioms rests on them, as [TypeTheoryAxiomClosure]() says:

```wl
primes = TypeTheoryEnvironment[{
    TypeTheoryAxiom[PrimeNumber, Naturals -> TypeUniverse[0]],
    TypeTheoryAxiom[TwoPrime, PrimeNumber[2]],
    TypeTheoryTheorem[OnePlusOnePrime, PrimeNumber[1 + 1], TwoPrime]
}]
```

<!-- => TypeTheoryEnvironment summary box: 253 constants -->

The axioms the theorem rests on:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[OnePlusOnePrime, primes]]
```

<!-- => <|PrimeNumber -> "Signature", TwoPrime -> "Proposition"|> -->

---

The excluded middle of the prelude rests on its three axioms:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["excludedMiddle"]]
```

<!-- => <|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|> -->

---

An opaque definition, unlike an axiom, has a value the kernel checks, so it rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Secret, TypeTheoryEnvironment[TypeTheoryDefinition[Secret, Typed[42, Naturals], "Opaque" -> True]]]]
```

<!-- => <||> -->

## Possible Issues

An axiom's type must be a type:

```wl
TypeTheoryEnvironment[TypeTheoryAxiom[Five, 5]]
```

<!-- => Failure["TypeExpected", ...] -->

---

The prelude proves the excluded middle from its axioms, so the name is taken there:

```wl
TypeTheoryEnvironment[TypeTheoryAxiom["excludedMiddle", ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]]
```

<!-- => Failure["AlreadyDeclared", ...] -->

---

The kernel does not check that an axiom is consistent. Assuming [False]() proves anything, here `2 + 2 == 5`:

```wl
absurd = TypeTheoryEnvironment[{
    TypeTheoryAxiom[Absurd, False],
    TypeTheoryTheorem[TwoPlusTwoFive, 2 + 2 == 5, "falseElimination"[Absurd]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 252 constants -->

The theorem it declares:

```wl
absurd[TwoPlusTwoFive]
```

<!-- => theorem TwoPlusTwoFive : 2 + 2 == 5 -->

[TypeTheoryAxiomClosure]() shows what it rests on:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[TwoPlusTwoFive, absurd]]
```

<!-- => <|Absurd -> "Proposition"|> -->

---

`"Implementation"` takes a symbol, not a pure function:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom[PrimeCounting, Naturals -> Naturals, "Implementation" -> (PrimePi[#] &)]}]
```

<!-- => Failure["InvalidOption", ...] -->

---

`"Overloads"` takes only the operations whose meanings elaboration chooses by type:

```wl
TypeTheoryEnvironment[{
    TypeTheoryAxiom[Polynomial, TypeUniverse[1]],
    TypeTheoryAxiom[PolynomialMaximum, TypeSpecifier[{Polynomial, Polynomial} -> Polynomial], "Overloads" -> Max]
}]
```

<!-- => Failure["OverloadedOperation", ...] -->
