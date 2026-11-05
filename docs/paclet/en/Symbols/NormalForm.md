---
Template: Symbol
Name: NormalForm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NormalForm
Keywords: [normal form, reduction, computation, evaluation, reduce, beta reduction, unfolding]
SeeAlso: [WeakHeadNormalForm, DefinitionallyEqualQ, TypeTheoryTerm, TypeTheoryType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [PatternsAndRewriting, RulesAndComputation]
---

## Usage

<code>[NormalForm]()[*term*]</code> reduces the [TypeTheoryTerm]() *term* and every part of it, under its binders too, until nothing can reduce: its normal form.

## Details & Options

- [NormalForm]() is [WeakHeadNormalForm]() applied to the term, then to each of its parts, as Lean's `#reduce`: a function's body is reduced with its variable free, and the arguments of a stuck application are reduced.
- It unfolds definitions, computes recursors on constructors and natural numbers as literals, so a closed term of data reduces to its value.
- Two terms are equal by computation when their normal forms are the same, which [DefinitionallyEqualQ]() decides without computing them in full.

## Basic Examples

A list whose elements compute:

```wl
NormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {2, 6} -->

---

[WeakHeadNormalForm]() reduces only the head, here the list's first constructor:

```wl
WeakHeadNormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {1 + 1, 2 6} -->

## Scope

The body of a function reduces with its variable free:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n -->

---

A rewriting of expressions reduces to the expression it gives:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
NormalForm[TypeTheoryTerm[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], wolfram]]
```

<!-- => {HoldForm[{{1}, {2, 3}}], HoldForm[{{1, 2}, {3}}]} -->

## Possible Issues

A term with a free variable reduces only as far as it computes:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> 0 + n]]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[...] -->
