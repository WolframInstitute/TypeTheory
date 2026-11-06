---
Template: Symbol
Name: WeakHeadNormalForm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/WeakHeadNormalForm
Keywords: [reduction, weak head normal form, computation, beta reduction, unfolding, recursor, head, constructor, lazy evaluation]
SeeAlso: [NormalForm, DefinitionallyEqualQ, TypeTheoryCheck, TypeTheoryTerm, TypeTheoryDefinition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation]
---

## Usage

<code>[WeakHeadNormalForm]()[*term*]</code> reduces the [TypeTheoryTerm]() *term* until its head can no longer reduce.

## Details & Options

- Reduction applies functions to their arguments, unfolds definitions and local definitions, applies a recursor to a constructor, takes a field of a constructed structure, and computes the operations on natural number literals. Theorems never unfold.
- Only the head is reduced: the arguments of a constructor, and the body of a function, stay as they are. So the result says which constructor a term is, or that it is a function, without computing the rest. [NormalForm]() reduces every part.
- A [TypeTheoryTerm]() without an environment is in the default environment, the prelude unless [SetTypeTheoryEnvironment]() set another.
- The kernel reduces a term to its weak head normal form to compare it with another, as [DefinitionallyEqualQ]() and [TypeTheoryCheck]() do.

## Basic Examples

A function applied to an argument reduces to its body, and the list it gives keeps its element as it is:

```wl
WeakHeadNormalForm[TypeTheoryTerm[(x |-> {x + 1})[41]]]
```

<!-- => {41 + 1} -->

---

Only the head reduces, here the list's first constructor, and its elements stay as they are:

```wl
WeakHeadNormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {1 + 1, 2 3} -->

[NormalForm]() computes them:

```wl
NormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}]]
```

<!-- => {2, 6} -->

---

The second of two rules applies to `f[1, 2, 3]`: the weak head normal form says that a rule applied, and leaves its result to compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[ReplaceList[f[1, 2, 3], {f[x_, y_] :> {y, x}, f[x__] :> {x}}]]]]
```

<!-- => some[Construct[List, Sequence @@ {Arguments[f[1, 2, 3]]}]] -->

## Scope

A Boolean that decides a proposition reduces to its value:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2^10 == 1024]]]
```

<!-- => true -->

---

A definition unfolds, here [Not]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

---

A recursor applied to a literal computes, and so do the operations on literals, so the factorial of 5 reduces all the way to the number:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Naturals][Naturals &, 1, {k, r} |-> (k + 1) r, 5]]]
```

<!-- => 120 -->

---

The argument of a function is not reduced before the function is applied:

```wl
WeakHeadNormalForm[TypeTheoryTerm[(l |-> Prepend[l, 1 + 1])[{2 + 2}]]]
```

<!-- => {1 + 1, 2 + 2} -->

---

A [Join]() of lists reduces to its first element in front of the rest, which is left to compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Join[{1 + 1}, {2, 3}]]]
```

<!-- => Prepend[List_rec[(t ∶ {ℕ}) ↦ {ℕ}, {2, 3}, (x ∶ ℕ) (rest ∶ {ℕ}) (r ∶ {ℕ}) ↦ Prepend[r, x], {}], 1 + 1] -->

## Properties and Relations

A function is in weak head normal form, its body as it is; [NormalForm]() would reduce `n + 0` to `n`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[n |-> n + 0]]
```

<!-- => (n ∶ ℕ) ↦ n + 0 -->

---

A theorem, which does not unfold:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

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
