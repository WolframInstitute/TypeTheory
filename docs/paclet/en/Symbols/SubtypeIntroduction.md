---
Template: Symbol
Name: SubtypeIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtypeIntroduction
Keywords: [subtype, introduction, element, property, prelude, classical logic]
SeeAlso: [Subtype, ExistsIntroduction, NonemptyIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtypeIntroduction]()[*x*, *h*]</code> is the element *x* of <code>[Subtype]()[*P*]</code>, with a proof *h* of <code>*P*[*x*]</code>.

## Details & Options

- [SubtypeIntroduction]() is the constructor of [Subtype]().
- The type of *x* and the property *P* are implicit arguments. *P* is found from the expected type: the type of *h* alone does not say which property it is.

## Basic Examples

The statement of [SubtypeIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtypeIntroduction]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} ∀_x∶α P[x] → Subtype[P] -->

---

4 is a natural number of at least 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtypeIntroduction[4, LessEqualStep[LessEqualStep[LessEqualReflexivity]]]], TypeTheoryTerm[Subtype[Function[{Typed[n, Naturals]}, 2 <= n]]]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

[Typed]() gives the expected type inside the term:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[SubtypeIntroduction[4, LessEqualStep[LessEqualStep[LessEqualReflexivity]]], Subtype[Function[{Typed[n, Naturals]}, 2 <= n]]]]]
```

<!-- => Subtype[(n ∶ ℕ) ↦ 2 ≤ n] -->

## Applications

A function on the numbers of at least 2 takes the number from the first field:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[s, Subtype[Function[{Typed[n, Naturals]}, 2 <= n]]]}, s[[1]] - 2]]]
```

<!-- => Subtype[(n ∶ ℕ) ↦ 2 ≤ n] → ℕ -->

Applied to 4 with its proof, it computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[s, Subtype[Function[{Typed[n, Naturals]}, 2 <= n]]]}, s[[1]] - 2][SubtypeIntroduction[4, LessEqualStep[LessEqualStep[LessEqualReflexivity]]]]]]
```

<!-- => 2 -->

## Properties and Relations

[Subtype]() is a type, where [Exists]() of the same property is a proposition:

```wl
TypeOf[TypeTheoryTerm[Subtype[Function[{Typed[n, Naturals]}, 2 <= n]]]]
```

<!-- => Type -->

The existential statement:

```wl
TypeOf[TypeTheoryTerm[Exists[Function[{Typed[n, Naturals]}, 2 <= n]]]]
```

<!-- => Prop -->

## Possible Issues

Without the expected type, the property is unknown, since the proof alone does not say which property of 4 it proves:

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtypeIntroduction[4, LessEqualStep[LessEqualStep[LessEqualReflexivity]]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
