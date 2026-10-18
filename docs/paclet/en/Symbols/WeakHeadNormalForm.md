---
Template: Symbol
Name: WeakHeadNormalForm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/WeakHeadNormalForm
Keywords: [reduction, normal form, computation, beta, unfolding, recursor]
SeeAlso: [DefinitionallyEqualQ, TypeTheoryCheck, TypeTheoryTerm, TypeTheoryDefinition]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[WeakHeadNormalForm]()[*term*]</code> reduces the [TypeTheoryTerm]() *term* until its head can no longer reduce.

## Details & Options

- Reduction applies functions to their arguments, unfolds definitions and local definitions, applies a recursor to a constructor, takes a field of a constructed structure, and adds natural number literals. Theorems never unfold.
- Only the head is reduced: the arguments of a constructor stay as they are.

## Basic Examples

Addition of literals:

```wl
WeakHeadNormalForm[TypeTheoryTerm[2 + 3]]
```

<!-- => 5 -->

---

A function applied to an argument:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, x + 1][41]]]
```

<!-- => 42 -->

## Scope

A definition unfolds:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Not[1 == 2]]]
```

<!-- => 1 == 2 ⇒ False -->

---

A recursor applied to a constructor:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[And][
    Function[{Typed[t, And[True, True]]}, NonNegativeIntegers],
    Function[{Typed[p, True], Typed[q, True]}, 7],
    AndIntroduction[TrueIntroduction, TrueIntroduction]
]]]
```

<!-- => 7 -->
