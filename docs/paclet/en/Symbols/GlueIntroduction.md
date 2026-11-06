---
Template: Symbol
Name: GlueIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/GlueIntroduction
Keywords: [Glue type, glue, cubical type theory, system, univalence, path over univalence, element of a Glue type]
SeeAlso: [GlueType, GlueElimination, CubicalTransport, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[GlueIntroduction]()[{*face* -> *t*, ...}, *a*]</code> is the element of the Glue type expected that is *t* where a face holds, over *a*, an element of the base that the equivalence takes *t* to.

<code>[GlueIntroduction]()[*A*, *system*, {*face* -> *t*, ...}, *a*]</code> gives the Glue type <code>[GlueType]()[*A*, *system*]</code> in full.

## Details & Options

- The terms go with the faces of the Glue type, in order, one for each. Each must be an element of its glued type where its face holds, and the equivalence there must take it to *a*; the kernel fails with `"GlueMismatch"` otherwise.
- Where a face holds, the element is its term. [GlueElimination]() of it is *a*.
- The short form takes its Glue type from the type expected, such as a path type over the path of `"equivalenceToPath"`. Where a face of the Glue type holds, the Glue type is already its glued type, and the short form finds none: give it in full.
- Along univalence, the function of `i` that is *x* where `i == 0` and *e*[*x*] where `i == 1`, over *e*[*x*], is a path over the path of types from *x* to *e*[*x*].

## Basic Examples

A path over univalence: the function of `i` that is `"true"` where `i == 0` and `"false"` where `i == 1`, over `"false"`, which negation takes `"true"` to, goes from `"true"` to `"false"` along the line of Glue types:

```wl
TypeTheoryType[
    Typed[i, Interval] |-> GlueIntroduction[
        Booleans, {i == 0 -> {Booleans, "negationEquivalence"}, i == 1 -> {Booleans, "identityEquivalence"[Booleans]}},
        {i == 0 -> "true", i == 1 -> "false"},
        "false"
    ],
    "Cubical"
]
```

<!-- => Path[(i ∶ Interval) ↦ GlueType[𝔹, {i == 0 → 〈𝔹, negationEquivalence〉, i == 1 → 〈𝔹, identityEquivalence[𝔹]〉}], true, false] -->

---

Where its face holds, the element is its term:

```wl
WeakHeadNormalForm[TypeTheoryTerm[GlueIntroduction[Booleans, {1 -> {Booleans, "negationEquivalence"}}, {1 -> "true"}, "false"], "Cubical"]]
```

<!-- => true -->

---

The short form takes its Glue type from the type expected, here the paths over the path of types that univalence makes from negation:

```wl
TypeTheoryType[
    Typed[i |-> GlueIntroduction[{i == 0 -> "true", i == 1 -> "false"}, "false"], Path["equivalenceToPath"["negationEquivalence"], "true", "false"]],
    "Cubical"
]
```

<!-- => Path[(i ∶ Interval) ↦ equivalenceToPath[𝔹, 𝔹, negationEquivalence, i], true, false] -->

## Scope

With the one face `i == 0`, the element at the end of the line lies in a Glue type glued nowhere, over `"false"`:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueIntroduction[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}}, {i == 0 -> "true"}, "false"], "Cubical"]
```

<!-- => Path[(i ∶ Interval) ↦ GlueType[𝔹, {i == 0 → 〈𝔹, negationEquivalence〉}], true, GlueIntroduction[{False → true}, false]] -->

## Properties and Relations

[GlueElimination]() of the element is the element of the base it lies over:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> GlueElimination[GlueIntroduction[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}}, {i == 0 -> "true"}, "false"]], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ false -->

## Possible Issues

The equivalence must take each term to the element of the base: negation takes `"true"` to `"false"`, not to `"true"`:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueIntroduction[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}}, {i == 0 -> "true"}, "true"], "Cubical"]
```

<!-- => Failure["GlueMismatch", ...] -->

---

The terms go with the faces of the Glue type in order: written in the other order, each is checked against the other face:

```wl
TypeTheoryType[
    Typed[i, Interval] |-> GlueIntroduction[
        Booleans, {i == 0 -> {Booleans, "negationEquivalence"}, i == 1 -> {Booleans, "identityEquivalence"[Booleans]}},
        {i == 1 -> "false", i == 0 -> "true"},
        "false"
    ],
    "Cubical"
]
```

<!-- => Failure["GlueMismatch", ...] -->

---

There is a term for each face of the Glue type:

```wl
TypeTheoryType[
    Typed[i, Interval] |-> GlueIntroduction[
        Booleans, {i == 0 -> {Booleans, "negationEquivalence"}, i == 1 -> {Booleans, "identityEquivalence"[Booleans]}},
        {i == 0 -> "true"},
        "false"
    ],
    "Cubical"
]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

Where its face holds, a Glue type is already its glued type, so the short form finds no Glue type to build an element of:

```wl
TypeTheoryType[Typed[GlueIntroduction[{1 -> "true"}, "false"], GlueType[Booleans, {1 -> {Booleans, "negationEquivalence"}}]], "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->
