---
Template: Symbol
Name: GlueType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/GlueType
Keywords: [Glue type, univalence, equivalence, path of types, cubical type theory, system, face, equivalenceToPath]
SeeAlso: [GlueIntroduction, GlueElimination, CubicalTransport, Equivalence, DependentSum, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[GlueType]()[*A*, {*face* -> *pair*, ...}]</code> is the type *A* glued, where each face holds, to the type *T* of the pair, an element {*T*, *e*} of the dependent sum with *e* an equivalence from *T* to *A*; where a face holds it is *T*.

## Details & Options

- A pair may be written as `{T, e}`, or with the constructor of the dependent sum, as <code>"dependentPair"[*T*, *e*]</code>.
- An equivalence is a function with contractible fibers, the type the kernel writes with the dependent sum and paths; <code>[Equivalence]()[*T*, *A*]</code> is that type in the cubical environment. A function that is not an equivalence is refused.
- Where a face holds, the Glue type is its glued type; where none holds, it is a type of its own over *A*. Any two pairs must agree where both their faces hold. A Glue type is in the universe of *A*.
- Univalence, `"equivalenceToPath"`, is a line of Glue types over *B*: *A* glued along *e* where `i == 0`, and *B* along the identity where `i == 1`. It turns an equivalence into a path of types, and transport along it, [CubicalTransport](), applies the equivalence.
- [GlueIntroduction]() builds an element of a Glue type over an element of *A*, and [GlueElimination]() takes it to *A*.
- [GlueType]() must be given both arguments.

## Basic Examples

Where its face holds, a Glue type is its glued type:

```wl
WeakHeadNormalForm[TypeTheoryTerm[GlueType[Booleans, {1 -> {Booleans, "negationEquivalence"}}], "Cubical"]]
```

<!-- => 𝔹 -->

---

Univalence glues along the equivalence at 0 and along the identity at 1:

```wl
TypeTheoryEnvironment["Cubical"]["equivalenceToPath"]
```

<!-- => definition equivalenceToPath : ∀_{A ∶ Type u} ∀_{B ∶ Type u} Equivalence[A, B] → A ≡ B := {A ∶ Type u} {B ∶ Type u} (e ∶ Equivalence[A, B]) (i ∶ Interval) ↦ GlueType[B, {i == 0 → 〈A, e〉, i == 1 → 〈B, identityEquivalence[B]〉}] -->

---

So an equivalence gives a path of types, here negation a path from the Booleans to the Booleans:

```wl
TypeTheoryType["equivalenceToPath"["negationEquivalence"], "Cubical"]
```

<!-- => 𝔹 ≡ 𝔹 -->

---

Transport along that path applies negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["negationEquivalence"], 0, "true"], "Cubical"]]
```

<!-- => false -->

## Scope

A pair may be written with the constructor of the dependent sum:

```wl
WeakHeadNormalForm[TypeTheoryTerm[GlueType[Booleans, {1 -> "dependentPair"[Booleans, "negationEquivalence"]}], "Cubical"]]
```

<!-- => 𝔹 -->

---

A line of Glue types written out, the Booleans glued along negation where `i == 0` and along the identity where `i == 1`, is a path of types:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueType[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}, i == 1 -> {Booleans, "identityEquivalence"[Booleans]}}], "Cubical"]
```

<!-- => 𝔹 ≡ 𝔹 -->

---

With the one face `i == 0`, the line ends in a Glue type glued nowhere, a type of its own:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueType[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}}], "Cubical"]
```

<!-- => 𝔹 ≡ GlueType[𝔹, {False → 〈𝔹, negationEquivalence〉}] -->

---

A Glue type is in the universe of its base:

```wl
TypeTheoryType[GlueType[Booleans, {1 -> {Booleans, "negationEquivalence"}}], "Cubical"]
```

<!-- => Type -->

## Properties and Relations

The equivalence of a pair is an element of [Equivalence]():

```wl
TypeTheoryType["negationEquivalence", "Cubical"]
```

<!-- => Equivalence[𝔹, 𝔹] -->

---

Along the path that the identity equivalence gives, transport is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["identityEquivalence"[Booleans]], 0, "true"], "Cubical"]]
```

<!-- => true -->

---

[GlueElimination]() takes the line of Glue types to its base: along univalence it is a path of functions from negation, the equivalence at 0, to the identity at 1:

```wl
TypeTheoryType[
    Typed[i, Interval] |-> Function[{Typed[b, GlueType[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}, i == 1 -> {Booleans, "identityEquivalence"[Booleans]}}]]}, GlueElimination[b]],
    "Cubical"
]
```

<!-- => Path[(i ∶ Interval) ↦ (GlueType[𝔹, {i == 0 → 〈𝔹, negationEquivalence〉, i == 1 → 〈𝔹, identityEquivalence[𝔹]〉}] → 𝔹), not, (b ∶ 𝔹) ↦ b] -->

## Possible Issues

A function is not an equivalence: `"not"` has to be made one, as `"negationEquivalence"` is:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueType[Booleans, {i == 0 -> {Booleans, "not"}}], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

Two pairs must agree where both their faces hold:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueType[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}, i == 0 -> {Booleans, "identityEquivalence"[Booleans]}}], "Cubical"]
```

<!-- => Failure["SystemDisagreement", ...] -->

---

The system is a list of rules, *face* -> *pair*, not a pair alone:

```wl
TypeTheoryType[GlueType[Booleans, {Booleans, "negationEquivalence"}], "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

[GlueType]() must be given both arguments:

```wl
TypeTheoryType[GlueType[Booleans], "Cubical"]
```

<!-- => Failure["CubicalUnsaturated", ...] -->
