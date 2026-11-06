---
Template: Symbol
Name: GlueElimination
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/GlueElimination
Keywords: [Glue type, unglue, cubical type theory, univalence, equivalence, base of a Glue type]
SeeAlso: [GlueType, GlueIntroduction, CubicalTransport, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[GlueElimination]()[*b*]</code> is the element of the base under *b*, an element of a Glue type.

<code>[GlueElimination]()[*A*, *system*, *b*]</code> gives the Glue type <code>[GlueType]()[*A*, *system*]</code> in full.

## Details & Options

- Where a face of the Glue type holds, [GlueElimination]() is the equivalence there applied to *b*, the first one whose face holds; of <code>[GlueIntroduction]()[*terms*, *a*]</code> it is *a*.
- The short form takes the Glue type from the type of *b*, which must be a Glue type as it stands: where a face holds, the Glue type is its glued type already, and the form in full is needed.
- Along a line of Glue types, such as the path that `"equivalenceToPath"` makes from an equivalence *e*, [GlueElimination]() is a path of functions from *e* to the identity.
- Transport in a Glue type starts from the element under the element transported, which it carries along the base.

## Basic Examples

Where the face holds, the element under `"true"` is the equivalence applied, negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[GlueElimination[Booleans, {1 -> {Booleans, "negationEquivalence"}}, "true"], "Cubical"]]
```

<!-- => false -->

---

Under an element built over `"false"`, the element of the base is `"false"`:

```wl
NormalForm[TypeTheoryTerm[Typed[i, Interval] |-> GlueElimination[GlueIntroduction[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}}, {i == 0 -> "true"}, "false"]], "Cubical"]]
```

<!-- => (i ∶ Interval) ↦ false -->

---

Along the line of Glue types of univalence, the Booleans glued along negation where `i == 0` and along the identity where `i == 1`, [GlueElimination]() is a path of functions from negation to the identity:

```wl
TypeTheoryType[
    Typed[i, Interval] |-> Function[{Typed[b, GlueType[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}, i == 1 -> {Booleans, "identityEquivalence"[Booleans]}}]]}, GlueElimination[b]],
    "Cubical"
]
```

<!-- => Path[(i ∶ Interval) ↦ (GlueType[𝔹, {i == 0 → 〈𝔹, negationEquivalence〉, i == 1 → 〈𝔹, identityEquivalence[𝔹]〉}] → 𝔹), not, (b ∶ 𝔹) ↦ b] -->

## Scope

A path over a line of Glue types, from `"true"` to the element over `"false"`, goes under it to a path in the Booleans from the negation of `"true"` to `"false"`:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueElimination[GlueIntroduction[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}}, {i == 0 -> "true"}, "false"]], "Cubical"]
```

<!-- => !true ≡ false -->

---

With several faces, the equivalence is the one whose face holds, here the identity over 1, not negation over 0:

```wl
WeakHeadNormalForm[TypeTheoryTerm[GlueElimination[Booleans, {0 -> {Booleans, "negationEquivalence"}, 1 -> {Booleans, "identityEquivalence"[Booleans]}}, "true"], "Cubical"]]
```

<!-- => true -->

## Possible Issues

Away from its faces a Glue type is not its base, so `"true"` is not an element of it:

```wl
TypeTheoryType[Typed[i, Interval] |-> GlueElimination[Booleans, {i == 0 -> {Booleans, "negationEquivalence"}}, "true"], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The short form needs an element of a Glue type:

```wl
TypeTheoryType[GlueElimination["true"], "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

Where its face holds, the Glue type of `b` is its glued type already, so the short form finds no Glue type; give it in full:

```wl
TypeTheoryType[Typed[b, GlueType[Booleans, {1 -> {Booleans, "negationEquivalence"}}]] |-> GlueElimination[b], "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->
