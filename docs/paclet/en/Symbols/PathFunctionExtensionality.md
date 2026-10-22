---
Template: Symbol
Name: PathFunctionExtensionality
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PathFunctionExtensionality
Keywords: [function extensionality, path, cubical type theory]
SeeAlso: [PathCongruence, FunctionExtensionality]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[PathFunctionExtensionality]()[*h*]</code> is the path from *f* to *g* that a path *h*[*x*] from *f*[*x*] to *g*[*x*] for every *x* gives: the function of *i* that is the function of *x* that is *h*[*x*][*i*].

## Details & Options

- In cubical type theory function extensionality is a term, where the prelude has [FunctionExtensionality]() as a theorem proved from the soundness of quotients.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[PathFunctionExtensionality, cubical]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_{f ∶ A → B} ∀_{g ∶ A → B} (∀_x∶A f[x] ≡ g[x]) → f ≡ g -->

---

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

At 0 it is the first function, by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[PathFunctionExtensionality[Function[{Typed[b, Booleans]}, NegationInvolution[b]]][0], cubical],
    TypeTheoryTerm[Function[{Typed[b, Booleans]}, "not"["not"[b]]], cubical]
]
```

<!-- => True -->
