---
Template: Symbol
Name: $TypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/$TypeTheoryEnvironment
Keywords: [default environment, environment, prelude, Block, session]
SeeAlso: [SetTypeTheoryEnvironment, TypeTheoryEnvironment, TypeTheoryTerm, TypeTheoryProof]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[$TypeTheoryEnvironment]()</code> is the default environment, of the terms, proofs and declarations that name none.

## Details & Options

- [$TypeTheoryEnvironment]() is the prelude when the paclet loads. [SetTypeTheoryEnvironment]() sets another, and <code>[SetTypeTheoryEnvironment]()["Prelude"]</code> sets the prelude back.
- A [TypeTheoryTerm]() or a [TypeTheoryProof]() that names no environment is in [$TypeTheoryEnvironment](), and <code>[TypeTheoryEnvironment]()[{*declaration1*, ...}]</code> extends it.
- <code>[Block]()[{[$TypeTheoryEnvironment]() = *env*}, *expr*]</code> makes the environment *env* the default while *expr* evaluates.

## Basic Examples

The default environment is the prelude:

```wl
$TypeTheoryEnvironment
```

<!-- => TypeTheoryEnvironment summary box: 169 constants -->

Declarations without an environment extend the default, here the constructive environment for one computation:

```wl
Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment["Constructive"]}, TypeTheoryEnvironment[{TypeTheoryAxiom[Unprovable, False]}]]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->
