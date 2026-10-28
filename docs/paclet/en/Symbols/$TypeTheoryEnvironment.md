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

## Scope

[Block]() makes an environment with a definition the default for one computation, so terms use the definition without naming the environment:

```wl
Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Function[{Typed[n, Naturals]}, n + n]]}]}, WeakHeadNormalForm[TypeTheoryTerm[Doubled[21]]]]
```

<!-- => 42 -->

---

[SetTypeTheoryEnvironment]() sets it for the session, here to the constructive environment:

```wl
SetTypeTheoryEnvironment["Constructive"]
```

<!-- => TypeTheoryEnvironment summary box: 155 constants -->

The default environment is now the constructive one:

```wl
$TypeTheoryEnvironment
```

<!-- => TypeTheoryEnvironment summary box: 155 constants -->

It has no excluded middle:

```wl
KeyExistsQ[$TypeTheoryEnvironment, ExcludedMiddle]
```

<!-- => False -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 169 constants -->

## Properties and Relations

A proof that names no environment is in the default environment:

```wl
TypeTheoryProof[2 + 2 == 4]["Environment"] === $TypeTheoryEnvironment
```

<!-- => True -->

## Possible Issues

A name of a library environment, such as `"Constructive"`, stands for that environment, as in [SetTypeTheoryEnvironment](); any other value that is no environment leaves the prelude, where the excluded middle is declared:

```wl
Block[{$TypeTheoryEnvironment = "Classical"}, TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle]]]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

<code>[TypeTheoryEnvironment]()["Constructive"]</code>, or its name, makes the constructive environment the default, which has no excluded middle:

```wl
Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment["Constructive"]}, TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
