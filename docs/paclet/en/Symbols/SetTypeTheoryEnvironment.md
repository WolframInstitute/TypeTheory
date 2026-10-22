---
Template: Symbol
Name: SetTypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SetTypeTheoryEnvironment
Keywords: [default environment, environment, prelude, session, Block, declarations, terms, proofs]
SeeAlso: [$TypeTheoryEnvironment, TypeTheoryEnvironment, TypeTheoryTerm, TypeTheoryProof]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[SetTypeTheoryEnvironment]()[*env*]</code> makes the environment *env* the default environment, of the terms, proofs and declarations that name none, and gives it.

<code>[SetTypeTheoryEnvironment]()["Prelude"]</code> makes the prelude the default again.

<code>[SetTypeTheoryEnvironment]()[{*declaration1*, *declaration2*, ...}]</code> extends the default environment with the declarations and makes the result the default.

## Details & Options

- The default environment is [$TypeTheoryEnvironment](), the prelude when the paclet loads. A [TypeTheoryTerm]() or a [TypeTheoryProof]() that names no environment is in it, and [TypeTheoryEnvironment]() extends it with the declarations given without an environment.
- <code>[SetTypeTheoryEnvironment]()[*spec*]</code> makes <code>[TypeTheoryEnvironment]()[*spec*]</code> the default, so `"Constructive"`, `"HomotopyTypeTheory"` and a [TypeTheoryRules]() set those environments.
- An environment is a value, and declarations never change the default by themselves: it changes only when it is set.
- <code>[Block]()[{[$TypeTheoryEnvironment]() = *env*}, *expr*]</code> makes *env* the default while *expr* evaluates, and leaves the default as it was.
- A term that carries its environment, <code>[TypeTheoryTerm]()[*expr*, *env*]</code>, is in *env* whatever the default is.

## Basic Examples

Make the prelude with a definition added the default:

```wl
SetTypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Function[{Typed[n, Naturals]}, n + n]]}]
```

<!-- => TypeTheoryEnvironment summary box: 150 constants -->

Terms use it without naming it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Doubled[21]]]
```

<!-- => 42 -->

And so do proofs:

```wl
TypeTheoryProof[Doubled[2] == 4, {TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Proof complete -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 149 constants -->

## Scope

[Block]() makes an environment the default for one computation. In the constructive environment, the prelude without its axioms, the excluded middle is not declared:

```wl
Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment["Constructive"]}, TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle]]]
```

<!-- => Failure["ElaborationFailed", ...] -->

Outside the [Block](), the default is the prelude, where it is a theorem:

```wl
TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle]]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

## Possible Issues

A term written without an environment is in the default environment when it is used, not when it was written. Make the prelude with a definition the default:

```wl
SetTypeTheoryEnvironment[{TypeTheoryDefinition[Tripled, Function[{Typed[n, Naturals]}, n + n + n]]}]
```

<!-- => TypeTheoryEnvironment summary box: 150 constants -->

A term written while it is the default:

```wl
term = TypeTheoryTerm[Tripled[2]]
```

<!-- => Tripled[2] -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 149 constants -->

The term no longer has the definition:

```wl
TypeTheoryCheck[term]
```

<!-- => Failure["ElaborationFailed", ...] -->

To keep a term in its environment, give it the environment: <code>[TypeTheoryTerm]()[*expr*, *env*]</code>.
