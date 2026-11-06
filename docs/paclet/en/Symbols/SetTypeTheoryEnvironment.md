---
Template: Symbol
Name: SetTypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SetTypeTheoryEnvironment
Keywords: [default environment, environment, prelude, session, Block, declarations, terms, proofs, library environment, integers]
SeeAlso: [$TypeTheoryEnvironment, TypeTheoryEnvironment, TypeTheoryTerm, TypeTheoryProof, TypeTheoryRules]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction]
---

## Usage

<code>[SetTypeTheoryEnvironment]()[*env*]</code> makes the environment *env* the default environment, of the terms, proofs and declarations that name none, and gives it.

<code>[SetTypeTheoryEnvironment]()["*name*"]</code> makes the library environment called *name* the default, and <code>[SetTypeTheoryEnvironment]()["Prelude"]</code> makes the prelude the default again.

<code>[SetTypeTheoryEnvironment]()[{*declaration1*, *declaration2*, ...}]</code> extends the default environment with the declarations and makes the result the default.

<code>[SetTypeTheoryEnvironment]()[*rules*]</code> makes the environment with no constants that follows the [TypeTheoryRules]() *rules* the default.

## Details & Options

- The default environment is [$TypeTheoryEnvironment](), the prelude when the paclet loads. A [TypeTheoryTerm]() or a [TypeTheoryProof]() that names no environment is in it, and [TypeTheoryEnvironment]() extends it with the declarations given without an environment.
- <code>[SetTypeTheoryEnvironment]()[*spec*]</code> makes <code>[TypeTheoryEnvironment]()[*spec*]</code> the default, so a name such as `"Integers"` or `"HomotopyTypeTheory"`, a list of declarations and a [TypeTheoryRules]() each set the environment they give.
- Where <code>[TypeTheoryEnvironment]()[*spec*]</code> is a [Failure](), as for a misspelled name or a declaration that does not check, [SetTypeTheoryEnvironment]() gives the [Failure]() and leaves the default as it was. Anything that specifies no environment gives a [Failure]() tagged `"NotAnEnvironment"`.
- An environment is a value, and declarations never change the default by themselves: it changes only when it is set.
- The default belongs to the kernel, so it holds for every later evaluation of the session. Code that sets it for one computation sets it back with <code>[SetTypeTheoryEnvironment]()["Prelude"]</code>, or uses <code>[Block]()[{[$TypeTheoryEnvironment]() = *env*}, *expr*]</code>, which makes *env* the default while *expr* evaluates and leaves the default as it was.
- A term or proof that names its environment, <code>[TypeTheoryTerm]()[*expr*, *env*]</code> or <code>[TypeTheoryProof]()[*statement*, *env*, {...}]</code>, is in *env* whatever the default is.

## Basic Examples

Make the integers the default environment:

```wl
SetTypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 332 constants -->

A proof about integers now names no environment:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y)^2 == x^2 - 2 x y + y^2], {"Introduce"[x, y], "Ring"}]
```

<!-- => Proof complete -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

---

Make the prelude with a definition added the default:

```wl
SetTypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Typed[n, Naturals] |-> n + n]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Terms use the definition without naming the environment:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Doubled[21]]]
```

<!-- => 42 -->

And so do proofs:

```wl
TypeTheoryProof[Doubled[2] == 4, {"Reflexivity"}]
```

<!-- => Proof complete -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

## Scope

Make homotopy type theory the default:

```wl
SetTypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Its constants need no environment named, here the loop of the circle, a path from its base point to itself:

```wl
TypeTheoryType["circleLoop"]
```

<!-- => circleBase == circleBase -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

---

Declarations extend the default that is set. Make the integers the default:

```wl
SetTypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 332 constants -->

Then add a definition to them and make the result the default:

```wl
SetTypeTheoryEnvironment[{TypeTheoryDefinition[IntegerSquare, Typed[x, Integers] |-> x x]}]
```

<!-- => TypeTheoryEnvironment summary box: 333 constants -->

The definition is a function on the integers:

```wl
TypeTheoryType[IntegerSquare]
```

<!-- => ℤ → ℤ -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

---

Make the empty environment of Martin-Löf type theory the default:

```wl
SetTypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory"]]
```

<!-- => TypeTheoryEnvironment summary box: 0 constants -->

Declarations without an environment extend it, under its rules:

```wl
TypeTheoryEnvironment[{TypeTheoryInductiveType[Unit, TypeUniverse[1], {UnitIntroduction -> Unit}]}]
```

<!-- => TypeTheoryEnvironment summary box: 3 constants -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

---

[Block]() makes an environment the default for one computation. In the constructive environment, the prelude without its axioms, the excluded middle is not declared:

```wl
Block[{$TypeTheoryEnvironment = "Constructive"}, TypeTheoryType["excludedMiddle"]]
```

<!-- => Failure["ElaborationFailed", ...] -->

Outside the [Block](), the default is the prelude, where it is a theorem:

```wl
TypeTheoryType["excludedMiddle"]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

## Properties and Relations

[SetTypeTheoryEnvironment]() sets [$TypeTheoryEnvironment](). Make the integers the default:

```wl
SetTypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 332 constants -->

[$TypeTheoryEnvironment]() is now the integers:

```wl
$TypeTheoryEnvironment === TypeTheoryEnvironment["Integers"]
```

<!-- => True -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

---

[TypeTheoryEnvironment]() extends the default without changing it:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom[Mystery, Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The default has no `Mystery`:

```wl
KeyExistsQ[$TypeTheoryEnvironment, Mystery]
```

<!-- => False -->

---

Make the constructive environment the default:

```wl
SetTypeTheoryEnvironment["Constructive"]
```

<!-- => TypeTheoryEnvironment summary box: 155 constants -->

A term that names its environment is in it whatever the default is:

```wl
TypeTheoryType["excludedMiddle", "Prelude"]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

## Possible Issues

A term written without an environment is in the default environment when it is used, not when it was written. Make the prelude with a definition the default:

```wl
SetTypeTheoryEnvironment[{TypeTheoryDefinition[Tripled, Typed[n, Naturals] |-> n + n + n]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

A term written while it is the default:

```wl
term = TypeTheoryTerm[Tripled[2]]
```

<!-- => Tripled[2] -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

The term no longer has the definition:

```wl
TypeTheoryType[term]
```

<!-- => Failure["ElaborationFailed", ...] -->

To keep a term in its environment, give it the environment: <code>[TypeTheoryTerm]()[*expr*, *env*]</code>.

---

A misspelled name gives a [Failure]():

```wl
SetTypeTheoryEnvironment["Integer"]
```

<!-- => Failure["UnknownEnvironment", ...] -->

The default stays the prelude:

```wl
$TypeTheoryEnvironment
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

---

Declarations that do not check leave the default as it was:

```wl
SetTypeTheoryEnvironment[{TypeTheoryTheorem[Wrong, 2 + 2 == 5, "equalityReflexivity"[4]]}]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A value that specifies no environment gives a [Failure]():

```wl
SetTypeTheoryEnvironment[5]
```

<!-- => Failure["NotAnEnvironment", ...] -->
