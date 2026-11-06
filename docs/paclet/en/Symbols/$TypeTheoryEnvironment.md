---
Template: Symbol
Name: $TypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/$TypeTheoryEnvironment
Keywords: [default environment, environment, prelude, Block, session, library environment]
SeeAlso: [SetTypeTheoryEnvironment, TypeTheoryEnvironment, TypeTheoryTerm, TypeTheoryProof]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction]
---

## Usage

<code>[$TypeTheoryEnvironment]()</code> is the default environment, of the terms, proofs and declarations that name none.

## Details & Options

- [$TypeTheoryEnvironment]() is the prelude when the paclet loads. [SetTypeTheoryEnvironment]() sets another, and <code>[SetTypeTheoryEnvironment]()["Prelude"]</code> sets the prelude back.
- A [TypeTheoryTerm]() or a [TypeTheoryProof]() that names no environment is in [$TypeTheoryEnvironment]() when it is used, and <code>[TypeTheoryEnvironment]()[{*declaration1*, ...}]</code> extends it.
- <code>[Block]()[{[$TypeTheoryEnvironment]() = *env*}, *expr*]</code> makes the environment *env* the default while *expr* evaluates. *env* may be the name of a library environment, such as `"Integers"`, which stands for that environment; any other value that is no environment leaves the prelude.
- <code>[TypeTheoryEnvironment]()[]</code>, the empty environment, does not depend on the default.

## Basic Examples

The default environment is the prelude:

```wl
$TypeTheoryEnvironment
```

<!-- => TypeTheoryEnvironment summary box: 250 constants -->

---

Make the integers the default for one computation, by their name, so a proof about integers names no environment:

```wl
Block[{$TypeTheoryEnvironment = "Integers"},
    TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y)^2 == x^2 - 2 x y + y^2], {"Introduce"[x, y], "Ring"}]
]
```

<!-- => Proof complete -->

---

Declarations without an environment extend the default, here the constructive environment:

```wl
Block[{$TypeTheoryEnvironment = "Constructive"}, TypeTheoryEnvironment[{TypeTheoryAxiom[Unprovable, False]}]]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->

## Scope

An environment with a definition as the default, so terms use the definition without naming the environment:

```wl
Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Typed[n, Naturals] |-> n + n]}]},
    WeakHeadNormalForm[TypeTheoryTerm[Doubled[21]]]
]
```

<!-- => 42 -->

---

Homotopy type theory as the default, where univalence is an axiom:

```wl
Block[{$TypeTheoryEnvironment = "HomotopyTypeTheory"}, TypeTheoryType["univalence"]]
```

<!-- => ∀_A∶Type u ∀_B∶Type u IsEquivalence[(p ∶ A == B) ↦ equalityToEquivalence[p]] -->

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
KeyExistsQ[$TypeTheoryEnvironment, "excludedMiddle"]
```

<!-- => False -->

Make the prelude the default again:

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 250 constants -->

## Properties and Relations

A proof that names no environment is in the default environment:

```wl
Block[{$TypeTheoryEnvironment = "Integers"}, TypeTheoryProof[2 + 2 == 4]["Environment"] === TypeTheoryEnvironment["Integers"]]
```

<!-- => True -->

---

A term that names its environment is in it whatever the default is:

```wl
Block[{$TypeTheoryEnvironment = "Constructive"}, TypeTheoryType["excludedMiddle", "Prelude"]]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

---

The empty environment does not depend on the default:

```wl
Block[{$TypeTheoryEnvironment = "Integers"}, Length[TypeTheoryEnvironment[]]]
```

<!-- => 0 -->

## Possible Issues

A term written without an environment is in the default where it is used. A term written in a [Block]() of the integers:

```wl
negation = Block[{$TypeTheoryEnvironment = "Integers"}, TypeTheoryTerm[Typed[x, Integers] |-> -x]]
```

<!-- => (x ∶ ℤ) ↦ -x -->

Outside the [Block](), it is in the prelude, which has no integers:

```wl
TypeTheoryType[negation]
```

<!-- => Failure["ElaborationFailed", ...] -->

Given its environment, it keeps it:

```wl
TypeTheoryType[TypeTheoryTerm[Typed[x, Integers] |-> -x, "Integers"]]
```

<!-- => ℤ → ℤ -->

---

A name of a library environment stands for that environment; any other value that is no environment leaves the prelude, where the excluded middle is a theorem:

```wl
Block[{$TypeTheoryEnvironment = "Classical"}, TypeTheoryType["excludedMiddle"]]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->
