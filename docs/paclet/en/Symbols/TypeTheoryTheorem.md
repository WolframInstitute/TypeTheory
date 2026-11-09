---
Template: Symbol
Name: TypeTheoryTheorem
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTheorem
Keywords: [theorem, proof, declaration, proposition, kernel, environment, induction, tactics, hole, sorry, annotation, citation, universe parameter]
SeeAlso: [TypeTheoryProof, TypeTheoryEnvironment, TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryCheck, TypeTheoryHole, TypeTheoryAxiomClosure]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction]
---

## Usage

<code>[TypeTheoryTheorem]()[*name*, *statement*, *proof*]</code> declares *name* as a theorem: *proof* must prove *statement* when the declaration is added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryTheorem]()[*name*, *proof*]</code> declares the statement of the finished [TypeTheoryProof]() *proof*.

## Details & Options

- *statement* must be a proposition, a type in <code>[TypeUniverse]()[0]</code>; under rules without Prop, as in the HoTT environment, it may be any type. *proof* is a term, a [TypeTheoryTerm](), or a finished [TypeTheoryProof]() written out or held in a symbol.
- The kernel checks *proof* against *statement* when the theorem is added; a proof that does not check gives a [Failure](). Nothing a tactic did is trusted: the kernel checks the term a [TypeTheoryProof]() built.
- A theorem never unfolds: what it states is all that is used of it. A theorem applies like a function to the variables its statement quantifies over.
- A proof may leave parts to give with [TypeTheoryHole](), or with the tactic `"Hole"`: the environment then holds a constant <code>[TypeTheoryHole]()[*name*, *k*]</code> for each hole, before the theorem, and <code>[Information]()[[TypeTheoryTerm]()[*name*, *env*], "Holes"]</code> lists them. A proof with goals still open is no proof and gives a [Failure]().
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear, and makes each level that nothing in the declaration decides one more, `"u_1"`, `"u_2"`, ….
- The option `"Annotation" -> *data*` keeps *data*, a citation, the statement in words or anything else, in the theorem's record as it is given: <code>[Information]()[[TypeTheoryTerm]()[*name*, *env*], "Annotation"]</code> gives it back, and [Normal]() and a saved environment keep it.

## Basic Examples

A theorem proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its declaration:

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

---

A proof by induction that 0 is a left identity of addition, by tactics:

```wl
proof = TypeTheoryProof[ForAll[{n}, 0 + n == n], {
    "Introduce"[n],
    "Induction"[n],
    "Reflexivity",
    "Introduce"[k, ih],
    "Exact"["equalityCongruence"["successor", ih]]
}]
```

<!-- => Proof complete -->

The theorem it proves, which the kernel checks again:

```wl
proved = TypeTheoryEnvironment[TypeTheoryTheorem[ZeroLeftIdentity, proof]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its statement is what the proof proved:

```wl
proved[ZeroLeftIdentity]
```

<!-- => theorem ZeroLeftIdentity : ∀_n∶ℕ 0 + n == n -->

## Scope

A theorem with a proof term, a function from a proof of `p` to a proof of `p`, whose variables take their types from the statement:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfImplication, ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], {p, h} |-> h]}][SelfImplication]
```

<!-- => theorem SelfImplication : ∀_p∶Prop p ⇒ p -->

---

A proof written out in the theorem, here that conjunction commutes:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[AndCommutes, TypeTheoryProof[
    ForAll[{p, q}, Implies[p && q, q && p]],
    {"Introduce"[p, q, h], "Cases"[h], "Introduce"[a, b], "Constructor", "Exact"[b], "Exact"[a]}
]]}][AndCommutes]
```

<!-- => theorem AndCommutes : ∀_p∶Prop ∀_q∶Prop (p ∧ q) ⇒ (q ∧ p) -->

---

A theorem about the integers, declared by the name of their environment:

```wl
squares = TypeTheoryEnvironment["Integers", {TypeTheoryTheorem[SquareOfSum, TypeTheoryProof[
    ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + y)^2 == x^2 + 2 x y + y^2],
    "Integers",
    {"Introduce"[x, y], "Ring"}
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 357 constants -->

The theorem it declares:

```wl
squares[SquareOfSum]
```

<!-- => theorem SquareOfSum : ∀_x∶ℤ ∀_y∶ℤ (x + y)^2 == x^2 + 2 x y + y^2 -->

---

A theorem applies like a function, to the variables its statement quantifies over:

```wl
proved = TypeTheoryEnvironment[TypeTheoryTheorem[ZeroLeftIdentity, TypeTheoryProof[ForAll[{n}, 0 + n == n], {
    "Introduce"[n], "Induction"[n], "Reflexivity", "Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]
}]]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Applied to 7, it states `0 + 7 == 7`:

```wl
TypeTheoryType[ZeroLeftIdentity[7], proved]
```

<!-- => 0 + 7 == 7 -->

Later proofs use it, here to rewrite `0 + m`:

```wl
TypeTheoryProof[ForAll[{m, n}, (0 + m) + n == m + n], proved, {"Introduce"[m, n], "Rewrite"[ZeroLeftIdentity]}]
```

<!-- => Proof complete -->

---

A variable written without a type, whose sort nothing else decides, is a proposition in a statement that can be one:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfImplication, ForAll[{p}, Implies[p, p]], {p, h} |-> h]}][SelfImplication]
```

<!-- => theorem SelfImplication : ∀_p∶Prop p ⇒ p -->

---

A variable of any type gets its universe as a parameter of the theorem, `"u_1"`, which the statement names:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfEquality, ForAll[{A, Typed[x, A]}, x == x], {A, x} |-> "equalityReflexivity"[x]]}][SelfEquality]
```

<!-- => theorem SelfEquality : ∀_A∶Sort u_1 ∀_x∶A x == x -->

---

Under rules without Prop, a theorem states a type. In homotopy type theory, a path from the base point of the circle to itself, the loop reversed:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory", {TypeTheoryTheorem[LoopInverse, "circleBase" == "circleBase", "equalitySymmetry"["circleLoop"]]}][LoopInverse]
```

<!-- => theorem LoopInverse : circleBase == circleBase -->

---

A proof with a hole, the commutativity of addition left to give:

```wl
later = TypeTheoryEnvironment[TypeTheoryTheorem[AdditionCommutes, TypeTheoryProof[
    ForAll[{m, n}, m + n == n + m],
    {"Introduce"[m, n], "Hole"}
]]]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The environment holds a constant for the hole before the theorem:

```wl
Take[Keys[later], -2]
```

<!-- => {TypeTheoryHole[AdditionCommutes, 1], AdditionCommutes} -->

The holes the theorem rests on:

```wl
Information[TypeTheoryTerm[AdditionCommutes, later], "Holes"]
```

<!-- => <|AdditionCommutes -> {<|"Hole" -> TypeTheoryHole[AdditionCommutes, 1], "Statement" -> ∀_m∶ℕ ∀_n∶ℕ m + n == n + m, "Annotation" -> None|>}|> -->

## Options

### Annotation

A theorem with a citation:

```wl
cited = TypeTheoryEnvironment[TypeTheoryTheorem[OnePlusOne, 1 + 1 == 2, "equalityReflexivity"[2], "Annotation" -> "Principia Mathematica, *54.43"]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The annotation, as it was given:

```wl
Information[TypeTheoryTerm[OnePlusOne, cited], "Annotation"]
```

<!-- => "Principia Mathematica, *54.43" -->

### UniverseParameters

The universe parameters named explicitly:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[
    SelfEquality,
    ForAll[{TypedImplicit[A, TypeUniverse[v]], Typed[x, A]}, x == x],
    {TypedImplicit[A, TypeUniverse[v]], x} |-> "equalityReflexivity"[x],
    "UniverseParameters" -> {v}
]}][SelfEquality]
```

<!-- => theorem SelfEquality : ∀_{A∶Sort v} ∀_x∶A x == x -->

## Properties and Relations

A theorem never unfolds. Proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

It computes to itself, not to its proof:

```wl
WeakHeadNormalForm[TypeTheoryTerm[TwoPlusTwo, arithmetic]]
```

<!-- => TwoPlusTwo -->

Any two proofs of a proposition are equal by computation, so it is still equal to its proof:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[TwoPlusTwo, arithmetic], TypeTheoryTerm["equalityReflexivity"[4], arithmetic]]
```

<!-- => True -->

It rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[TwoPlusTwo, arithmetic]]
```

<!-- => <||> -->

---

A theorem about the integers rests on the axiom that makes two classes of related pairs equal:

```wl
squares = TypeTheoryEnvironment["Integers", {TypeTheoryTheorem[SquareOfSum, TypeTheoryProof[
    ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + y)^2 == x^2 + 2 x y + y^2],
    "Integers",
    {"Introduce"[x, y], "Ring"}
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 357 constants -->

The axiom it rests on:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[SquareOfSum, squares]]
```

<!-- => <|"quotientSoundness" -> "Proposition"|> -->

---

<code>[Information]()[*env*, "Theorems"]</code> gives every theorem with its statement:

```wl
Take[Information[TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]], "Theorems"], -1]
```

<!-- => <|TwoPlusTwo -> 2 + 2 == 4|> -->

## Possible Issues

A proof of another statement is rejected:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Wrong, 2 + 2 == 5, "equalityReflexivity"[4]]]
```

<!-- => Failure["TypeMismatch", ...]: equalityReflexivity[4] has type 4 == 4, but the expected type is 2 + 2 == 5 -->

---

A theorem's statement must be a proposition:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Three, Naturals, 3]]
```

<!-- => Failure["PropositionExpected", ...] -->

---

A proof with goals left open is no proof:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Unfinished, TypeTheoryProof[
    ForAll[{m, n}, m + n == n + m],
    {"Introduce"[m, n]}
]]]
```

<!-- => Failure["ProofIncomplete", ...] -->

---

The two-argument form takes a [TypeTheoryProof](), not a proof term:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, "equalityReflexivity"[4]]]
```

<!-- => Failure["ProofExpected", ...] -->

---

The prelude proves `n + 0 == n` already, as `"additionZeroRight"`, so that name is taken:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem["additionZeroRight", ForAll[{n}, n + 0 == n], n |-> "equalityReflexivity"[n]]]
```

<!-- => Failure["AlreadyDeclared", ...] -->
