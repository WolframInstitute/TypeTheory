---
Template: Symbol
Name: TypeTheoryProof
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryProof
Keywords: [proof, goals, tactics, interactive proof, proof state, induction]
SeeAlso: [TypeTheoryTactic, TypeTheoryTheorem, TypeTheoryEnvironment, TypeTheoryTerm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryProof]()[*statement*]</code> starts a proof of *statement* in the prelude, with *statement* itself as its one goal.

<code>[TypeTheoryProof]()[*statement*, *env*]</code> starts it in the [TypeTheoryEnvironment]() *env*, and <code>[TypeTheoryProof]()[[TypeTheoryTerm]()[*statement*, *env*]]</code> does the same.

<code>[TypeTheoryProof]()[*statement*, {*tactic1*, *tactic2*, ...}]</code> and <code>[TypeTheoryProof]()[*statement*, *env*, {*tactic1*, ...}]</code> apply the [TypeTheoryTactic]() tactics in turn.

## Details & Options

- A proof holds a partial proof term with holes, its goals. A [TypeTheoryTactic]() works on the first goal and fills it with a term that may have new holes.
- In a notebook a proof shows each open goal as its hypotheses over the goal, with the constructor's name on goals that come from induction. The display stands for the proof itself: copied, or evaluated again, it gives the [TypeTheoryProof]().
- <code>*proof*["Goals"]</code> gives the open goals as <code>[TypeTheoryTerm]()[[RightTee]()[{[Typed]()[*x*, *type*], ...}, *goal*], *env*]</code>, each a statement in its own right. <code>*proof*["Term"]</code> gives the proof term, <code>*proof*["Statement"]</code> the statement and <code>*proof*["Environment"]</code> the environment.
- Nothing a tactic does is trusted: [TypeTheoryTheorem]() has the kernel check the finished proof term.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

Start a proof:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n]]
```

<!-- => Proof, 1 goal: ⊢ ∀_n∶ℕ 0 + n == n -->

Induction on `n` gives a goal for each constructor:

```wl
proof = TypeTheoryTactic["Induction", n][TypeTheoryTactic["Introduce", n][proof]]
```

<!-- => Proof, 2 goals: case NaturalNumberZero ⊢ 0 + 0 == 0; case NaturalNumberSuccessor ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

The first is true by computation; the second follows from the induction hypothesis:

```wl
proof = TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]][
    TypeTheoryTactic["Introduce", k, ih][TypeTheoryTactic["Reflexivity"][proof]]
]
```

<!-- => Proof complete -->

## Scope

All tactics at once:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

The proof term:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ EqualityReflexivity[n + 0] -->

---

Applying [AndIntroduction]() leaves a goal for each side of the conjunction:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a, Implies[b, And[a, b]]]], {
    TypeTheoryTactic["Introduce", a, b, ha, hb],
    TypeTheoryTactic["Apply", AndIntroduction]
}]
```

<!-- => Proof, 2 goals: a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ a; a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ b -->

The goals as statements:

```wl
proof["Goals"]
```

<!-- => {a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ a, a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ b} -->

## Properties and Relations

A finished proof:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n], {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Reflexivity"]}]
```

<!-- => Proof complete -->

A finished proof is declared with [TypeTheoryTheorem]():

```wl
proved = TypeTheoryEnvironment[TypeTheoryTheorem[ZeroRightIdentity, proof]]
```

<!-- => TypeTheoryEnvironment summary box: 159 constants -->

The theorem in the new environment:

```wl
proved[ZeroRightIdentity]
```

<!-- => theorem ZeroRightIdentity : ∀_n∶ℕ n + 0 == n -->

## Possible Issues

An unfinished proof cannot be declared:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Absurd, TypeTheoryProof[False]]]
```

<!-- => Failure["ProofIncomplete", ...] -->
