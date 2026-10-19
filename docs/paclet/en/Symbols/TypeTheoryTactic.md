---
Template: Symbol
Name: TypeTheoryTactic
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTactic
Keywords: [tactic, proof, introduce, exact, apply, reflexivity, induction, assumption]
SeeAlso: [TypeTheoryProof, TypeTheoryTheorem, TypeTheoryTerm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryTactic]()[*name*, *arguments*...]</code> is a tactic: <code>[TypeTheoryTactic]()[*name*, *arguments*...][*proof*]</code> applies it to the first goal of the [TypeTheoryProof]() *proof*.

## Details & Options

- The tactics:

| Tactic | Effect |
|---|---|
| `"Introduce", x, ...` | moves the variables or hypotheses of a universal statement, implication or [Not]() into the context |
| `"Exact", term` | solves the goal with a term |
| `"Apply", term` | solves the goal with a term applied to new goals, as many as its conclusion needs |
| `"Reflexivity"` | solves `a == b` when the two sides are equal by computation |
| `"Induction", x` | one goal per constructor of the type of `x`, with induction hypotheses |
| `"Assumption"` | solves the goal with a hypothesis of the same type |

- [TypeTheoryTactic]() holds its arguments, so a term in `"Exact"` or `"Apply"` is not evaluated.
- A tactic that does not apply gives a [Failure]().

## Basic Examples

Start a proof with [TypeTheoryProof]():

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n]]
```

<!-- => Proof, 1 goal: ⊢ ∀_n∶ℕ n + 0 == n -->

Introduce a variable:

```wl
proof = TypeTheoryTactic["Introduce", n][proof]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ n + 0 == n -->

Finish it by computation:

```wl
TypeTheoryTactic["Reflexivity"][proof]
```

<!-- => Proof complete -->

## Scope

`"Apply"` leaves a goal for each argument of [AndIntroduction]():

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a, Implies[b, And[a, b]]]], {
    TypeTheoryTactic["Introduce", a, b, ha, hb],
    TypeTheoryTactic["Apply", AndIntroduction]
}]
```

<!-- => Proof, 2 goals: a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ a; a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ b -->

`"Assumption"` closes the first with a hypothesis:

```wl
proof = TypeTheoryTactic["Assumption"][proof]
```

<!-- => Proof, 1 goal: a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ b -->

`"Exact"` closes the second:

```wl
proof = TypeTheoryTactic["Exact", hb][proof]
```

<!-- => Proof complete -->

The proof term:

```wl
proof["Term"]
```

<!-- => (a ∶ Prop) (b ∶ Prop) (ha ∶ a) (hb ∶ b) ↦ AndIntroduction[ha, hb] -->

---

Applying [EqualityTransitivity]() leaves a goal for each equation, and one for the term between them, which both mention:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, Implies[x == y, Implies[y == z, x == z]]], {
    TypeTheoryTactic["Introduce", x, y, z, h1, h2],
    TypeTheoryTactic["Apply", EqualityTransitivity]
}]
```

<!-- => Proof, 3 goals: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x == y, h2 ∶ y == z ⊢ x == ?m; the same hypotheses ⊢ ?m == z; the same hypotheses ⊢ ℕ -->

Solving one goal can solve another it mentions: `h1` makes the term between them `y`:

```wl
proof = TypeTheoryTactic["Exact", h1][proof]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x == y, h2 ∶ y == z ⊢ y == z -->

The last goal is the other hypothesis:

```wl
proof = TypeTheoryTactic["Exact", h2][proof]
```

<!-- => Proof complete -->

---

`"Introduce"` unfolds [Not](), so the hypothesis of `¬¬p` is `¬p`, and its goal [False]():

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, Not[Not[p]]]], {
    TypeTheoryTactic["Introduce", p, hp, hnp]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, hp ∶ p, hnp ∶ ¬p ⊢ False -->

The two hypotheses contradict each other:

```wl
proof = TypeTheoryTactic["Exact", hnp[hp]][proof]
```

<!-- => Proof complete -->

## Possible Issues

`"Reflexivity"` needs the sides to be equal by computation; `0 + n` is not `n` until induction:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
