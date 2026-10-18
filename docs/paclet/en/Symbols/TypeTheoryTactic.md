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

Introduce a variable:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n]];
proof = TypeTheoryTactic["Introduce", n][proof];
proof["Goals"]
```

<!-- => {n ∶ ℕ ⊢ n + 0 == n} -->

Finish it by computation:

```wl
TypeTheoryTactic["Reflexivity"][proof]["Goals"]
```

<!-- => {} -->

## Scope

`"Apply"` leaves a goal for each argument, and `"Assumption"` closes one with a hypothesis:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a, Implies[b, And[a, b]]]], {
    TypeTheoryTactic["Introduce", a, b, ha, hb],
    TypeTheoryTactic["Apply", AndIntroduction],
    TypeTheoryTactic["Assumption"],
    TypeTheoryTactic["Exact", hb]
}];
proof["Term"]
```

<!-- => (a ∶ Prop) (b ∶ Prop) (ha ∶ a) (hb ∶ b) ↦ AndIntroduction[ha, hb] -->

---

Solving one goal can solve another it mentions:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, Implies[x == y, Implies[y == z, x == z]]], {
    TypeTheoryTactic["Introduce", x, y, z, h1, h2],
    TypeTheoryTactic["Apply", EqualityTransitivity],
    TypeTheoryTactic["Exact", h1],
    TypeTheoryTactic["Exact", h2]
}];
proof["Goals"]
```

<!-- => {} -->

---

`"Introduce"` unfolds [Not]():

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, Not[Not[p]]]], {
    TypeTheoryTactic["Introduce", p, hp, hnp],
    TypeTheoryTactic["Exact", hnp[hp]]
}];
proof["Goals"]
```

<!-- => {} -->

## Possible Issues

`"Reflexivity"` needs the sides to be equal by computation; `0 + n` is not `n` until induction:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
