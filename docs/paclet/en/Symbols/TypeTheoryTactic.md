---
Template: Symbol
Name: TypeTheoryTactic
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTactic
Keywords: [tactic, proof, introduce, exact, apply, reflexivity, induction, cases, generalize, constructor, assumption, rewrite, change, simplify, decide, ring, FindInstance, PolynomialReduce, LinearArithmetic, linear arithmetic, FindEquationalProof, equational reasoning, oracle]
SeeAlso: [TypeTheoryProof, TypeTheoryTheorem, TypeTheoryTerm, Decidable, Lists]
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
| `"Induction", x` | one goal per constructor of the type of `x`, with induction hypotheses; the indices of an inductive family must be variables, and the hypotheses that depend on `x` are generalized |
| `"Cases", x` | one goal per constructor of the type of `x`, without induction hypotheses |
| `"Generalize", h, ...` | moves the hypotheses `h, ...`, with those that depend on them, back into the goal |
| `"Constructor"` | applies the first constructor of the goal's inductive type that applies |
| `"Assumption"` | solves the goal with a hypothesis of the same type |
| `"Rewrite", h` | replaces the first instance of the left side of the equation `h` in the goal, and every copy of it, by the right side, then closes a goal whose sides are the same |
| `"Rewrite", h, "RightToLeft"` | replaces the right side by the left |
| `"Rewrite", h, "At" -> k` | rewrites the hypothesis `k` instead of the goal; `"RightToLeft"` can come before `"At" -> k` |
| `"Change", statement` | replaces the goal by a statement equal to it by computation |
| `"Simplify", {h, ...}` | rewrites with the equations `h, ...` until none applies, unfolds each definition among them where it computes, then closes an equation whose sides are equal by computation |
| `"Decide"` | proves a closed statement by computing its decision, the instance of [Decidable]() that elaboration finds: the prelude's decide `==` and `<=` of natural numbers, [And](), [Or](), [Not](), [True]() and [False]() |
| `"Ring"` | proves an equation of natural numbers that holds in every commutative semiring, normalizing each side to a polynomial in its atoms with a proof from the prelude's laws |
| `"FindInstance"` | proves <code>[Exists]()[{[Typed]()[*x*, [Naturals]()], ...}, *p*]</code> with witnesses that Wolfram's [FindInstance]() finds, proving *p* of them by `"Decide"` |
| `"PolynomialReduce"` | proves an equation of natural numbers from the equations among the hypotheses, by a polynomial combination whose cofactors Wolfram finds, with [PolynomialReduce]() or linear algebra, and `"Ring"` checks |
| `"LinearArithmetic"` | proves an inequality, an equation or [False](), of natural numbers, from the inequalities and equations among the hypotheses, by a linear combination whose multipliers Wolfram's [FindInstance]() finds, each monomial counted as a variable |
| `"FindEquationalProof"` | proves an equation from the hypotheses that are equations of its type for all values of their variables, by replaying the proof that Wolfram's [FindEquationalProof]() finds, step by step |

- [TypeTheoryTactic]() holds its arguments, so a term in `"Exact"` or `"Apply"` is not evaluated.
- A definition by recursion on one of its arguments, such as [Join]() on its first, computes where that argument is a constructor applied; `"Simplify"` then folds each recursive call back into the definition, so `Join[ListPrepend[x, l], m]` becomes `ListPrepend[x, Join[l, m]]`, as Lean's `simp [f]` unfolds `f`.
- `"FindInstance"`, `"PolynomialReduce"`, `"LinearArithmetic"` and `"FindEquationalProof"` ask Wolfram for what the proof needs, and the kernel checks the proof built from the answer: a wrong answer can make the tactic fail, never prove a false statement.
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

---

`"Induction"` on a list leaves a goal for the empty list and one for a list with a first element:

```wl
proof = TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Join[l, EmptyList] == l], {
    TypeTheoryTactic["Introduce", l],
    TypeTheoryTactic["Induction", l]
}]
```

<!-- => Proof, 2 goals: case EmptyList ⊢ Join[EmptyList, EmptyList] == EmptyList; case ListPrepend ⊢ ∀_x∶ℕ ∀_l∶Lists[ℕ] Join[l, EmptyList] == l ⇒ Join[ListPrepend[x, l], EmptyList] == ListPrepend[x, l] -->

`"Simplify"` unfolds [Join]() on the empty list, and the sides are then the same:

```wl
proof = TypeTheoryTactic["Simplify", {Join}][proof]
```

<!-- => Proof, 1 goal: case ListPrepend ⊢ ∀_x∶ℕ ∀_l∶Lists[ℕ] Join[l, EmptyList] == l ⇒ Join[ListPrepend[x, l], EmptyList] == ListPrepend[x, l] -->

Introduce the first element, the rest and the induction hypothesis:

```wl
proof = TypeTheoryTactic["Introduce", x, rest, ih][proof]
```

<!-- => Proof, 1 goal: x ∶ ℕ, rest ∶ Lists[ℕ], ih ∶ Join[rest, EmptyList] == rest ⊢ Join[ListPrepend[x, rest], EmptyList] == ListPrepend[x, rest] -->

Unfolding [Join]() once more brings out `Join[rest, EmptyList]`, which the induction hypothesis rewrites:

```wl
proof = TypeTheoryTactic["Simplify", {Join, ih}][proof]
```

<!-- => Proof complete -->

---

`"Rewrite"` replaces `a` by `b`, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, Implies[a == b, a + 1 == b + 1]], {
    TypeTheoryTactic["Introduce", a, b, h],
    TypeTheoryTactic["Rewrite", h]
}]
```

<!-- => Proof complete -->

---

With `"At" -> k`, the hypothesis `k` is rewritten instead:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, Implies[a == b, Implies[a + 1 == 3, b + 1 == 3]]], {
    TypeTheoryTactic["Introduce", a, b, h, k],
    TypeTheoryTactic["Rewrite", h, "At" -> k]
}]
```

<!-- => Proof, 1 goal: a ∶ ℕ, b ∶ ℕ, h ∶ a == b, k ∶ b + 1 == 3 ⊢ b + 1 == 3 -->

The rewritten hypothesis is the goal:

```wl
TypeTheoryTactic["Exact", k][proof]
```

<!-- => Proof complete -->

---

`"Cases"` splits a natural number into zero and a successor, with no induction hypothesis:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Or[n == 0, Exists[{Typed[k, Naturals]}, n == k + 1]]], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Cases", n]
}]
```

<!-- => Proof, 2 goals: case NaturalNumberZero ⊢ 0 == 0 ∨ ∃_k∶ℕ 0 == k + 1; case NaturalNumberSuccessor ⊢ ∀_n∶ℕ (n + 1 == 0 ∨ ∃_k∶ℕ n + 1 == k + 1) -->

---

`"Constructor"` applies [AndIntroduction](), the constructor of [And]():

```wl
TypeTheoryProof[And[True, 2 == 2], {TypeTheoryTactic["Constructor"]}]
```

<!-- => Proof, 2 goals: ⊢ True; ⊢ 2 == 2 -->

---

`"Generalize"` moves `m` back into the goal, with `h`, which depends on it:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals], Typed[m, Naturals]}, Implies[n == m, m == n]], {
    TypeTheoryTactic["Introduce", n, m, h],
    TypeTheoryTactic["Generalize", m]
}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ ∀_m∶ℕ n == m ⇒ m == n -->

---

`"Change"` replaces the goal by one equal to it by computation:

```wl
TypeTheoryProof[2 + 2 == 4, {TypeTheoryTactic["Change", 4 == 4]}]
```

<!-- => Proof, 1 goal: ⊢ 4 == 4 -->

---

`"Decide"` proves a closed statement by computing its decision, which it finds among the instances of [Decidable]():

```wl
TypeTheoryProof[And[3 + 4 == 7, Not[2 == 3]], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

---

`"Ring"` proves a polynomial identity:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, (a + b)^2 == a^2 + 2 a b + b^2], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

---

`"FindInstance"` asks Wolfram for natural numbers with a property:

```wl
proof = TypeTheoryProof[Exists[{Typed[x, Naturals], Typed[y, Naturals]}, And[x^2 + y^2 == 25, 0 < x, x < y]], {TypeTheoryTactic["FindInstance"]}]
```

<!-- => Proof complete -->

The proof holds the witnesses; the decision that the kernel computes for them is the instance argument of [DecideSoundness](), which a term does not show:

```wl
proof["Term"]
```

<!-- => ExistsIntroduction[3, ExistsIntroduction[4, DecideSoundness[EqualityReflexivity[true]]]] -->

---

`"PolynomialReduce"` finds how the hypotheses combine into the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x + y == 10, Implies[x == 2 y + 1, x y == 21]]], {
    TypeTheoryTactic["Introduce", x, y, h, k],
    TypeTheoryTactic["PolynomialReduce"]
}]
```

<!-- => Proof complete -->

---

`"LinearArithmetic"` multiplies and adds inequalities:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[2 x + 3 y <= 12, Implies[4 <= x, y <= 1]]], {
    TypeTheoryTactic["Introduce", x, y, h, k],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->

---

`"FindEquationalProof"` derives the right identity of a group from its left identity and left inverses:

```wl
TypeTheoryProof[ForAll[
    {Typed[G, TypeUniverse[1]], Typed[op, TypeSpecifier[{G, G} -> G]], Typed[e, G], Typed[inv, TypeSpecifier[{G} -> G]]},
    Implies[ForAll[{Typed[a, G], Typed[b, G], Typed[c, G]}, op[op[a, b], c] == op[a, op[b, c]]],
        Implies[ForAll[{Typed[a, G]}, op[e, a] == a],
            Implies[ForAll[{Typed[a, G]}, op[inv[a], a] == e], ForAll[{Typed[x, G]}, op[x, e] == x]]]]
], {
    TypeTheoryTactic["Introduce", G, op, e, inv, associativity, identity, inverse, x],
    TypeTheoryTactic["FindEquationalProof"]
}]
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

---

`"Decide"` needs a closed statement; with a variable there is nothing to compute:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n <= n + 1], {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Decide"]}]
```

<!-- => Failure["NotDecided", ...] -->

---

A definition by recursion does not unfold on a variable, where it does not compute; `"Induction"` on the variable comes first:

```wl
TypeTheoryProof[ForAll[{Typed[l, Lists[Naturals]]}, Join[l, EmptyList] == l], {TypeTheoryTactic["Introduce", l], TypeTheoryTactic["Simplify", {Join}]}]
```

<!-- => Failure["NoProgress", ...] -->

---

`"Induction"` on a proof of an inductive family needs its indices to be variables:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, Implies[a <= b + 1, a <= b + 2]], {
    TypeTheoryTactic["Introduce", a, b, h],
    TypeTheoryTactic["Induction", h]
}]
```

<!-- => Failure["IndexNotVariable", ...] -->

---

`"Ring"` proves only what holds in every commutative semiring:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, (a + b)^2 == a^2 + b^2], {TypeTheoryTactic["Introduce", a, b], TypeTheoryTactic["Ring"]}]
```

<!-- => Failure["NotRingEquation", ...] -->

---

`"FindInstance"` needs a statement of the variables it binds alone; a hypothesis in it is not translated:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, Exists[{Typed[n, Naturals]}, n == m + 1]], {TypeTheoryTactic["Introduce", m], TypeTheoryTactic["FindInstance"]}]
```

<!-- => Failure["NotTranslatable", ...] -->

---

`"LinearArithmetic"` proves only what follows from the hypotheses:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, y <= x]], {TypeTheoryTactic["Introduce", x, y, h], TypeTheoryTactic["LinearArithmetic"]}]
```

<!-- => Failure["NoLinearCombination", ...] -->
