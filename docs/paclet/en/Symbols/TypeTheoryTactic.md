---
Template: Symbol
Name: TypeTheoryTactic
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTactic
Keywords: [tactic, proof, introduce, exact, apply, reflexivity, induction, cases, generalize, constructor, assumption, rewrite, change, simplify, decide, classical, truth table, ring, FindInstance, PolynomialReduce, LinearArithmetic, linear arithmetic, linarith, NonlinearArithmetic, nonlinear arithmetic, nlinarith, FindEquationalProof, equational reasoning, SumOfSquares, sum of squares, SemidefiniteOptimization, hole, sorry, oracle]
SeeAlso: [TypeTheoryProof, TypeTheoryTheorem, TypeTheoryHole, TypeTheoryTerm, Decidable, Decide, List]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ProgramsAndProofs]
---

## Usage

<code>[TypeTheoryTactic]()[*name*, *arguments*...]</code> is a tactic: <code>[TypeTheoryTactic]()[*name*, *arguments*...][*proof*]</code> applies it to the first goal of the [TypeTheoryProof]() *proof*.

<code>[TypeTheoryTactic]()[*name*[*arguments*...]]</code> is <code>[TypeTheoryTactic]()[*name*, *arguments*...]</code>.

## Details & Options

- The tactics:

| Tactic | Effect |
|---|---|
| `"Introduce", x, ...` | moves the variables or hypotheses of a universal statement, implication or [Not]() into the context, named `x, ...`; `"Introduce"` alone moves one, with the name of its binder |
| `"Exact", term` | solves the goal with a term |
| `"Apply", term` | solves the goal with a term applied to new goals, as many as its conclusion needs |
| `"Reflexivity"` | solves `a == b` when the two sides are equal by computation |
| `"Induction", x` | one goal per constructor of the type of `x`, with induction hypotheses; the indices of an inductive family must be variables, and the hypotheses that depend on `x` are generalized. On a class of a quotient, one goal for the class of an element |
| `"Cases", x` | one goal per constructor of the type of `x`, without induction hypotheses |
| `"Generalize", h, ...` | moves the hypotheses `h, ...`, with those that depend on them, back into the goal |
| `"Constructor"` | applies the first constructor of the goal's inductive type that applies |
| `"Assumption"` | solves the goal with a hypothesis of the same type |
| `"Hole"`, `"Hole", annotation` | closes the goal with a [TypeTheoryHole](), a proof left to give, which the theorem declared with the proof keeps |
| `"Rewrite", h` | replaces the first instance of the left side of the equation `h` in the goal, and every copy of it, by the right side, then closes a goal whose sides are the same |
| `"Rewrite", h, "RightToLeft"` | replaces the right side by the left |
| `"Rewrite", h, "At" -> k` | rewrites the hypothesis `k` instead of the goal; `"RightToLeft"` can come before `"At" -> k` |
| `"Change", statement` | replaces the goal by a statement equal to it by computation |
| `"RewriteRepeated", h, ...` | rewrites with the equations `h, ...` until none applies, as [ReplaceRepeated]() does where `"Rewrite"` is [Replace](); unfolds each definition among them where it computes, then closes an equation whose sides are equal by computation; the equations may also be one list |
| `"Decide"` | proves a statement by computing its decision, the instance of [Decidable]() that elaboration finds: the prelude's instances decide `==` and `<=` of natural numbers, `==` of Booleans, [And](), [Or](), [Not](), [True]() and [False](). A closed statement always computes; one with variables computes only where its decision does not depend on them |
| `"Ring"` | proves an equation of natural numbers that holds in every commutative semiring, normalizing each side to a polynomial in its atoms with a proof from the prelude's laws; in <code>[TypeTheoryEnvironment]()["Integers"]</code>, an equation of integers that holds in every commutative ring, by normal forms with proofs from the integers' laws |
| `"Classical"` | proves a statement of classical propositional logic from the hypotheses that are propositions, by a truth table: each atom, a proposition that no connective builds, is split by `"excludedMiddle"`, and the goal is built from the cases under every assignment that makes the hypotheses true |
| `"FindInstance"` | proves <code>[Exists]()[{[Typed]()[*x*, [Naturals]()], ...}, *p*]</code> with witnesses that Wolfram's [FindInstance]() finds, proving *p* of them by `"Decide"` |
| `"PolynomialReduce"` | proves an equation of natural numbers from the equations among the hypotheses, by a polynomial combination whose cofactors Wolfram finds, with [PolynomialReduce]() or linear algebra, and `"Ring"` checks; in <code>[TypeTheoryEnvironment]()["Integers"]</code>, an equation of integers from the equations of integers |
| `"LinearArithmetic"` | proves an inequality, an equation or [False](), of natural numbers, from the inequalities and equations among the hypotheses, by a linear combination whose multipliers Wolfram's [FindInstance]() finds, each monomial counted as a variable |
| `"NonlinearArithmetic"` | proves what `"LinearArithmetic"` proves from the inequalities among the hypotheses and their products: each inequality a <= b times each side k of each, a k <= b k, so that n <= m gives n n <= m m |
| `"FindEquationalProof"` | proves an equation from the hypotheses that are equations of its type for all values of their variables, by replaying the proof that Wolfram's [FindEquationalProof]() finds, step by step |
| `"SumOfSquares"` | in <code>[TypeTheoryEnvironment]()["Integers"]</code>, proves an inequality of integers or of natural numbers whose larger side less the smaller, times a positive integer, is a sum of squares of polynomials that Wolfram finds with exact linear algebra, linear inequalities and [SemidefiniteOptimization](); `"integerLessEqualOfMultiple"` takes the equation, which `"Ring"` proves, and the proof that the sum is at least 0 |

- [TypeTheoryTactic]() holds its arguments, so a term in `"Exact"` or `"Apply"` is not evaluated.
- In a list of tactics written out in [TypeTheoryProof](), a tactic is written as its name, or its name applied to its arguments: <code>{"Introduce"[n], "Reflexivity"}</code> is <code>{[TypeTheoryTactic]()["Introduce", n], [TypeTheoryTactic]()["Reflexivity"]}</code>, and its arguments are held as well.
- A definition by recursion on one of its arguments, such as [Join]() on its first, computes where that argument is a constructor applied; `"RewriteRepeated"` then folds each recursive call back into the definition, so `Join[Prepend[x][l], m]` becomes `Prepend[x][Join[l, m]]`. A definition applied to another unfolds after the inner one, so for a sum `total` defined by recursion on lists, `total[Join[Prepend[x][l], m]]` becomes `x + total[Join[l, m]]`, where an induction hypothesis about `total[Join[l, m]]` applies.
- `"FindInstance"`, `"PolynomialReduce"`, `"LinearArithmetic"`, `"NonlinearArithmetic"`, `"FindEquationalProof"` and `"SumOfSquares"` ask Wolfram for what the proof needs, and the kernel checks the proof built from the answer: a wrong answer can make the tactic fail, never prove a false statement.
- `"NonlinearArithmetic"` multiplies once: it adds products of two factors, not of three.
- The proofs `"LinearArithmetic"` and `"NonlinearArithmetic"` build compute with the literals of the statement, and with a few hundred, or with products of a few dozen, the kernel can reject the proof as a computation too deep to check.
- A tactic that does not apply gives a [Failure]() that says why, with the goal.

## Basic Examples

A proof as a list of tactics, each its name applied to its arguments:

```wl
TypeTheoryProof[ForAll[{n}, n + 0 == n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

---

Start a proof with [TypeTheoryProof]():

```wl
proof = TypeTheoryProof[ForAll[{n}, n + 0 == n]]
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

---

A tactic works on the first goal. Induction leaves two:

```wl
proof = TypeTheoryProof[ForAll[{n}, 0 + n == n], {"Introduce"[n], "Induction"[n]}]
```

<!-- => Proof, 2 goals: case zero ⊢ 0 + 0 == 0; case successor ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

`"Reflexivity"` closes the first, the case of zero:

```wl
TypeTheoryTactic["Reflexivity"][proof]
```

<!-- => Proof, 1 goal: case successor ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

## Scope

### Introduction and Exact Terms

`"Introduce"` moves a variable and a hypothesis into the context:

```wl
TypeTheoryProof[ForAll[{n}, Implies[n == 0, n + n == 0]], {"Introduce"[n, h]}]
```

<!-- => Proof, 1 goal: n ∶ ℕ, h ∶ n == 0 ⊢ n + n == 0 -->

---

`"Introduce"` without names moves one variable, named as its binder:

```wl
TypeTheoryProof[ForAll[{n, m}, n + m == m + n], {"Introduce"}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ ∀_m∶ℕ n + m == m + n -->

---

`"Introduce"` unfolds [Not](), so the hypothesis of `¬¬p` is `¬p`, and its goal [False]():

```wl
proof = TypeTheoryProof[ForAll[{p}, Implies[p, Not[Not[p]]]], {
    "Introduce"[p, hp, hnp]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, hp ∶ p, hnp ∶ ¬p ⊢ False -->

The two hypotheses contradict each other:

```wl
TypeTheoryTactic["Exact", hnp[hp]][proof]
```

<!-- => Proof complete -->

---

`"Exact"` solves a goal with a theorem of the prelude, applied to the variables:

```wl
TypeTheoryProof[ForAll[{n, m}, n + m == m + n], {"Introduce"[n, m], "Exact"["additionCommutativity"[n, m]]}]
```

<!-- => Proof complete -->

---

`"Apply"` leaves a goal for each argument of `"andIntroduction"`:

```wl
proof = TypeTheoryProof[ForAll[{a, b}, Implies[a, Implies[b, And[a, b]]]], {
    "Introduce"[a, b, ha, hb],
    "Apply"["andIntroduction"]
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

<!-- => (a ∶ Prop) (b ∶ Prop) (ha ∶ a) (hb ∶ b) ↦ andIntroduction[ha, hb] -->

---

Applying `"equalityTransitivity"` leaves a goal for each equation, and one for the term between them, an unknown shown as `?` and a number, which both mention:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, Implies[x == y, Implies[y == z, x == z]]], {
    "Introduce"[x, y, z, h1, h2],
    "Apply"["equalityTransitivity"]
}]
```

<!-- => Proof, 3 goals: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x == y, h2 ∶ y == z ⊢ x == ?...; x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x == y, h2 ∶ y == z ⊢ ?... == z; x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x == y, h2 ∶ y == z ⊢ ℕ -->

Solving one goal can solve another it mentions: `h1` makes the term between them `y`:

```wl
proof = TypeTheoryTactic["Exact", h1][proof]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x == y, h2 ∶ y == z ⊢ y == z -->

The last goal is the other hypothesis:

```wl
TypeTheoryTactic["Exact", h2][proof]
```

<!-- => Proof complete -->

---

`"Apply"` with a witness of an existential statement leaves its property to prove:

```wl
proof = TypeTheoryProof[Exists[{n}, n n == 49], {"Apply"["existsIntroduction"[7]]}]
```

<!-- => Proof, 1 goal: ⊢ 7 7 == 49 -->

It holds by computation:

```wl
TypeTheoryTactic["Reflexivity"][proof]
```

<!-- => Proof complete -->

---

`"Constructor"` applies `"andIntroduction"`, the constructor of [And]():

```wl
proof = TypeTheoryProof[And[True, 2 == 2], {"Constructor"}]
```

<!-- => Proof, 2 goals: ⊢ True; ⊢ 2 == 2 -->

[True]() has a constructor too, which proves it:

```wl
TypeTheoryTactic["Constructor"][proof]
```

<!-- => Proof, 1 goal: ⊢ 2 == 2 -->

---

`"Change"` shows what a definition means: `n < n + 1` is `n + 1 <= n + 1` by computation:

```wl
proof = TypeTheoryProof[ForAll[{n}, n < n + 1], {"Introduce"[n], "Change"[n + 1 <= n + 1]}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ n + 1 <= n + 1 -->

`"lessEqualReflexivity"`, a constructor of [LessEqual](), proves it:

```wl
TypeTheoryTactic["Exact", "lessEqualReflexivity"][proof]
```

<!-- => Proof complete -->

---

`"Generalize"` moves `m` back into the goal, with `h`, which depends on it:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals], Typed[m, Naturals]}, Implies[n == m, m == n]], {
    "Introduce"[n, m, h],
    "Generalize"[m]
}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ ∀_m∶ℕ n == m ⇒ m == n -->

Induction on `n` then has a hypothesis for every `m`:

```wl
TypeTheoryTactic["Induction", n][proof]
```

<!-- => Proof, 2 goals: case zero ⊢ ∀_m∶ℕ 0 == m ⇒ m == 0; case successor ⊢ ∀_n∶ℕ (∀_m∶ℕ n == m ⇒ m == n) ⇒ ∀_m∶ℕ n + 1 == m ⇒ m == n + 1 -->

### Induction and Cases

`"Induction"` on a list leaves a goal for the empty list and one for a list with a first element:

```wl
proof = TypeTheoryProof[ForAll[{Typed[l, {Naturals}]}, Join[l, {}] == l], {
    "Introduce"[l],
    "Induction"[l]
}]
```

<!-- => Proof, 2 goals: case {} ⊢ Join[{}, {}] == {}; case Prepend ⊢ ∀_x∶ℕ ∀_l∶{ℕ} Join[l, {}] == l ⇒ Join[Prepend • x • l, {}] == Prepend • x • l -->

`"RewriteRepeated"` unfolds [Join]() on the empty list, and the sides are then the same:

```wl
proof = TypeTheoryTactic["RewriteRepeated", Join][proof]
```

<!-- => Proof, 1 goal: case Prepend ⊢ ∀_x∶ℕ ∀_l∶{ℕ} Join[l, {}] == l ⇒ Join[Prepend • x • l, {}] == Prepend • x • l -->

Introduce the first element, the rest and the induction hypothesis:

```wl
proof = TypeTheoryTactic["Introduce", x, rest, ih][proof]
```

<!-- => Proof, 1 goal: x ∶ ℕ, rest ∶ {ℕ}, ih ∶ Join[rest, {}] == rest ⊢ Join[Prepend • x • rest, {}] == Prepend • x • rest -->

Unfolding [Join]() once more brings out `Join[rest, {}]`, which the induction hypothesis rewrites:

```wl
TypeTheoryTactic["RewriteRepeated", Join, ih][proof]
```

<!-- => Proof complete -->

---

On an integer, a class of pairs of natural numbers, `"Induction"` leaves a goal for the class of a pair:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x + 0 == x], "Integers", {
    "Introduce"[x],
    "Induction"[x]
}]
```

<!-- => Proof, 1 goal: case QuotientIntroduction ⊢ ∀_a∶ℕ × ℕ QuotientIntroduction[integerRelation, a] + 0 == QuotientIntroduction[integerRelation, a] -->

---

`"Induction"` on a proof of `a <= b`, an inductive family whose index `b` is a variable, leaves a goal for each of its constructors:

```wl
TypeTheoryProof[ForAll[{a, b}, Implies[a <= b, a + 1 <= b + 1]], {
    "Introduce"[a, b, h],
    "Induction"[h]
}]
```

<!-- => Proof, 2 goals: case lessEqualReflexivity a ∶ ℕ ⊢ a + 1 <= a + 1; case lessEqualStep a ∶ ℕ ⊢ ∀_{m∶ℕ} a <= m ⇒ a + 1 <= m + 1 ⇒ a + 1 <= m + 1 + 1 -->

Each is a constructor of [LessEqual]() applied:

```wl
TypeTheoryProof[ForAll[{a, b}, Implies[a <= b, a + 1 <= b + 1]], {
    "Introduce"[a, b, h],
    "Induction"[h],
    "Exact"["lessEqualReflexivity"],
    "Introduce"[c, hc, ih],
    "Exact"["lessEqualStep"[ih]]
}]
```

<!-- => Proof complete -->

---

`"Induction"` takes along the hypotheses that depend on the variable, here `h`, so that each case has its own:

```wl
TypeTheoryProof[ForAll[{n, m}, Implies[n == m, n + 0 == m]], {
    "Introduce"[n, m, h],
    "Induction"[n]
}]
```

<!-- => Proof, 2 goals: case zero m ∶ ℕ ⊢ 0 == m ⇒ 0 + 0 == m; case successor m ∶ ℕ ⊢ ∀_n∶ℕ (n == m ⇒ n + 0 == m) ⇒ n + 1 == m ⇒ n + 1 + 0 == m -->

---

`"Cases"` splits a natural number into zero and a successor, with no induction hypothesis:

```wl
TypeTheoryProof[ForAll[{n}, Or[n == 0, Exists[{k}, n == k + 1]]], {
    "Introduce"[n],
    "Cases"[n]
}]
```

<!-- => Proof, 2 goals: case zero ⊢ 0 == 0 ∨ ∃_k∶ℕ 0 == k + 1; case successor ⊢ ∀_n∶ℕ (n + 1 == 0 ∨ ∃_k∶ℕ n + 1 == k + 1) -->

Zero is the left case, and `k + 1` the right one with the witness `k`:

```wl
TypeTheoryProof[ForAll[{n}, Or[n == 0, Exists[{k}, n == k + 1]]], {
    "Introduce"[n],
    "Cases"[n],
    "Exact"["orIntroductionLeft"["equalityReflexivity"[0]]],
    "Introduce"[k],
    "Exact"["orIntroductionRight"["existsIntroduction"[k, "equalityReflexivity"[k + 1]]]]
}]
```

<!-- => Proof complete -->

---

`"Cases"` takes a conjunction apart into its two proofs:

```wl
proof = TypeTheoryProof[ForAll[{p, q}, Implies[p && q, q && p]], {
    "Introduce"[p, q, h],
    "Cases"[h],
    "Introduce"[hp, hq]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, q ∶ Prop, hp ∶ p, hq ∶ q ⊢ q ∧ p -->

The conjunction the other way round:

```wl
TypeTheoryTactic["Exact", "andIntroduction"[hq, hp]][proof]
```

<!-- => Proof complete -->

---

On a disjunction, `"Cases"` leaves a goal for each side:

```wl
TypeTheoryProof[ForAll[{p, q}, Implies[p || q, q || p]], {
    "Introduce"[p, q, h],
    "Cases"[h]
}]
```

<!-- => Proof, 2 goals: case orIntroductionLeft p ∶ Prop, q ∶ Prop ⊢ p ⇒ (q ∨ p); case orIntroductionRight p ∶ Prop, q ∶ Prop ⊢ q ⇒ (q ∨ p) -->

---

On an existential statement, `"Cases"` gives the witness and its property. If `n` is `k + k`, then `n + 2` is even too:

```wl
proof = TypeTheoryProof[ForAll[{n}, Implies[Exists[{k}, n == k + k], Exists[{j}, n + 2 == j + j]]], {
    "Introduce"[n, h],
    "Cases"[h],
    "Introduce"[k, hk]
}]
```

<!-- => Proof, 1 goal: n ∶ ℕ, k ∶ ℕ, hk ∶ n == k + k ⊢ ∃_j∶ℕ n + 2 == j + j -->

The witness is `k + 1`:

```wl
proof = TypeTheoryTactic["Apply", "existsIntroduction"[k + 1]][proof]
```

<!-- => Proof, 1 goal: n ∶ ℕ, k ∶ ℕ, hk ∶ n == k + k ⊢ n + 2 == k + 1 + (k + 1) -->

`hk` replaces `n`:

```wl
proof = TypeTheoryTactic["Rewrite", hk][proof]
```

<!-- => Proof, 1 goal: n ∶ ℕ, k ∶ ℕ, hk ∶ n == k + k ⊢ k + k + 2 == k + 1 + (k + 1) -->

The rest is algebra:

```wl
TypeTheoryTactic["Ring"][proof]
```

<!-- => Proof complete -->

### Rewriting and Simplification

`"Rewrite"` replaces the left side of an equation by its right side, every copy of it:

```wl
proof = TypeTheoryProof[ForAll[{a, b, c}, Implies[a == b + c, a a == (b + c) a]], {
    "Introduce"[a, b, c, h]
}]
```

<!-- => Proof, 1 goal: a ∶ ℕ, b ∶ ℕ, c ∶ ℕ, h ∶ a == b + c ⊢ a a == (b + c) a -->

Both sides become `(b + c) (b + c)`, and the goal closes:

```wl
TypeTheoryTactic["Rewrite", h][proof]
```

<!-- => Proof complete -->

---

With `"RightToLeft"`, the right side is replaced by the left:

```wl
proof = TypeTheoryProof[ForAll[{a, b}, Implies[a == b, b + b == 2 a]], {
    "Introduce"[a, b, h],
    "Rewrite"[h, "RightToLeft"]
}]
```

<!-- => Proof, 1 goal: a ∶ ℕ, b ∶ ℕ, h ∶ a == b ⊢ a + a == 2 a -->

The rest is algebra:

```wl
TypeTheoryTactic["Ring"][proof]
```

<!-- => Proof complete -->

---

With `"At" -> k`, the hypothesis `k` is rewritten instead:

```wl
proof = TypeTheoryProof[ForAll[{a, b}, Implies[a == b, Implies[a + 1 == 3, b + 1 == 3]]], {
    "Introduce"[a, b, h, k],
    "Rewrite"[h, "At" -> k]
}]
```

<!-- => Proof, 1 goal: a ∶ ℕ, b ∶ ℕ, h ∶ a == b, k ∶ b + 1 == 3 ⊢ b + 1 == 3 -->

The rewritten hypothesis is the goal:

```wl
TypeTheoryTactic["Exact", k][proof]
```

<!-- => Proof complete -->

---

`"Rewrite"` with a theorem finds an instance of its left side. `"lengthJoin"` says that the length of `Join[a, b]` is the sum of the lengths:

```wl
proof = TypeTheoryProof[ForAll[{Typed[l, {Naturals}], Typed[m, {Naturals}]}, Length[Join[l, m]] == Length[Join[m, l]]], {
    "Introduce"[l, m],
    "Rewrite"["lengthJoin"]
}]
```

<!-- => Proof, 1 goal: l ∶ {ℕ}, m ∶ {ℕ} ⊢ Length[l] + Length[m] == Length[Join[m, l]] -->

The other instance:

```wl
proof = TypeTheoryTactic["Rewrite", "lengthJoin"][proof]
```

<!-- => Proof, 1 goal: l ∶ {ℕ}, m ∶ {ℕ} ⊢ Length[l] + Length[m] == Length[m] + Length[l] -->

Addition commutes:

```wl
TypeTheoryTactic["Ring"][proof]
```

<!-- => Proof complete -->

---

`"RewriteRepeated"` rewrites with several theorems until none applies. The length of a reversed join:

```wl
TypeTheoryProof[ForAll[{Typed[l, {Naturals}], Typed[m, {Naturals}]}, Length[Reverse[Join[l, m]]] == Length[l] + Length[m]], {
    "Introduce"[l, m],
    "RewriteRepeated"["lengthReverse", "lengthJoin"]
}]
```

<!-- => Proof complete -->

---

A definition among the equations of `"RewriteRepeated"` unfolds where it computes. [Length]() computes on a list with a first element:

```wl
TypeTheoryProof[ForAll[{x, Typed[l, {Naturals}]}, Length[Prepend[x][l]] == Length[l] + 1], {
    "Introduce"[x, l],
    "RewriteRepeated"[Length]
}]
```

<!-- => Proof complete -->

### Arithmetic

`"Ring"` proves a polynomial identity of natural numbers:

```wl
TypeTheoryProof[ForAll[{a, b}, (a + b)^2 == a^2 + 2 a b + b^2], {
    "Introduce"[a, b],
    "Ring"
}]
```

<!-- => Proof complete -->

---

In the integers, `"Ring"` proves what holds in every commutative ring, subtraction included:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y) (x + y) == x^2 - y^2], "Integers", {
    "Introduce"[x, y],
    "Ring"
}]
```

<!-- => Proof complete -->

---

`"PolynomialReduce"` proves an equation from the equations among the hypotheses. Here `x` and `y` are 7 and 3:

```wl
proof = TypeTheoryProof[ForAll[{x, y}, Implies[x + y == 10, Implies[x == 2 y + 1, x y == 21]]], {
    "Introduce"[x, y, h, k]
}]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, h ∶ x + y == 10, k ∶ x == 2 y + 1 ⊢ x y == 21 -->

Wolfram finds how the hypotheses combine into the goal:

```wl
TypeTheoryTactic["PolynomialReduce"][proof]
```

<!-- => Proof complete -->

---

In the integers, from the equations of integers among the hypotheses:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x == y + 1, x^2 - y^2 == x + y]], "Integers", {
    "Introduce"[x, y, h],
    "PolynomialReduce"
}]
```

<!-- => Proof complete -->

---

`"LinearArithmetic"` multiplies and adds inequalities: with `x` at least 4, `2 x + 3 y <= 12` leaves room for `y` to be at most 1:

```wl
TypeTheoryProof[ForAll[{x, y}, Implies[2 x + 3 y <= 12, Implies[4 <= x, y <= 1]]], {
    "Introduce"[x, y, h, k],
    "LinearArithmetic"
}]
```

<!-- => Proof complete -->

---

`"LinearArithmetic"` proves [False]() from hypotheses that contradict each other:

```wl
TypeTheoryProof[ForAll[{x, y}, Implies[x + 1 <= y, Implies[y <= x, False]]], {
    "Introduce"[x, y, h, k],
    "LinearArithmetic"
}]
```

<!-- => Proof complete -->

---

`"NonlinearArithmetic"` multiplies the inequalities among the hypotheses by their sides, so `n <= m` gives `n n <= m m`:

```wl
TypeTheoryProof[ForAll[{n, m}, Implies[n <= m, n n <= m m]], {
    "Introduce"[n, m, h],
    "NonlinearArithmetic"
}]
```

<!-- => Proof complete -->

---

Two inequalities multiply:

```wl
proof = TypeTheoryProof[ForAll[{a, b, c, d}, Implies[a <= b, Implies[c <= d, a c <= b d]]], {
    "Introduce"[a, b, c, d, h1, h2]
}]
```

<!-- => Proof, 1 goal: a ∶ ℕ, b ∶ ℕ, c ∶ ℕ, d ∶ ℕ, h1 ∶ a <= b, h2 ∶ c <= d ⊢ a c <= b d -->

The products `a c <= b c` and `b c <= b d` add up to the goal:

```wl
TypeTheoryTactic["NonlinearArithmetic"][proof]
```

<!-- => Proof complete -->

---

`"SumOfSquares"` proves an inequality of integers whose larger side less the smaller is a sum of squares, here half the sum of the squares of `x - y`, `y - z` and `z - x`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x y + y z + z x <= x^2 + y^2 + z^2], "Integers", {
    "Introduce"[x, y, z],
    "SumOfSquares"
}]
```

<!-- => Proof complete -->

---

In the integers' environment, `"SumOfSquares"` proves inequalities of natural numbers too, here that `(a - b)^2` is at least 0:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, 2 a b <= a^2 + b^2], "Integers", {
    "Introduce"[a, b],
    "SumOfSquares"
}]
```

<!-- => Proof complete -->

### Decision

`"Decide"` proves a statement by computing its decision, which it finds among the instances of [Decidable](); a closed statement always computes:

```wl
TypeTheoryProof[And[3 + 4 == 7, Not[2 == 3]], {"Decide"}]
```

<!-- => Proof complete -->

---

With a variable, the decision computes where it does not depend on the variable. A successor is never 0:

```wl
TypeTheoryProof[ForAll[{n}, n + 1 != 0], {"Introduce"[n], "Decide"}]
```

<!-- => Proof complete -->

---

`"Classical"` proves Peirce's law, which needs the excluded middle:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[Implies[Implies[a, b], a], a]], {
    "Introduce"[a, b, h]
}]
```

<!-- => Proof, 1 goal: a ∶ Prop, b ∶ Prop, h ∶ (a ⇒ b) ⇒ a ⊢ a -->

A truth table of `a` and `b` under the hypothesis `h`:

```wl
TypeTheoryTactic["Classical"][proof]
```

<!-- => Proof complete -->

---

`"Classical"` uses the hypotheses: from `a ∨ b` and `¬a` follows `b`:

```wl
TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[Or[a, b], Implies[Not[a], b]]], {
    "Introduce"[a, b, h, na],
    "Classical"
}]
```

<!-- => Proof complete -->

---

`"FindInstance"` asks Wolfram for natural numbers with a property:

```wl
proof = TypeTheoryProof[Exists[{x, y}, And[x^2 + y^2 == 25, 0 < x, x < y]], {"FindInstance"}]
```

<!-- => Proof complete -->

The proof holds the witnesses; the decision that the kernel computes for them is the instance argument of `"decideSoundness"`, which a term does not show:

```wl
proof["Term"]
```

<!-- => existsIntroduction[3, existsIntroduction[4, decideSoundness[equalityReflexivity[true]]]] -->

---

`"FindEquationalProof"` derives the right identity of a group from its left identity and left inverses:

```wl
TypeTheoryProof[ForAll[
    {Typed[G, TypeUniverse[1]], Typed[op, TypeSpecifier[{G, G} -> G]], Typed[e, G], Typed[inv, TypeSpecifier[{G} -> G]]},
    Implies[ForAll[{a, b, c}, op[op[a, b], c] == op[a, op[b, c]]],
        Implies[ForAll[{a}, op[e, a] == a],
            Implies[ForAll[{a}, op[inv[a], a] == e], ForAll[{x}, op[x, e] == x]]]]
], {
    "Introduce"[G, op, e, inv, associativity, identity, inverse, x],
    "FindEquationalProof"
}]
```

<!-- => Proof complete -->

---

An idempotent function applied three times is applied once:

```wl
proof = TypeTheoryProof[ForAll[{Typed[S, TypeUniverse[1]], Typed[f, TypeSpecifier[{S} -> S]]},
    Implies[ForAll[{a}, f[f[a]] == f[a]], ForAll[{x}, f[f[f[x]]] == f[x]]]
], {"Introduce"[S, f, idempotent, x]}]
```

<!-- => Proof, 1 goal: S ∶ Type, f ∶ S → S, idempotent ∶ ∀_a∶S f[f[a]] == f[a], x ∶ S ⊢ f[f[f[x]]] == f[x] -->

The proof that Wolfram finds, replayed with the hypothesis:

```wl
TypeTheoryTactic["FindEquationalProof"][proof]
```

<!-- => Proof complete -->

### Holes

`"Hole"` closes a goal with a proof left to give:

```wl
TypeTheoryProof[ForAll[{m, n}, m + n == n + m], {"Introduce"[m, n], "Hole"}]
```

<!-- => Proof complete with 1 hole -->

---

A hole with an annotation for one part of a conjunction:

```wl
proof = TypeTheoryProof[ForAll[{m, n}, m + n == n + m && m n == n m], {
    "Introduce"[m, n],
    "Constructor",
    "Hole"["addition commutes"]
}]
```

<!-- => Proof, 1 goal, 1 hole: m ∶ ℕ, n ∶ ℕ ⊢ m n == n m -->

The other part is proved:

```wl
proof = TypeTheoryTactic["Ring"][proof]
```

<!-- => Proof complete with 1 hole -->

The theorem declared with the proof keeps the hole, a constant before it:

```wl
Take[Keys[TypeTheoryEnvironment[TypeTheoryTheorem[BothCommute, proof]]], -2]
```

<!-- => {TypeTheoryHole[BothCommute, 1], BothCommute} -->

## Properties and Relations

A tactic written as its name applied to its arguments is the tactic with the name and the arguments:

```wl
TypeTheoryTactic["Introduce"[n, k]]
```

<!-- => TypeTheoryTactic["Introduce", n, k] -->

---

`"Ring"` uses no hypothesis, so it does not prove what `"PolynomialReduce"` proves from them:

```wl
TypeTheoryProof[ForAll[{x, y}, Implies[x + y == 10, Implies[x == 2 y + 1, x y == 21]]], {
    "Introduce"[x, y, h, k],
    "Ring"
}]
```

<!-- => Failure["NotRingEquation", ...] -->

---

`"LinearArithmetic"` finds no combination for `n n <= m m`, which `"NonlinearArithmetic"` proves:

```wl
TypeTheoryProof[ForAll[{n, m}, Implies[n <= m, n n <= m m]], {
    "Introduce"[n, m, h],
    "LinearArithmetic"
}]
```

<!-- => Failure["NoLinearCombination", ...] -->

---

`"Classical"` proves De Morgan's law, which holds for propositions with no decision:

```wl
TypeTheoryProof[ForAll[{a, b}, Implies[Not[And[a, b]], Or[Not[a], Not[b]]]], {
    "Introduce"[a, b, h],
    "Classical"
}]
```

<!-- => Proof complete -->

`"Decide"` needs a decision, and the prelude has none for a proposition variable:

```wl
TypeTheoryProof[ForAll[{a, b}, Implies[Not[And[a, b]], Or[Not[a], Not[b]]]], {
    "Introduce"[a, b, h],
    "Decide"
}]
```

<!-- => Failure["NotDecidable", ...] -->

---

`"Reflexivity"` proves equations only:

```wl
TypeTheoryProof[3 != 4, {"Reflexivity"}]
```

<!-- => Failure["EquationExpected", ...] -->

`"Decide"` proves any statement whose decision computes:

```wl
TypeTheoryProof[3 != 4, {"Decide"}]
```

<!-- => Proof complete -->

## Possible Issues

`"Reflexivity"` needs the sides to be equal by computation; `0 + n` is not `n` until induction:

```wl
TypeTheoryProof[ForAll[{n}, 0 + n == n], {
    "Introduce"[n],
    "Reflexivity"
}]
```

<!-- => Failure["NotReflexive", ...] -->

---

`"Decide"` needs a decision that computes. With a variable it computes only where the decision does not depend on the variable, and the decision of `n <= n + 1` depends on `n`:

```wl
TypeTheoryProof[ForAll[{n}, n <= n + 1], {"Introduce"[n], "Decide"}]
```

<!-- => Failure["NotDecided", ...] -->

---

A definition by recursion does not unfold on a variable, where it does not compute; `"Induction"` on the variable comes first:

```wl
TypeTheoryProof[ForAll[{Typed[l, {Naturals}]}, Join[l, {}] == l], {"Introduce"[l], "RewriteRepeated"[Join]}]
```

<!-- => Failure["NoProgress", ...] -->

---

`"Induction"` on a proof of an inductive family needs its indices to be variables:

```wl
TypeTheoryProof[ForAll[{a, b}, Implies[a <= b + 1, a <= b + 2]], {
    "Introduce"[a, b, h],
    "Induction"[h]
}]
```

<!-- => Failure["IndexNotVariable", ...] -->

---

`"Constructor"` applies the first constructor that fits the goal's type, so on a disjunction it takes the left side, even when the left side is false:

```wl
TypeTheoryProof[Or[1 == 2, 2 == 2], {"Constructor"}]
```

<!-- => Proof, 1 goal: ⊢ 1 == 2 -->

`"Apply"` chooses the side:

```wl
TypeTheoryProof[Or[1 == 2, 2 == 2], {"Apply"["orIntroductionRight"], "Reflexivity"}]
```

<!-- => Proof complete -->

---

`"Ring"` proves only what holds in every commutative semiring:

```wl
TypeTheoryProof[ForAll[{a, b}, (a + b)^2 == a^2 + b^2], {"Introduce"[a, b], "Ring"}]
```

<!-- => Failure["NotRingEquation", ...] -->

---

The subtraction of natural numbers stops at 0, so it is no operation of a semiring, and `"Ring"` does not prove `(a + 1) - 1 == a`:

```wl
TypeTheoryProof[ForAll[{a}, (a + 1) - 1 == a], {"Introduce"[a], "Ring"}]
```

<!-- => Failure["NotRingEquation", ...] -->

---

`"FindInstance"` needs a statement of the variables it binds alone; a hypothesis in it is not translated:

```wl
TypeTheoryProof[ForAll[{m}, Exists[{n}, n == m + 1]], {"Introduce"[m], "FindInstance"}]
```

<!-- => Failure["NotTranslatable", ...] -->

---

`"LinearArithmetic"` proves only what follows from the hypotheses:

```wl
TypeTheoryProof[ForAll[{x, y}, Implies[x <= y, y <= x]], {"Introduce"[x, y, h], "LinearArithmetic"}]
```

<!-- => Failure["NoLinearCombination", ...] -->

---

`"NonlinearArithmetic"` multiplies once, so it proves `n n <= m m` but not `n n n <= m m m`:

```wl
TypeTheoryProof[ForAll[{n, m}, Implies[n <= m, n n n <= m m m]], {"Introduce"[n, m, h], "NonlinearArithmetic"}]
```

<!-- => Failure["NoLinearCombination", ...] -->

---

The proofs of `"LinearArithmetic"` compute with the literals of the statement, and with a few hundred the computation goes too deep for the kernel, which rejects the proof:

```wl
TypeTheoryProof[ForAll[{x, y}, Implies[2 x + 3 y <= 600, Implies[200 <= x, y <= 66]]], {
    "Introduce"[x, y, h, k],
    "LinearArithmetic"
}]
```

<!-- => Failure["ProofRejected", ...] -->

The products of `"NonlinearArithmetic"` reach that depth sooner; `n <= 7` gives `n n <= 49`, but `n <= 8` does not give `n n <= 64`:

```wl
TypeTheoryProof[ForAll[{n}, Implies[n <= 8, n n <= 64]], {"Introduce"[n, h], "NonlinearArithmetic"}]
```

<!-- => Failure["ProofRejected", ...] -->

---

`"SumOfSquares"` proves only what a sum of squares shows; `x^2 <= 2` is false for `x = 2`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x^2 <= 2], "Integers", {"Introduce"[x], "SumOfSquares"}]
```

<!-- => Failure["NoSumOfSquares", ...] -->

---

`"SumOfSquares"` needs the integers' environment, even for an inequality of natural numbers:

```wl
TypeTheoryProof[ForAll[{a, b}, 2 a b <= a^2 + b^2], {"Introduce"[a, b], "SumOfSquares"}]
```

<!-- => Failure["SumOfSquaresUnavailable", ...] -->

---

A tactic takes the arguments listed for it, and no others:

```wl
TypeTheoryProof[ForAll[{n}, n + 0 == n], {"Introduce"[n], "Reflexivity"[n]}]
```

<!-- => Failure["UnknownTactic", ...] -->

## Neat Examples

Ramanujan's taxicab number 1729 is a sum of two cubes:

```wl
proof = TypeTheoryProof[Exists[{a, b}, And[a^3 + b^3 == 1729, a < b]], {"FindInstance"}]
```

<!-- => Proof complete -->

The cubes of 1 and 12:

```wl
proof["Term"]
```

<!-- => existsIntroduction[1, existsIntroduction[12, decideSoundness[equalityReflexivity[true]]]] -->

---

It is a sum of two cubes in a second way, with both numbers larger than 1:

```wl
proof = TypeTheoryProof[Exists[{a, b}, And[a^3 + b^3 == 1729, 1 < a, a < b]], {"FindInstance"}]
```

<!-- => Proof complete -->

The cubes of 9 and 10:

```wl
proof["Term"]
```

<!-- => existsIntroduction[9, existsIntroduction[10, decideSoundness[equalityReflexivity[true]]]] -->
