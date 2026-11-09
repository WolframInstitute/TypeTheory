---
Template: Symbol
Name: TypeTheoryProof
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryProof
Keywords: [proof, goals, tactics, interactive proof, proof state, induction, cases, proof term, statement, hypotheses, universe parameters]
SeeAlso: [TypeTheoryTactic, TypeTheoryTheorem, TypeTheoryHole, TypeTheoryProofTree, TypeTheoryEnvironment, TypeTheoryTerm, TypeTheoryFormalize]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ProgramsAndProofs]
---

## Usage

<code>[TypeTheoryProof]()[*statement*]</code> starts a proof of *statement* in the default environment, [$TypeTheoryEnvironment](), with *statement* itself as its one goal.

<code>[TypeTheoryProof]()[*statement*, *env*]</code> starts it in the [TypeTheoryEnvironment]() *env*, or in the library environment that the name *env* stands for, such as `"Integers"`.

<code>[TypeTheoryProof]()[[TypeTheoryTerm]()[*statement*, *env*]]</code> starts a proof of the term *statement* in its own environment *env*.

<code>[TypeTheoryProof]()[*statement*, {*tactic1*, *tactic2*, ...}]</code> and <code>[TypeTheoryProof]()[*statement*, *env*, {*tactic1*, ...}]</code> apply the [TypeTheoryTactic]() tactics in turn; a tactic in the list may be written `"name"` or `"name"[arguments...]`.

## Details & Options

- A proof holds a partial proof term with holes, its goals. A [TypeTheoryTactic]() works on the first goal and fills it with a term that may have new holes, the goals it leaves. A proof with no goals left is finished.
- The arguments come in the order statement, environment, list of tactics, options. Any other order gives a [Failure]() tagged `"ProofArguments"`.
- A statement without an environment is in the default environment, the prelude unless [SetTypeTheoryEnvironment]() set another. The prelude has the expressions of the Wolfram Language, so a statement about an expression or [Replace]() with a rule names no environment. A statement about the integers or the rationals names their environment.
- The statement is held. It may hold the patterns of a rule, as `Replace[f[5], f[x_] :> x] == 5` does, but a statement that is a pattern or an [Association]() starts no proof: <code>[TypeTheoryProof]()[_[Association]()]</code> stays as it is.
- A list of tactics written out is held as well: <code>{"Introduce"[n], "Reflexivity"}</code> stands for <code>{[TypeTheoryTactic]()["Introduce", n], [TypeTheoryTactic]()["Reflexivity"]}</code>, whose arguments are not evaluated. An environment, options and a list of tactics kept in a symbol evaluate. A statement kept in a symbol is used only when its value is a [TypeTheoryTerm]().
- The tactics run in turn. The first that does not apply gives its [Failure](), which says why, and the proof stops there.
- In a notebook a proof shows each open goal as its hypotheses over the goal, with the name of the constructor on goals that come from induction, as `case zero` or `case Prepend`. A finished proof shows `Proof complete`, with the number of holes the tactic `"Hole"` left. The display stands for the proof itself: copied, or evaluated again, it gives the [TypeTheoryProof]().
- <code>*proof*["Goals"]</code> gives the open goals as <code>[TypeTheoryTerm]()[[RightTee]()[{[Typed]()[*x*, *type*], ...}, *goal*], *env*]</code>, each a statement in its own right, its hypotheses quantified. <code>*proof*["Term"]</code> gives the proof term, <code>*proof*["Statement"]</code> the statement and <code>*proof*["Environment"]</code> the environment.
- Nothing a tactic does is trusted: <code>[TypeTheoryTheorem]()[*name*, *proof*]</code> has the kernel check the finished proof term before it declares the theorem. [TypeTheoryProofTree]() gives the natural-deduction derivation of a finished proof of propositional logic.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear, and makes each level that nothing in the statement decides one more, `"u_1"`, `"u_2"`, ….

## Basic Examples

Start a proof; its one goal is the statement:

```wl
proof = TypeTheoryProof[ForAll[{n}, 0 + n == n]]
```

<!-- => Proof, 1 goal: ⊢ ∀_n∶ℕ 0 + n == n -->

A tactic applied to a proof gives the next proof. Introduce `n` and split it by induction, a goal for each constructor of the natural numbers:

```wl
proof = TypeTheoryTactic["Induction", n][TypeTheoryTactic["Introduce", n][proof]]
```

<!-- => Proof, 2 goals: case zero ⊢ 0 + 0 == 0; case successor ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

The case of zero holds by computation:

```wl
proof = TypeTheoryTactic["Reflexivity"][proof]
```

<!-- => Proof, 1 goal: case successor ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

Introduce the number `k` and the induction hypothesis `ih`:

```wl
proof = TypeTheoryTactic["Introduce", k, ih][proof]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 0 + k == k ⊢ 0 + (k + 1) == k + 1 -->

Adding 1 to both sides of `ih` finishes the proof:

```wl
proof = TypeTheoryTactic["Exact", "equalityCongruence"["successor", ih]][proof]
```

<!-- => Proof complete -->

---

The same proof as a list of tactics, each its name applied to its arguments:

```wl
TypeTheoryProof[ForAll[{n}, 0 + n == n], {
    "Introduce"[n],
    "Induction"[n],
    "Reflexivity",
    "Introduce"[k, ih],
    "Exact"["equalityCongruence"["successor", ih]]
}]
```

<!-- => Proof complete -->

---

A proof about the integers, in the environment named `"Integers"`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y) (x + y) == x^2 - y^2], "Integers", {"Introduce"[x, y], "Ring"}]
```

<!-- => Proof complete -->

---

A finished proof:

```wl
proof = TypeTheoryProof[ForAll[{n}, n + 0 == n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

[TypeTheoryTheorem]() declares it, once the kernel has checked its term:

```wl
proved = TypeTheoryEnvironment[TypeTheoryTheorem[ZeroRightIdentity, proof]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The theorem states what the proof proved:

```wl
proved[ZeroRightIdentity]
```

<!-- => theorem ZeroRightIdentity : ∀_n∶ℕ n + 0 == n -->

## Scope

### Statements and Environments

A statement given as a [TypeTheoryTerm]() is proved in the term's environment:

```wl
TypeTheoryProof[TypeTheoryTerm[ForAll[{Typed[x, Integers]}, x - x == 0], "Integers"], {"Introduce"[x], "Ring"}]
```

<!-- => Proof complete -->

---

A statement kept in a symbol whose value is a [TypeTheoryTerm]():

```wl
statement = TypeTheoryTerm[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], "Integers"]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x y == y x -->

The proof is in the integers, the term's environment:

```wl
TypeTheoryProof[statement, {"Introduce"[x, y], "Ring"}]
```

<!-- => Proof complete -->

---

A statement about rewriting holds the patterns of a rule. [Replace]() with `f[x_] :> x` takes `f[5]` to 5 by computation:

```wl
TypeTheoryProof[Replace[f[5], f[x_] :> x] == 5, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

The rule takes `g[e]` to `e` for every expression `e`, a statement with a quantifier:

```wl
TypeTheoryProof[ForAll[{e}, Replace[g[e], g[x_] :> x] == e], {"Introduce"[e], "Reflexivity"}]
```

<!-- => Proof complete -->

---

A statement about a quoted expression, by computation: the head of `f[x]` is `f`:

```wl
TypeTheoryProof[Head[f[x]] == f, {"Reflexivity"}]
```

<!-- => Proof complete -->

### Goals and Cases

Induction on a list leaves a goal for the empty list and one for a list with a first element, each named by its constructor:

```wl
TypeTheoryProof[ForAll[{Typed[l, {Naturals}]}, Join[l, {}] == l], {"Introduce"[l], "Induction"[l]}]
```

<!-- => Proof, 2 goals: case {} ⊢ Join[{}, {}] == {}; case Prepend ⊢ ∀_x∶ℕ ∀_l∶{ℕ} Join[l, {}] == l ⇒ Join[Prepend • x • l, {}] == Prepend • x • l -->

---

Applying `"andIntroduction"` leaves a goal for each side of the conjunction, each under the hypotheses:

```wl
proof = TypeTheoryProof[ForAll[{a, b}, Implies[a, Implies[b, And[a, b]]]], {
    "Introduce"[a, b, ha, hb],
    "Apply"["andIntroduction"]
}]
```

<!-- => Proof, 2 goals: a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ a; a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ b -->

The goals as statements:

```wl
proof["Goals"]
```

<!-- => {a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ a, a ∶ Prop, b ∶ Prop, ha ∶ a, hb ∶ b ⊢ b} -->

---

A goal is a statement in its own right. The goals of a proof by induction:

```wl
goals = TypeTheoryProof[ForAll[{n}, 0 + n == n], {"Introduce"[n], "Induction"[n]}]["Goals"]
```

<!-- => {⊢ 0 + 0 == 0, ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1} -->

The case of the successor:

```wl
successorCase = Last[goals]
```

<!-- => ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

A proof of it alone:

```wl
TypeTheoryProof[successorCase, {"Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]}]
```

<!-- => Proof complete -->

### Tactics

A list of tactics kept in a symbol evaluates, so one list serves several proofs. `"Introduce"` without names takes the names of the binders:

```wl
steps = {"Introduce", "Reflexivity"};
TypeTheoryProof[ForAll[{n}, n - 0 == n], steps]
```

<!-- => Proof complete -->

---

The same list proves that joining the empty list to `l` gives `l`:

```wl
steps = {"Introduce", "Reflexivity"};
TypeTheoryProof[ForAll[{Typed[l, {Naturals}]}, Join[{}, l] == l], steps]
```

<!-- => Proof complete -->

### Parts of a Proof

A finished proof by induction:

```wl
proof = TypeTheoryProof[ForAll[{n}, 0 + n == n], {
    "Introduce"[n], "Induction"[n], "Reflexivity", "Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]
}]
```

<!-- => Proof complete -->

The proof term the tactics built, a function by the recursor of the natural numbers:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 0 + n1 == n1, equalityReflexivity[0 + 0], (k ∶ ℕ) (ih ∶ 0 + k == k) ↦ equalityCongruence[successor, ih], n] -->

The statement it proves:

```wl
proof["Statement"]
```

<!-- => ∀_n∶ℕ 0 + n == n -->

## Options

### UniverseParameters

A statement about the elements of any type, its universe named `v`:

```wl
proof = TypeTheoryProof[ForAll[{TypedImplicit[A, TypeUniverse[v]], Typed[x, A]}, x == x], {"Introduce"[A, x], "Reflexivity"}, "UniverseParameters" -> {v}]
```

<!-- => Proof complete -->

The theorem it proves has the universe parameter `v`:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[SelfEquality, proof]][SelfEquality]
```

<!-- => theorem SelfEquality : ∀_{A∶Sort v} ∀_x∶A x == x -->

---

With the default [Automatic](), a type whose universe nothing decides gets the parameter `"u_1"`:

```wl
proof = TypeTheoryProof[ForAll[{A, Typed[x, A]}, x == x], {"Introduce"[A, x], "Reflexivity"}]
```

<!-- => Proof complete -->

The theorem it proves:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[SelfEquality, proof]][SelfEquality]
```

<!-- => theorem SelfEquality : ∀_A∶Sort u_1 ∀_x∶A x == x -->

## Applications

### Gauss's Formula

The triangular numbers 1 + 2 + ... + n, defined by recursion in the Wolfram Language and read by [TypeTheoryFormalize]() as a definition of the type theory:

```wl
triangular[0] = 0;
triangular[n_Integer] := n + triangular[n - 1];
programs = TypeTheoryEnvironment[TypeTheoryFormalize[triangular]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Twice the n-th triangular number is n (n + 1). By induction, the case of zero computes, and in the case of `k + 1` the definition unfolds once, leaving algebra with the induction hypothesis:

```wl
proof = TypeTheoryProof[ForAll[{n}, 2 triangular[n] == n (n + 1)], programs, {
    "Introduce"[n], "Induction"[n], "RewriteRepeated"[triangular],
    "Introduce"[k, ih], "RewriteRepeated"[triangular]
}]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ 2 (k + 1 + triangular[k]) == (k + 1) (k + 1 + 1) -->

`"PolynomialReduce"` finds how the hypothesis gives the goal:

```wl
TypeTheoryTactic["PolynomialReduce"][proof]
```

<!-- => Proof complete -->

### Summing in Parts

The sum of a list, by recursion on the list:

```wl
total[{}] = 0;
total[{x_, rest___}] := x + total[{rest}];
programs = TypeTheoryEnvironment[TypeTheoryFormalize[total]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The sum of two lists joined is the sum of their sums. After induction on the first list, the case of a list with a first element `x`:

```wl
proof = TypeTheoryProof[ForAll[{a, b}, total[Join[a, b]] == total[a] + total[b]], programs, {
    "Introduce"[a, b], "Induction"[a], "RewriteRepeated"[total, Join], "Ring",
    "Introduce"[x, rest, ih]
}]
```

<!-- => Proof, 1 goal: b ∶ {ℕ}, x ∶ ℕ, rest ∶ {ℕ}, ih ∶ total[Join[rest, b]] == total[rest] + total[b] ⊢ total[Join[Prepend • x • rest, b]] == total[Prepend • x • rest] + total[b] -->

`"RewriteRepeated"` unfolds [Join]() inside `total` first, so that `total[Join[rest, b]]` appears and the induction hypothesis rewrites it:

```wl
proof = TypeTheoryTactic["RewriteRepeated", total, Join, ih][proof]
```

<!-- => Proof, 1 goal: b ∶ {ℕ}, x ∶ ℕ, rest ∶ {ℕ}, ih ∶ total[Join[rest, b]] == total[rest] + total[b] ⊢ x + (total[rest] + total[b]) == x + total[rest] + total[b] -->

What is left is the associativity of addition:

```wl
TypeTheoryTactic["Ring"][proof]
```

<!-- => Proof complete -->

## Properties and Relations

[TypeTheoryProofTree]() gives the natural-deduction derivation of a finished proof of propositional logic:

```wl
proof = TypeTheoryProof[ForAll[{a, b}, Implies[a, Implies[b, And[a, b]]]], {
    "Introduce"[a, b, ha, hb], "Apply"["andIntroduction"], "Assumption", "Assumption"
}]
```

<!-- => Proof complete -->

A conjunction introduced, then two implications:

```wl
TypeTheoryProofTree[proof]
```

<!-- => (((a   b) / (a ∧ b) ∧I) / (b ⇒ (a ∧ b)) →I) / (a ⇒ b ⇒ (a ∧ b)) →I -->

---

A list of tactics does what the tactics do applied one at a time: the two proofs have the same term:

```wl
TypeTheoryProof[ForAll[{n}, n + 0 == n], {"Introduce"[n], "Reflexivity"}]["Term"] ===
    TypeTheoryTactic["Reflexivity"][TypeTheoryTactic["Introduce", n][TypeTheoryProof[ForAll[{n}, n + 0 == n]]]]["Term"]
```

<!-- => True -->

---

A finished proof:

```wl
proof = TypeTheoryProof[ForAll[{n}, n + 0 == n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

The kernel checks its term against its statement, as [TypeTheoryTheorem]() does:

```wl
TypeTheoryCheck[proof["Term"], proof["Statement"]]
```

<!-- => Success["TypeChecked", ...] -->

A finished proof stands for its term, whose type is equal to the statement by computation, though not the same:

```wl
TypeTheoryType[proof]
```

<!-- => ∀_n∶ℕ n + 0 == n + 0 -->

The display of a proof is the proof: evaluated again, it gives the same proof:

```wl
ToExpression[ToBoxes[proof]] === proof
```

<!-- => True -->

## Possible Issues

An unfinished proof cannot be declared:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Absurd, TypeTheoryProof[False]]]
```

<!-- => Failure["ProofIncomplete", ...] -->

---

A tactic that does not apply ends the proof with its [Failure](), which says why; `0 + n` is not `n` by computation:

```wl
TypeTheoryProof[ForAll[{n}, 0 + n == n], {"Introduce"[n], "Reflexivity", "Induction"[n]}]
```

<!-- => Failure["NotReflexive", ...] -->

---

A tactic applied to a finished proof has no goal to work on:

```wl
TypeTheoryTactic["Reflexivity"][TypeTheoryProof[2 + 2 == 4, {"Reflexivity"}]]
```

<!-- => Failure["NoGoals", ...] -->

---

The environment comes before the tactics:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x - x == 0], {"Introduce"[x], "Ring"}, "Integers"]
```

<!-- => Failure["ProofArguments", ...] -->

---

The integers are not in the prelude, so a statement about them names their environment:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x - x == 0], {"Introduce"[x], "Ring"}]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The statement is held, so a symbol whose value is a plain expression stands for itself, not for the expression:

```wl
plain = ForAll[{n}, n + 0 == n];
TypeTheoryProof[plain, {"Introduce"[n], "Reflexivity"}]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A pattern is not a statement, so it starts no proof:

```wl
TypeTheoryProof[_Association]
```

<!-- => TypeTheoryProof[_Association] -->

---

[TypeTheoryProofTree]() knows the rules of natural deduction, not the recursor of [And]() that `"Cases"` uses to take a conjunction apart:

```wl
TypeTheoryProofTree[TypeTheoryProof[ForAll[{a, b}, Implies[a && b, b && a]], {
    "Introduce"[a, b, h], "Cases"[h], "Introduce"[x, y], "Constructor", "Exact"[y], "Exact"[x]
}]]
```

<!-- => Missing["Untranslatable"] -->
