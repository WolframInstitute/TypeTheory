---
Template: Symbol
Name: InductiveRecursor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/InductiveRecursor
Keywords: [recursor, induction, recursion, eliminator, inductive type, motive, minor premise, case analysis, large elimination, iota reduction, nested inductive type]
SeeAlso: [TypeTheoryInductiveType, TypeTheoryTactic, WeakHeadNormalForm, NormalForm, TypeTheoryDefinition, Naturals]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, ProgramsAndProofs]
---

## Usage

<code>[InductiveRecursor]()[*type*]</code> is the recursor of the inductive type *type*, generated when the type is declared.

<code>[InductiveRecursor]()[*type*, *k*]</code> is the recursor on the *k*th container that *type*, or a type declared with it, is nested in.

## Details & Options

- Its arguments are the type's parameters (implicit), a motive, one minor premise per constructor, the indices (implicit) and the term to eliminate. For types declared together, or nested in containers, there is a motive for each type and container, and a minor premise for each of their constructors, as in Lean.
- The motive is a function from the term eliminated to the type of the result, which may depend on the term: a type such as [Naturals]() for a definition by recursion, a proposition for a proof by induction.
- A minor premise takes the constructor's fields and a result for each recursive field: the recursive call, or the induction hypothesis.
- Applied to a constructor, the recursor reduces to its minor premise, and on a literal of the natural numbers to the case of its predecessor; at a variable it does not reduce, so a fact about a definition by recursion at a variable is proved by induction.
- The motive may go into any universe, except for a proposition with more than one constructor, as [Or](), or with a constructor that holds data, as [Exists]() holds its witness: those eliminate only into Prop, so no function computes data from their proofs, as in Lean. [And](), [Equal]() and [False]() eliminate into any universe.
- The recursor is how definitions recurse and how proofs go by induction: the tactics `"Induction"` and `"Cases"` build an application of it.
- The kernel reduces a recursion on a literal *n* one step at a time, *n* steps deep, and near a thousand nested steps it reports that the computation goes deeper than it can recurse, a [Failure]() tagged `"RecursionLimit"`; the arithmetic that [TypeTheoryNaturalNumbers]() registers, [Plus]() and the others, computes on literals with Wolfram integers instead. The kernel does not share results either, so a step that uses the result before it twice, as a Fibonacci step does, computes it twice, and the time grows exponentially with *n*.
- <code>[InductiveRecursor]()[*type*]</code> shows as *type*_rec, and <code>[InductiveRecursor]()[*type*, *k*]</code> as *type*_rec_*k*, as Lean writes `type.rec`.

## Basic Examples

The recursor of the natural numbers:

```wl
TypeTheoryType[InductiveRecursor[Naturals]]
```

<!-- => ∀_m∶ℕ → Sort u m[0] → (∀_n∶ℕ m[n] → m[n + 1]) → ∀_t∶ℕ m[t] -->

---

Recursion: double a natural number, adding 2 for each successor:

```wl
double = TypeTheoryTerm[Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][
    Function[{Typed[t, Naturals]}, Naturals],
    0,
    Function[{Typed[k, Naturals], Typed[r, Naturals]}, r + 2],
    n
]]]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 2, n] -->

Applied to 5, it computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[double[5]]]
```

<!-- => 10 -->

---

The recursor of the Booleans is a conditional, with the case of `"false"` first; `3 <= 2` decides to `"false"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Booleans][Typed[t, Booleans] |-> Naturals, 10, 20, Decide[3 <= 2]]]]
```

<!-- => 10 -->

## Scope

### Recursion

The factorial of 5, multiplying by `k + 1` at each successor `k + 1`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Naturals][Typed[t, Naturals] |-> Naturals, 1, {Typed[k, Naturals], Typed[r, Naturals]} |-> r * (k + 1), 5]]]
```

<!-- => 120 -->

---

The sum of a list, with the recursor of [List](), whose minor premise for a list with a first element takes the element, the rest and the sum of the rest:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[List][Typed[t, {Naturals}] |-> Naturals, 0, {Typed[x, Naturals], Typed[rest, {Naturals}], Typed[r, Naturals]} |-> x + r, Typed[{1, 2, 3}, {Naturals}]]]]
```

<!-- => 6 -->

---

The recursor of [CartesianProductType]() applies a function of two arguments to the fields of a pair:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[CartesianProductType][Typed[t, CartesianProductType[Naturals, Naturals]] |-> Naturals, {Typed[x, Naturals], Typed[y, Naturals]} |-> x * y, "pair"[6, 7]]]]
```

<!-- => 42 -->

---

A motive into a universe makes a type by cases, here the natural numbers for `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Booleans][Typed[t, Booleans] |-> TypeUniverse[1], Booleans, Naturals, "true"]]]
```

<!-- => ℕ -->

### Induction

A proof by induction, written with the recursor: the motive is the statement, the minor premise for 0 proves it at 0, and the one for successors takes the induction hypothesis `ih`:

```wl
TypeTheoryType[Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][
    Typed[k, Naturals] |-> 0 + k == k,
    "equalityReflexivity"[0],
    {Typed[k, Naturals], Typed[ih, 0 + k == k]} |-> "equalityCongruence"["successor", ih],
    n
]]]
```

<!-- => ∀_n∶ℕ 0 + n == n -->

---

Case analysis on a disjunction, with one minor premise for each side:

```wl
TypeTheoryType[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, p || q]},
    InductiveRecursor[Or][
        Function[{Typed[t, p || q]}, q || p],
        Function[{Typed[x, p]}, "orIntroductionRight"[x]],
        Function[{Typed[y, q]}, "orIntroductionLeft"[y]],
        h
    ]
]]
```

<!-- => ∀_p∶Prop ∀_q∶Prop (p ∨ q) ⇒ (q ∨ p) -->

---

Induction on a proof of an inequality, whose recursor takes a motive of the index `j` as well: from `m <= n`, `m <= n + 1`:

```wl
TypeTheoryType[Function[{Typed[m, Naturals], Typed[n, Naturals], Typed[h, m <= n]},
    InductiveRecursor[LessEqual][
        {Typed[j, Naturals], Typed[t, m <= j]} |-> m <= j + 1,
        "lessEqualStep"["lessEqualReflexivity"],
        {Typed[j, Naturals], Typed[t, m <= j], Typed[ih, m <= j + 1]} |-> "lessEqualStep"[ih],
        h
    ]
]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m <= n ⇒ m <= n + 1 -->

---

The recursor of [Equal]() substitutes equals: a bound on `m` holds for `n` too:

```wl
TypeTheoryType[{Typed[m, Naturals], Typed[n, Naturals], Typed[e, m == n], Typed[h, m <= 5]} |-> InductiveRecursor[Equal][{Typed[x, Naturals], Typed[t, m == x]} |-> x <= 5, h, e]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m == n ⇒ m <= 5 ⇒ n <= 5 -->

---

[False]() has no constructor, so its recursor has no minor premise, and proves anything:

```wl
TypeTheoryType[Typed[h, False] |-> InductiveRecursor[False][Typed[t, False] |-> 2 + 2 == 5, h]]
```

<!-- => False ⇒ 2 + 2 == 5 -->

### Nested Types

Rose trees, each with a list of rose trees as its children:

```wl
roses = TypeTheoryEnvironment[{TypeTheoryInductiveType[Rose, TypeUniverse[1], {
    RoseNode -> ForAll[{Typed[label, Naturals], Typed[children, {Rose}]}, Rose]
}]}]
```

<!-- => TypeTheoryEnvironment summary box: 173 constants -->

A tree nested in a list of trees has a recursor on the list as well, with the same motives and minor premises:

```wl
TypeTheoryType[InductiveRecursor[Rose, 1], roses]
```

<!-- => ∀_m1∶Rose → Sort u ∀_m2∶{Rose} → Sort u (∀_label∶ℕ ∀_children∶{Rose} m2[children] → m1[RoseNode[label, children]]) → m2[{}] → (∀_x∶Rose ∀_l∶{Rose} m1[x] → m2[l] → m2[Prepend[l, x]]) → ∀_t∶{Rose} m2[t] -->

## Applications

The sum 1 + 2 + ... + *n*, by recursion:

```wl
sums = TypeTheoryEnvironment[{TypeTheoryDefinition[SumTo, Typed[
    Typed[n, Naturals] |-> InductiveRecursor[Naturals][Typed[t, Naturals] |-> Naturals, 0, {Typed[k, Naturals], Typed[r, Naturals]} |-> r + (k + 1), n],
    TypeSpecifier[{Naturals} -> Naturals]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

It computes in the kernel:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SumTo[100], sums]]
```

<!-- => 5050 -->

Gauss's formula, by induction: `"Simplify"` unfolds `SumTo` at the successor `k + 1`, the recursor's step:

```wl
gauss = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 2 * SumTo[n] == n * (n + 1)], sums, {
    "Introduce"[n],
    "Induction"[n],
    "Reflexivity",
    "Introduce"[k, ih],
    "Simplify"[{SumTo}]
}]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 SumTo[k] == k (k + 1) ⊢ 2 (SumTo[k] + (k + 1)) == (k + 1) (k + 1 + 1) -->

The induction hypothesis finishes it, as a polynomial combination:

```wl
TypeTheoryTactic["PolynomialReduce"][gauss]
```

<!-- => Proof complete -->

## Properties and Relations

`"Induction"` builds the recursor: the proof term of a proof by induction applies it:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {
    "Introduce"[n],
    "Induction"[n],
    "Reflexivity",
    "Introduce"[k, ih],
    "Exact"["equalityCongruence"["successor", ih]]
}]
```

<!-- => Proof complete -->

Its term:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 0 + n1 == n1, equalityReflexivity[0 + 0], (k ∶ ℕ) (ih ∶ 0 + k == k) ↦ equalityCongruence[successor, ih], n] -->

---

Doubling, by recursion:

```wl
double = TypeTheoryTerm[Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][Typed[t, Naturals] |-> Naturals, 0, {Typed[k, Naturals], Typed[r, Naturals]} |-> r + 2, n]]]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 2, n] -->

At a successor of a variable the recursor takes a step, so the equation of the step holds by computation:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, double[n + 1] == double[n] + 2], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

---

The recursor of [Or]() has a motive into Prop only, so a proof of a disjunction is taken apart only to prove a proposition:

```wl
TypeTheoryType[InductiveRecursor[Or]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} ∀_m∶(a ∨ b) → Prop (∀_p∶a m[orIntroductionLeft[p]]) ⇒ (∀_q∶b m[orIntroductionRight[q]]) ⇒ ∀_t∶a ∨ b m[t] -->

---

The recursor of [And]() has a motive into any universe, `Sort u`, since a conjunction has one constructor whose fields are proofs:

```wl
TypeTheoryType[InductiveRecursor[And]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} ∀_m∶(a ∧ b) → Sort u (∀_p∶a ∀_q∶b m[andIntroduction[p, q]]) → ∀_t∶a ∧ b m[t] -->

## Possible Issues

Doubling, by recursion:

```wl
double = TypeTheoryTerm[Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][Typed[t, Naturals] |-> Naturals, 0, {Typed[k, Naturals], Typed[r, Naturals]} |-> r + 2, n]]]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 2, n] -->

At a variable the recursor does not reduce, so `double[n] == n + n` needs a proof by induction, not by computation:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, double[n] == n + n], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

On a literal it reduces one successor at a time, and at 1000 that goes deeper than the kernel recurses:

```wl
WeakHeadNormalForm[TypeTheoryTerm[double[1000]]]
```

<!-- => Failure["RecursionLimit", ...] -->

The kernel computes [Plus]() on literals at once:

```wl
WeakHeadNormalForm[TypeTheoryTerm[1000 + 1000]]
```

<!-- => 2000 -->

---

A disjunction eliminates only into Prop, so a function cannot compute a number from a proof of one:

```wl
TypeTheoryType[Function[{Typed[h, True || False]}, InductiveRecursor[Or][Typed[t, True || False] |-> Naturals, Typed[a, True] |-> 1, Typed[b, False] |-> 2, h]]]
```

<!-- => Failure["TypeMismatch", ...] -->
