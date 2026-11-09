---
Template: Symbol
Name: TypeTheoryProofTree
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryProofTree
Keywords: [natural deduction, proof tree, derivation, propositional logic, induction, Curry-Howard, Gentzen, implication, conjunction, disjunction, falsity, universal statement, open assumption]
SeeAlso: [TypeTheoryTerm, TypeTheoryProof, TypeTheoryCheck, TypeTheoryType, TypeTheoryAxiomClosure]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryProofTree]()[*proof*]</code> gives the natural-deduction derivation of *proof*, a [TypeTheoryTerm]() that proves a proposition or a finished [TypeTheoryProof]().

<code>[TypeTheoryProofTree]()[*rule*, *claim*, {*premise*~1~, ...}]</code> is a natural-deduction derivation of the [TypeTheoryTerm]() *claim* by *rule* from the premises, each a [TypeTheoryProofTree]().

## Details & Options

- The rules of a proof of propositional logic are those of natural deduction for implication, conjunction, disjunction and falsity: `"Assumption"`, `"ImpliesIntro"`, `"ImpliesElim"`, `"AndIntro"`, `"AndElim"`, `"OrIntro"`, `"OrElim"` and `"FalseElim"`.
- Beyond propositional logic, a function of a variable that is no proof, as a number, is `"ForAllIntro"`, and a proof applied to such an argument `"ForAllElim"`. A theorem, an axiom or a constructor applied to arguments is a rule of its own name, as `"equalityTransitivity"`, whose premises are the proofs among its arguments; its other arguments, numbers and functions and types, show in the claims. A recursor whose motive gives propositions is the elimination of its type: `"Induction"` for the natural numbers and the like, `"ExistsElim"`, `"AndElim"`, `"OrElim"`, `"FalseElim"` and `"EqualElim"`, with its cases as premises, after its major premise where that is a proof.
- A proof maps to a derivation by its form, as the Curry-Howard correspondence has it: a hypothesis is an assumption, a function of a proof introduces an implication and an application eliminates one, `"andIntroduction"`, `"andEliminationLeft"` and `"andEliminationRight"` introduce and eliminate a conjunction, `"orIntroductionLeft"`, `"orIntroductionRight"` and the recursor of [Or]() a disjunction, and `"falseElimination"` falsity.
- The functions of propositions a proof begins with bind the atoms of the derivation, so the derivation proves the proposition the rest of the proof has, over those atoms.
- Each claim is the proposition its part of the proof proves. In a proof of propositional logic it is a formula over the atoms: an atom, [True](), [False](), a conjunction, a disjunction, a negation or an implication. A negation `¬a` is `a ⇒ False`, so applying a proof of it eliminates an implication.
- A constant applied to formulas, as `"excludedMiddle"` of an atom, is an open assumption, discharged by no rule.
- A term that is no proof, as a number or a function of numbers, gives `Missing["Untranslatable"]`. A term that does not type-check gives its [Failure]().
- *proof* is a [TypeTheoryTerm](), or a finished [TypeTheoryProof](), whose tree is that of the term the tactics built; a proof with goals left gives `Failure["ProofIncomplete", ...]`.
- `Information[proof, "ProofTree"]` gives the same derivation.
- A [TypeTheoryProofTree]() shows drawn, each conclusion under a line over its premises, with the rule named at the line's right, as →I, →E, ∀I, ∀E, ∧I, ∧E, ∨I, ∨E, ⊥E, ∃E or =E, or by its name; an assumption shows as its claim.

## Basic Examples

The derivation of `a ⇒ a`, an implication introduced over the assumption `a`:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x]]
```

<!-- => a / (a ⇒ a) →I -->

---

The derivation of the K combinator's proposition, `a ⇒ b ⇒ a`:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[x, a], Typed[y, b]} |-> x]]
```

<!-- => (a / (b ⇒ a) →I) / (a ⇒ b ⇒ a) →I -->

---

The two eliminations of a conjunction and its introduction swap the conjuncts:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{a, b, Typed[h, And[a, b]]} |-> "andIntroduction"["andEliminationRight"[h], "andEliminationLeft"[h]]]]
```

<!-- => (((a ∧ b) / b ∧E   (a ∧ b) / a ∧E) / (b ∧ a) ∧I) / ((a ∧ b) ⇒ (b ∧ a)) →I -->

## Scope

Modus ponens, an implication eliminated:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[f, Implies[a, b]], x} |-> f[x]]]
```

<!-- => (((a ⇒ b   a) / b →E) / (a ⇒ b) →I) / ((a ⇒ b) ⇒ a ⇒ b) →I -->

---

A disjunction introduced, its type given by [Typed]():

```wl
TypeTheoryProofTree[TypeTheoryTerm[{a, b, x} |-> Typed["orIntroductionLeft"[x], a || b]]]
```

<!-- => (a / (a ∨ b) ∨I) / (a ⇒ (a ∨ b)) →I -->

---

A disjunction eliminated by the recursor of [Or](), one case for each disjunct:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{a, b, Typed[h, Or[a, b]]} |->
    InductiveRecursor[Or][Or[b, a] &, x |-> "orIntroductionRight"[x], y |-> "orIntroductionLeft"[y], h]
]]
```

<!-- => ((a ∨ b   a / (b ∨ a) ∨I   b / (b ∨ a) ∨I) / (b ∨ a) ∨E) / ((a ∨ b) ⇒ (b ∨ a)) →I -->

---

Falsity eliminated:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{a, h} |-> Typed["falseElimination"[h], a]]]
```

<!-- => (False / a ⊥E) / (False ⇒ a) →I -->

---

A negation applied to a proof eliminates an implication, to falsity:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{a, Typed[x, a], Typed[n, Not[a]]} |-> n[x]]]
```

<!-- => (((¬a   a) / False →E) / ((¬a) ⇒ False) →I) / (a ⇒ (¬a) ⇒ False) →I -->

---

From a contradiction, anything:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{a, b, Typed[x, a], Typed[n, Not[a]]} |-> Typed["falseElimination"[n[x]], b]]]
```

<!-- => ((((¬a   a) / False →E) / b ⊥E) / ((¬a) ⇒ b) →I) / (a ⇒ (¬a) ⇒ b) →I -->

---

A theorem applied to an atom is an open assumption:

```wl
TypeTheoryProofTree[TypeTheoryTerm[a |-> "excludedMiddle"[a]]]
```

<!-- => a ∨ ¬a -->

---

Peirce's law by excluded middle: the instance of `"excludedMiddle"` is an open assumption, and the recursor of [Or]() eliminates it:

```wl
TypeTheoryProofTree[TypeTheoryTerm[
    Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[f, Implies[Implies[a, b], a]]},
        InductiveRecursor[Or][
            Function[{Typed[t, Or[a, Not[a]]]}, a],
            Function[{x}, x],
            Function[{n}, f[y |-> "falseElimination"[n[y]]]],
            "excludedMiddle"[a]
        ]
    ]
]]
```

<!-- => ((a ∨ ¬a   a   ((a ⇒ b) ⇒ a   (((¬a   a) / False →E) / b ⊥E) / (a ⇒ b) →I) / a →E) / a ∨E) / (((a ⇒ b) ⇒ a) ⇒ a) →I -->

---

A proof made with tactics:

```wl
swapped = TypeTheoryProof[
    ForAll[{a, b}, Implies[a && b, b && a]],
    {"Introduce"[a, b, h], TypeTheoryTactic["Exact", "andIntroduction"["andEliminationRight"[h], "andEliminationLeft"[h]]]}
]
```

<!-- => Proof complete -->

Its derivation, of the term the symbol stands for:

```wl
TypeTheoryProofTree[TypeTheoryTerm[swapped]]
```

<!-- => (((a ∧ b) / b ∧E   (a ∧ b) / a ∧E) / (b ∧ a) ∧I) / ((a ∧ b) ⇒ (b ∧ a)) →I -->

---

A derivation written out, an assumption under an implication introduced:

```wl
TypeTheoryProofTree["ImpliesIntro", TypeTheoryTerm[Implies[a, a]], {TypeTheoryProofTree["Assumption", TypeTheoryTerm[a], {}]}]
```

<!-- => a / (a ⇒ a) →I -->

A finished [TypeTheoryProof]() gives the tree of its term, as the tactics built it:

```wl
TypeTheoryProofTree[TypeTheoryProof[ForAll[{a}, Implies[a, a]], {"Introduce"[a, h], "Assumption"}]]
```

<!-- => a / (a ⇒ a) →I -->

---

A proof beyond propositional logic has a derivation too. A theorem applied is a rule of its own name:

```wl
TypeTheoryProofTree[TypeTheoryTerm["equalityReflexivity"[2]]]
```

<!-- => the derivation of 2 == 2 by equalityReflexivity, from no premise -->

A proof by induction that tactics built: the variable is introduced, the recursor is the induction over its two cases, and the case of the successor introduces its variable and its hypothesis, which is the assumption at its top:

```wl
induction = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {"Introduce"[n], "Induction"[n], "Reflexivity", "Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]}];
TypeTheoryProofTree[induction]
```

<!-- => the derivation of ∀_n∶ℕ 0 + n == n by ∀I from an Induction, whose premises are equalityReflexivity and, by ∀I and →I, equalityCongruence from the assumption 0 + k == k -->

Its rules:

```wl
Cases[TypeTheoryProofTree[induction], TypeTheoryProofTree[rule_, __] :> rule, {0, Infinity}]
```

<!-- => {"equalityReflexivity", "Assumption", "equalityCongruence", "ImpliesIntro", "ForAllIntro", "Induction", "ForAllIntro"} -->

A hypothesis applied to a number eliminates a universal statement:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[h, ForAll[{Typed[n, Naturals]}, n + 0 == n]]} |-> h[2]]]
```

<!-- => the derivation of (∀_n∶ℕ n + 0 == n) ⇒ 2 + 0 == 2 by →I from ∀E of the assumption -->

## Properties and Relations

[Information]() gives the same derivation:

```wl
Information[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x], "ProofTree"] === TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x]]
```

<!-- => True -->

---

The derivation is an expression of its rules, claims and premises:

```wl
Cases[TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x]], TypeTheoryProofTree[rule_, __] :> rule, {0, Infinity}]
```

<!-- => {"Assumption", "ImpliesIntro"} -->

---

The rule of the last step comes first:

```wl
First[TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x]]]
```

<!-- => "ImpliesIntro" -->

---

The type of the proof quantifies over the atoms, which the derivation leaves free:

```wl
TypeTheoryType[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x]
```

<!-- => ∀_a∶Prop a ⇒ a -->

## Possible Issues

A term that is no proof has no derivation:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[n, Naturals]} |-> n + 1]]
```

<!-- => Missing["Untranslatable"] -->

---

A disjunction introduced without its type leaves the other disjunct to find:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[x, a]} |-> "orIntroductionLeft"[x]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

---

A term that does not type-check gives its [Failure]():

```wl
TypeTheoryProofTree[TypeTheoryTerm[1 + True]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A proof with goals left has no tree yet:

```wl
TypeTheoryProofTree[TypeTheoryProof[ForAll[{a}, Implies[a, a]], {"Introduce"[a, h]}]]
```

<!-- => Failure["ProofIncomplete", ...] -->
