---
Template: Symbol
Name: TypeTheoryProofTree
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryProofTree
Keywords: [natural deduction, proof tree, derivation, propositional logic, Curry-Howard, Gentzen]
SeeAlso: [TypeTheoryTerm, TypeTheoryCheck, TypeTheoryAxiomClosure, TypeTheoryProof]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryProofTree]()[*proof*]</code> gives the natural-deduction derivation of the [TypeTheoryTerm]() *proof*, a proof of propositional logic.

<code>[TypeTheoryProofTree]()[*rule*, *claim*, {*premise*~1~, ...}]</code> is a natural-deduction derivation of the [TypeTheoryTerm]() *claim* by *rule* from the premises, each a [TypeTheoryProofTree]().

## Details & Options

- The rules are those of natural deduction for implication, conjunction, disjunction and falsity: `"Assumption"`, `"ImpliesIntro"`, `"ImpliesElim"`, `"AndIntro"`, `"AndElim"`, `"OrIntro"`, `"OrElim"` and `"FalseElim"`.
- A proof maps to a derivation by its form, as the Curry-Howard correspondence has it: a hypothesis is an assumption, a function of a proof introduces an implication and an application eliminates one, `"andIntroduction"`, `"andEliminationLeft"` and `"andEliminationRight"` introduce and eliminate a conjunction, `"orIntroductionLeft"`, `"orIntroductionRight"` and the recursor of [Or]() a disjunction, and `"falseElimination"` falsity.
- The functions of propositions a proof begins with bind the atoms of the derivation.
- Each claim is the proposition its part of the proof proves, and must be a formula over the atoms: an atom, [True](), [False](), a conjunction, a disjunction, a negation or an implication.
- A constant applied to formulas, as `"excludedMiddle"` of an atom, is an open assumption, discharged by no rule.
- A proof that has another part, or a claim that is not such a formula, gives `Missing["Untranslatable"]`.
- `Information[proof, "ProofTree"]` gives the same derivation.
- A [TypeTheoryProofTree]() shows drawn, each conclusion under a line over its premises, with the rule named at the line's right, as →I, →E, ∧I, ∧E, ∨I, ∨E or ⊥E.

## Basic Examples

The derivation of the K combinator's proposition, a ⇒ b ⇒ a:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[x, a], Typed[y, b]} |-> x]]
```

---

The two eliminations of a conjunction and its introduction swap the conjuncts:

```wl
TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[h, And[a, b]]} |-> "andIntroduction"["andEliminationRight"[h], "andEliminationLeft"[h]]]]
```

## Scope

Peirce's law by excluded middle: the instance of `"excludedMiddle"` is an open assumption, and the recursor of [Or]() eliminates it:

```wl
TypeTheoryProofTree[TypeTheoryTerm[
    Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[f, Implies[Implies[a, b], a]]},
        InductiveRecursor[Or][
            Function[{Typed[t, Or[a, Not[a]]]}, a],
            Function[{Typed[x, a]}, x],
            Function[{Typed[n, Not[a]]}, f[Typed[y, a] |-> "falseElimination"[n[y]]]],
            "excludedMiddle"[a]
        ]
    ]
]]
```

---

The derivation is an expression of its rules, claims and premises:

```wl
Cases[TypeTheoryProofTree[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x]], TypeTheoryProofTree[rule_, __] :> rule, {0, Infinity}]
```

<!-- => {Assumption, ImpliesIntro} -->

## Possible Issues

A proof that is not one of propositional logic has no derivation:

```wl
TypeTheoryProofTree[TypeTheoryTerm["equalityReflexivity"[2]]]
```

<!-- => Missing[Untranslatable] -->
