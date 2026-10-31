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

<code>[TypeTheoryProofTree]()[*rule*, *claim*, {*premise*~1~, ...}]</code> is a natural-deduction derivation of the [TypeTheoryTerm]() *claim* by *rule* from the premises, each a [TypeTheoryProofTree]().

<code>[Information]()[*proof*, "ProofTree"]</code> gives the derivation of the [TypeTheoryTerm]() *proof*, a proof of propositional logic.

## Details & Options

- The rules are those of natural deduction for implication, conjunction, disjunction and falsity: `"Assumption"`, `"ImpliesIntro"`, `"ImpliesElim"`, `"AndIntro"`, `"AndElim"`, `"OrIntro"`, `"OrElim"` and `"FalseElim"`.
- A proof maps to a derivation by its form, as the Curry-Howard correspondence has it: a hypothesis is an assumption, a function of a proof introduces an implication and an application eliminates one, [AndIntroduction](), [AndEliminationLeft]() and [AndEliminationRight]() introduce and eliminate a conjunction, [OrIntroductionLeft](), [OrIntroductionRight]() and the recursor of [Or]() a disjunction, and [FalseElimination]() falsity.
- The functions of propositions a proof begins with bind the atoms of the derivation.
- Each claim is the proposition its part of the proof proves, and must be a formula over the atoms: an atom, [True](), [False](), a conjunction, a disjunction, a negation or an implication.
- A constant applied to formulas, as [ExcludedMiddle]() of an atom, is an open assumption, discharged by no rule.
- A proof that has another part, or a claim that is not such a formula, gives `Missing["Untranslatable"]`.
- A [TypeTheoryProofTree]() shows drawn, each conclusion under a line over its premises, with the rule named at the line's right, as →I, →E, ∧I, ∧E, ∨I, ∨E or ⊥E.

## Basic Examples

The derivation of the K combinator's proposition, a ⇒ b ⇒ a:

```wl
Information[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[x, a], Typed[y, b]}, x]], "ProofTree"]
```

---

The two eliminations of a conjunction and its introduction swap the conjuncts:

```wl
Information[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[h, And[a, b]]}, AndIntroduction[AndEliminationRight[h], AndEliminationLeft[h]]]], "ProofTree"]
```

## Scope

Peirce's law by excluded middle: the instance of [ExcludedMiddle]() is an open assumption, and the recursor of [Or]() eliminates it:

```wl
Information[
    TypeTheoryTerm[
        Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[f, Implies[Implies[a, b], a]]},
            InductiveRecursor[Or][
                Function[{Typed[t, Or[a, Not[a]]]}, a],
                Function[{Typed[x, a]}, x],
                Function[{Typed[n, Not[a]]}, f[Function[{Typed[y, a]}, FalseElimination[n[y]]]]],
                ExcludedMiddle[a]
            ]
        ]
    ],
    "ProofTree"
]
```

---

The derivation is an expression of its rules, claims and premises:

```wl
Cases[Information[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[x, a]}, x]], "ProofTree"], TypeTheoryProofTree[rule_, __] :> rule, {0, Infinity}]
```

<!-- => {Assumption, ImpliesIntro} -->

## Possible Issues

A proof that is not one of propositional logic has no derivation:

```wl
Information[TypeTheoryTerm[EqualityReflexivity[2]], "ProofTree"]
```

<!-- => Missing[Untranslatable] -->
