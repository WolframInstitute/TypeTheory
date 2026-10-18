---
Template: Paclet
ResourceType: Paclet
Name: WolframInstitute/TypeTheory
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
Description: A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language
ContributedBy: Nik Murzin
Keywords: [type theory, dependent types, Calculus of Inductive Constructions, proof assistant, proof checking, kernel, inductive types, tactics, theorem proving, formal mathematics, Lean, Coq]
MainGuide: Documentation/English/Guides/TypeTheory.nb
License: MIT
WolframVersion: 15.0+
Categories: [Higher Mathematical Computation, Symbolic & Numeric Computation]
Disclosures: [WLSystemSymbols]
Sources: ["Thierry Coquand, Gérard Huet, *The Calculus of Constructions*, Information and Computation 76, 1988", "Christine Paulin-Mohring, *Inductive Definitions in the System Coq: Rules and Properties*, TLCA 1993", "Mario Carneiro, *The Type Theory of Lean*, Master's thesis, Carnegie Mellon University, 2019"]
Links: ["[LeanLink, the Wolfram Language link to Lean, which translates declarations to and from TypeTheory](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink)", "[Lean 4 (lean-lang.org)](https://lean-lang.org/)"]
---

## Details & Options

- TypeTheory is a proof engine for the **Calculus of Inductive Constructions**, the dependent type theory of Lean and Coq, written entirely in the Wolfram Language, with no native library and no dependency on Lean.
- Terms are ordinary expressions built from built-in symbols - [Function](), [Typed](), [ForAll](), [Implies](), [Equal](), [Plus]() - held in a [TypeTheoryTerm](), which displays them in mathematical notation.
- Declarations are inert constructors - [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType]() and [TypeTheoryNaturalNumbers]() - that a small kernel checks when they are added to a [TypeTheoryEnvironment](). There is no global state: an environment is a value, a handle to a store of definitions, and every term and proof carries the environment it lives in.
- The kernel infers types, reduces terms, decides definitional equality (with eta for functions and structures, and proof irrelevance), checks inductive families for strict positivity and universe constraints, and generates their recursors.
- [TypeTheoryProof]() and [TypeTheoryTactic]() build proofs step by step. Nothing a tactic does is trusted: the kernel checks the finished proof term.
- The prelude, <code>[TypeTheoryEnvironment]()["Prelude"]</code>, has logic ([True](), [False](), [Not](), [And](), [Or](), [Exists]()), equality ([Equal]()) and the natural numbers ([NonNegativeIntegers](), with [Plus]()), so that literals are natural numbers.

## Usage

[TypeTheoryTerm]() writes terms; [TypeOf](), [TypeTheoryCheck](), [WeakHeadNormalForm]() and [DefinitionallyEqualQ]() check and compute them. [TypeTheoryEnvironment]() builds environments from the declarations [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType]() and [TypeTheoryNaturalNumbers](). [TypeTheoryProof]() and [TypeTheoryTactic]() prove theorems interactively. [TypeUniverse](), [ImpredicativeMaximum]() and [InductiveRecursor]() are part of the term language, and [TrueIntroduction](), [AndIntroduction](), [EqualityReflexivity](), [EqualityCongruence]() and the other constants of the prelude are proofs to build on.

## Basic Examples

The type of a term in the prelude:

```wl
TypeOf[TypeTheoryTerm[2 + 3, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ℕ -->

---

Terms compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + n][21], TypeTheoryEnvironment["Prelude"]]]
```

<!-- => 42 -->

---

Add a theorem to the prelude, checked by the kernel:

```wl
arithmetic = Append[TypeTheoryEnvironment["Prelude"], TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]];
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

---

A wrong proof is rejected:

```wl
Append[TypeTheoryEnvironment["Prelude"], TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]]
```

<!-- => Failure["TypeMismatch", ...] -->

## Scope

Prove `0 + n == n` by induction:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], TypeTheoryEnvironment["Prelude"], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Induction", n],
    TypeTheoryTactic["Reflexivity"],
    TypeTheoryTactic["Introduce", k, ih],
    TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]]
}]
```

<!-- => Proof complete -->

The proof term the tactics built:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(a ∶ ℕ) ↦ 0 + a == a, EqualityReflexivity[0 + NaturalNumberZero], (k ∶ ℕ) (ih ∶ 0 + k == k) ↦ EqualityCongruence[NaturalNumberSuccessor, ih], n] -->

---

Declare an inductive type, and compute with its recursor:

```wl
lists = TypeTheoryEnvironment[TypeTheoryEnvironment["Prelude"], {
    TypeTheoryInductiveType[NaturalList, TypeUniverse[1], {
        EmptyList -> NaturalList,
        ConsList -> ForAll[{Typed[h, NonNegativeIntegers], Typed[t, NaturalList]}, NaturalList]
    }],
    TypeTheoryDefinition[ListSum, Typed[
        Function[{Typed[l, NaturalList]}, InductiveRecursor[NaturalList][
            Function[{Typed[x, NaturalList]}, NonNegativeIntegers],
            0,
            Function[{Typed[h, NonNegativeIntegers], Typed[t, NaturalList], Typed[r, NonNegativeIntegers]}, h + r],
            l
        ]],
        TypeSpecifier[{NaturalList} -> NonNegativeIntegers]
    ]]
}];
WeakHeadNormalForm[TypeTheoryTerm[ListSum[ConsList[5, ConsList[6, ConsList[7, EmptyList]]]], lists]]
```

<!-- => 18 -->

## Properties and Relations

Check every declaration of an environment again from scratch:

```wl
TypeTheoryCheck[TypeTheoryEnvironment["Prelude"]]
```

<!-- => True -->

## Possible Issues

- Elaboration fills in implicit arguments by first-order unification, extended to patterns; there are no type classes. Mutual and nested inductive types and quotients are not supported yet, and the tactic `"Induction"` does not handle indexed families.
- The kernel is interpreted Wolfram Language: checking is fast enough for interactive proofs and libraries of hundreds of declarations, not for Mathlib.

## Author Notes

TypeTheory was designed and written by Nik Murzin (Wolfram Institute), with Anthropic's [Claude](https://www.anthropic.com/claude); these documentation pages were drafted with Claude against the live paclet and reviewed by the author. AI-assisted authorship is disclosed here so a reader can weigh the source appropriately.
