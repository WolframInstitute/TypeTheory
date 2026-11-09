---
Template: Paclet
ResourceType: Paclet
Name: WolframInstitute/TypeTheory
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
Description: A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language
ContributedBy: Nik Murzin
Keywords: [type theory, dependent types, Calculus of Inductive Constructions, proof assistant, proof checking, kernel, inductive types, tactics, theorem proving, formal mathematics, Rocq]
MainGuide: Documentation/English/Guides/TypeTheory.nb
License: MIT
WolframVersion: 15.0+
Categories: [Higher Mathematical Computation, Symbolic & Numeric Computation]
Disclosures: [WLSystemSymbols]
Sources: ["Thierry Coquand, Gérard Huet, *The Calculus of Constructions*, Information and Computation 76, 1988", "Christine Paulin-Mohring, *Inductive Definitions in the System Coq: Rules and Properties*, TLCA 1993", "Mario Carneiro, *The Type Theory of Lean*, Master's thesis, Carnegie Mellon University, 2019"]
Links: ["[LeanLink, the Wolfram Language link to Lean, which translates declarations to and from TypeTheory](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink)"]
---

## Details & Options

- TypeTheory is a proof engine for the **Calculus of Inductive Constructions**, a dependent type theory, written in the Wolfram Language; [TypeTheoryCheck]() also has a compiled kernel, the same algorithm compiled to native code.
- Terms are ordinary expressions built from built-in symbols - [Function](), [Typed](), [ForAll](), [Implies](), [Equal](), [Plus]() - held in a [TypeTheoryTerm](), which displays them in mathematical notation.
- Declarations are inert constructors - [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType](), [TypeTheoryNaturalNumbers](), [TypeTheoryRewriteRule](), [TypeTheoryQuotients]() and [TypeTheoryCubical]() - that a small kernel checks when they are added to a [TypeTheoryEnvironment](). An environment is a value, a handle to a store of definitions, and every term and proof carries the environment it lives in; the one setting is the default environment, [$TypeTheoryEnvironment](), the prelude unless [SetTypeTheoryEnvironment]() sets another.
- The kernel infers types, reduces terms, decides definitional equality (with eta for functions and structures, and proof irrelevance), checks inductive families for strict positivity and universe constraints, and generates their recursors.
- [TypeTheoryProof]() and [TypeTheoryTactic]() build proofs step by step. Nothing a tactic does is trusted: the kernel checks the finished proof term.
- The prelude has classical logic ([True](), [False](), [Not](), [And](), [Or](), [Exists]()), equality ([Equal]()), the natural numbers ([NonNegativeIntegers]()) with their arithmetic and order, so that literals are natural numbers, the Booleans, decisions, quotient types, pairs, sums, options and lists. It is the default environment unless [SetTypeTheoryEnvironment]() sets another.
- Terms display as mathematics: `∀`, `∃`, `↦`, `⇒`, `∧`, `∨`, `¬`, universes as Prop, Type and Sort, and the natural numbers as `0` and `n + 1`.

## Usage

[TypeTheoryTerm]() writes terms; [TypeTheoryType](), [TypeTheoryCheck](), [WeakHeadNormalForm]() and [DefinitionallyEqualQ]() check and compute them. [TypeTheoryEnvironment]() builds environments from the declarations [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType](), [TypeTheoryNaturalNumbers](), [TypeTheoryRewriteRule](), [TypeTheoryQuotients]() and [TypeTheoryCubical](). [TypeTheoryProof]() and [TypeTheoryTactic]() prove theorems interactively. [TypeUniverse](), [ImpredicativeMaximum]() and [InductiveRecursor]() are part of the term language, and `"trueIntroduction"`, `"andIntroduction"`, `"equalityReflexivity"`, `"equalityCongruence"` and the other constants of the prelude are proofs to build on.

## Basic Examples

The type of a term in the prelude:

```wl
TypeTheoryType[2 + 3]
```

<!-- => ℕ -->

---

Terms compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n + n][21]]]
```

<!-- => 42 -->

---

Add a theorem to the prelude, checked by the kernel:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 110 constants -->

The theorem in it:

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

---

A wrong proof is rejected:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[Wrong, 2 + 2 == 5, "equalityReflexivity"[4]]}]
```

<!-- => Failure["TypeMismatch", ...] -->

## Scope

Prove `0 + n == n` by induction:

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

The proof term the tactics built:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 0 + n1 == n1, equalityReflexivity[0 + 0], (k ∶ ℕ) (ih ∶ 0 + k == k) ↦ equalityCongruence[successor, ih], n] -->

---

Declare an inductive type, and a sum defined with its recursor:

```wl
lists = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[NaturalList, TypeUniverse[1], {
        "empty" -> NaturalList,
        "cons" -> ForAll[{Typed[h, Naturals], Typed[t, NaturalList]}, NaturalList]
    }],
    TypeTheoryDefinition[ListSum, Typed[
        Function[{Typed[l, NaturalList]}, InductiveRecursor[NaturalList][
            Function[{Typed[x, NaturalList]}, Naturals],
            0,
            Function[{Typed[h, Naturals], Typed[t, NaturalList], Typed[r, Naturals]}, h + r],
            l
        ]],
        TypeSpecifier[{NaturalList} -> Naturals]
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 114 constants -->

The sum computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[ListSum["cons"[5, "cons"[6, "cons"[7, "empty"]]]], lists]]
```

<!-- => 18 -->

## Properties and Relations

Check every declaration of an environment again from scratch, the prelude's included:

```wl
TypeTheoryCheck[TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Possible Issues

- Elaboration fills in implicit arguments by unification, extended to patterns, and finds instances of classes and coercions; it does not search for proofs, so a statement that needs one is proved with [TypeTheoryProof]() and its tactics.
- The tactic `"Induction"` eliminates a variable of an indexed family only when the indices are distinct variables.
- Elaboration, and the kernel that checks each declaration as it is made, run in Wolfram Language. <code>[TypeTheoryCheck]()[*env*]</code> checks a whole environment again with the compiled kernel, about a hundred times faster.

## Author Notes

TypeTheory was designed and written by Nik Murzin (Wolfram Institute), with Anthropic's [Claude](https://www.anthropic.com/claude); these documentation pages were drafted with Claude against the live paclet and reviewed by the author. AI-assisted authorship is disclosed here so a reader can weigh the source appropriately.
