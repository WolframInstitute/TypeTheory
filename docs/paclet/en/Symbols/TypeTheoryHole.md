---
Template: Symbol
Name: TypeTheoryHole
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryHole
Keywords: [hole, sorry, unfinished proof, open theorem, citation, annotation, placeholder, Mathlib, evidence, evaluation]
SeeAlso: [TypeTheoryTheorem, TypeTheoryProof, TypeTheoryTactic, TypeTheoryAxiom, TypeTheoryAxiomClosure, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryHole]()[]</code> stands in the proof of a declared theorem for a term of the type expected there, a proof left to give, as Lean's `sorry`.

<code>[TypeTheoryHole]()[*annotation*]</code> carries *annotation*, a citation or the evidence of a computation, which the theorem's environment keeps.

<code>[TypeTheoryHole]()[*theorem*, *k*]</code> is the *k*-th hole of the proof of *theorem*, a constant of the environment that declares *theorem*.

## Details & Options

- A hole stands where [TypeTheoryTheorem]() is given a proof, as all of it or as a part, and the tactic `"Hole"` of [TypeTheoryTactic]() closes a goal of a [TypeTheoryProof]() with one. A hole elsewhere, as in a definition or an axiom, or with no type expected, gives a [Failure]().
- A theorem whose proof has holes is declared after a constant <code>[TypeTheoryHole]()[*theorem*, *k*]</code> for each, in the order its proof term holds them. A hole's type is the type expected where it stands, under the variables in scope there.
- The kernel checks the theorem with its holes as it would with axioms in their place. A hole is never taken for a proof: [TypeTheoryAxiomClosure]() leaves holes out of the axioms, and <code>[Information]()[*term*, "Holes"]</code> gives the holes a term rests on, those of the theorems it uses included, by theorem, each with its statement and annotation. <code>[Information]()[*env*, "Kinds"]</code> counts them as `"Hole"`.
- An annotation is kept as given: a string is short for <code><\|"Citation" -> *string*\|></code>, and an association, such as <code><\|"Citation" -> *refs*, "Mathlib" -> *name*\|></code> or <code><\|"Evaluation" -> [HoldForm]()[*expr*], "Value" -> *value*\|></code>, is kept as it is. A hole with no annotation has the annotation [None](). <code>[Information]()[[TypeTheoryTerm]()[[TypeTheoryHole]()[*theorem*, *k*], *env*], "Annotation"]</code> gives it back.
- [TypeTheoryCheck]() replays a hole as it replays an axiom, and [Normal]() writes a theorem's proof with <code>[TypeTheoryHole]()[*annotation*]</code> where its holes stand, so its declarations declare the holes again. A saved environment keeps holes and their annotations.
- A hole shows as *hole*, with its annotation as a tooltip.

## Basic Examples

A theorem left open, with a citation:

```wl
open = TypeTheoryEnvironment[{TypeTheoryTheorem[AllZero, ForAll[{n}, n == 0], TypeTheoryHole["a claim left open"]]}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The environment has the hole, a constant before the theorem:

```wl
Take[Keys[open], -2]
```

<!-- => {TypeTheoryHole[AllZero, 1], AllZero} -->

The holes the theorem rests on, with their statements and annotations:

```wl
Information[TypeTheoryTerm[AllZero, open], "Holes"]
```

<!-- => <|AllZero -> {<|"Hole" -> TypeTheoryHole[AllZero, 1], "Statement" -> ∀_n∶ℕ n == 0, "Annotation" -> <|"Citation" -> "a claim left open"|>|>}|> -->

---

The tactic `"Hole"` closes a goal of a proof with a hole:

```wl
TypeTheoryProof[ForAll[{m, n}, m + n == n + m], {"Introduce"[m, n], "Hole"["addition commutes"]}]
```

<!-- => Proof complete with 1 hole -->

## Scope

### Holes in Proof Terms

A part of a proof left to give, under a binder:

```wl
partial = TypeTheoryEnvironment[{TypeTheoryTheorem[BothZero, ForAll[{n}, n + 0 == n && 0 + n == n],
    n |-> "andIntroduction"["equalityReflexivity"[n], TypeTheoryHole["zero plus n, by induction"]]]}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The hole states the part left, for every *n* in scope where it stands:

```wl
TypeTheoryType[TypeTheoryHole[BothZero, 1], partial]
```

<!-- => ∀_n∶ℕ 0 + n == n -->

---

A hole with no annotation:

```wl
later = TypeTheoryEnvironment[TypeTheoryTheorem[AdditionCommutes, ForAll[{m, n}, m + n == n + m], TypeTheoryHole[]]]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

Its annotation is [None]():

```wl
Information[TypeTheoryTerm[AdditionCommutes, later], "Holes"]
```

<!-- => <|AdditionCommutes -> {<|"Hole" -> TypeTheoryHole[AdditionCommutes, 1], "Statement" -> ∀_m∶ℕ ∀_n∶ℕ m + n == n + m, "Annotation" -> None|>}|> -->

### Holes from Tactics

A proof with two holes, one for each part of a conjunction:

```wl
proof = TypeTheoryProof[ForAll[{m, n}, m + n == n + m && m n == n m], {
    "Introduce"[m, n],
    "Constructor",
    "Hole"["addition commutes"],
    "Hole"["multiplication commutes"]
}]
```

<!-- => Proof complete with 2 holes -->

The theorem declared with it:

```wl
both = TypeTheoryEnvironment[TypeTheoryTheorem[BothCommute, proof]]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

A constant for each hole, in the order of the proof:

```wl
Take[Keys[both], -3]
```

<!-- => {TypeTheoryHole[BothCommute, 1], TypeTheoryHole[BothCommute, 2], BothCommute} -->

The second hole states the second part, for all the variables the tactics introduced:

```wl
TypeTheoryType[TypeTheoryHole[BothCommute, 2], both]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m n == n m -->

### Annotations

A hole that cites the theorem of Mathlib that would fill it:

```wl
cited = TypeTheoryEnvironment[TypeTheoryTheorem[AdditionCommutes, ForAll[{m, n}, m + n == n + m],
    TypeTheoryHole[<|"Citation" -> "Mathlib", "Mathlib" -> "Nat.add_comm"|>]]]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The annotation, as it was given:

```wl
Information[TypeTheoryTerm[TypeTheoryHole[AdditionCommutes, 1], cited], "Annotation"]
```

<!-- => <|"Citation" -> "Mathlib", "Mathlib" -> "Nat.add_comm"|> -->

---

A hole that records the evaluation that found a solution of Pell's equation `x^2 - 61 y^2 == 1`:

```wl
pell = TypeTheoryEnvironment[TypeTheoryTheorem[PellSolution, Exists[{x, y}, x^2 == 61 y^2 + 1 && 0 < y],
    TypeTheoryHole[<|"Evaluation" -> HoldForm[FindInstance[x^2 - 61 y^2 == 1 && y > 0, {x, y}, PositiveIntegers]], "Value" -> {{x -> 1766319049, y -> 226153980}}|>]]]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The evaluation and its value, kept held:

```wl
Information[TypeTheoryTerm[TypeTheoryHole[PellSolution, 1], pell], "Annotation"]
```

<!-- => <|"Evaluation" -> FindInstance[x^2 - 61 y^2 == 1 && y > 0, {x, y}, ℤ_>0], "Value" -> {{x -> 1766319049, y -> 226153980}}|> -->

## Properties and Relations

A theorem with a hole, and a theorem proved from it:

```wl
uses = TypeTheoryEnvironment[{
	TypeTheoryTheorem[AllZero, ForAll[{n}, n == 0], TypeTheoryHole["a claim left open"]],
	TypeTheoryTheorem[ThreeIsZero, 3 == 0, AllZero[3]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

The theorem proved from it inherits its hole:

```wl
Keys[Information[TypeTheoryTerm[ThreeIsZero, uses], "Holes"]]
```

<!-- => {AllZero} -->

A hole is no axiom, so the theorem rests on none:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[ThreeIsZero, uses]]
```

<!-- => <||> -->

---

The same statement assumed with [TypeTheoryAxiom]() is an axiom the theorem rests on:

```wl
assumed = TypeTheoryEnvironment[{
	TypeTheoryAxiom[AllZeroAxiom, ForAll[{n}, n == 0]],
	TypeTheoryTheorem[ThreeIsZero, 3 == 0, AllZeroAxiom[3]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The theorem rests on the axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[ThreeIsZero, assumed]]
```

<!-- => <|AllZeroAxiom -> "Proposition"|> -->

---

A theorem left open:

```wl
open = TypeTheoryEnvironment[{TypeTheoryTheorem[AllZero, ForAll[{n}, n == 0], TypeTheoryHole["a claim left open"]]}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

A proof by tactics uses it as any other theorem, so a false claim left open proves false consequences:

```wl
TypeTheoryProof[ForAll[{m}, m + 1 == 0], open, {"Introduce"[m], "Exact"[AllZero[m + 1]]}]
```

<!-- => Proof complete -->

The kinds of the constants count the hole:

```wl
Information[open, "Kinds"]
```

<!-- => <|"InductiveType" -> 27, "Constructor" -> 41, "Recursor" -> 28, "Definition" -> 81, "Quotient" -> 4, "Theorem" -> 73, "Axiom" -> 4, "Hole" -> 1|> -->

[TypeTheoryCheck]() checks the environment again, the hole as it would an axiom:

```wl
TypeTheoryCheck[open]
```

<!-- => Success["EnvironmentChecked", ...] -->

---

A saved environment keeps the holes and their annotations:

```wl
open = TypeTheoryEnvironment[{TypeTheoryTheorem[AllZero, ForAll[{n}, n == 0], TypeTheoryHole["a claim left open"]]}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

Save it and read it back:

```wl
file = Export[FileNameJoin[{$TemporaryDirectory, "open.wxf"}], open];
saved = TypeTheoryEnvironment[file]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The annotation read back:

```wl
Information[TypeTheoryTerm[TypeTheoryHole[AllZero, 1], saved], "Annotation"]
```

<!-- => <|"Citation" -> "a claim left open"|> -->

## Possible Issues

A hole stands only in a declared theorem's proof:

```wl
TypeTheoryType[Typed[TypeTheoryHole[], 1 == 1]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A definition cannot leave its value to give; a hole is a proof, and a definition's value is data:

```wl
TypeTheoryEnvironment[TypeTheoryDefinition[Mystery, Typed[TypeTheoryHole[], Naturals]]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A proof with goals still open is no proof; close them, with holes where a proof is left to give:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[Unfinished, TypeTheoryProof[1 == 1, {}]]}]
```

<!-- => Failure["ProofIncomplete", ...] -->
