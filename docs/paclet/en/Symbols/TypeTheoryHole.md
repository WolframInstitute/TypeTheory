---
Template: Symbol
Name: TypeTheoryHole
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryHole
Keywords: [hole, sorry, unfinished proof, open theorem, citation, annotation, placeholder]
SeeAlso: [TypeTheoryTheorem, TypeTheoryProof, TypeTheoryTactic, TypeTheoryAxiomClosure, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryHole]()[]</code> stands in the proof of a declared theorem for a term of the type expected there, a proof left to give, as Lean's `sorry`.

<code>[TypeTheoryHole]()[*annotation*]</code> carries *annotation*, a citation or the evidence of a computation, which the theorem's environment keeps.

<code>[TypeTheoryHole]()[*theorem*, *k*]</code> is the *k*-th hole of the proof of *theorem*, a constant of the environment that declares *theorem*.

## Details & Options

- A hole stands where [TypeTheoryTheorem]() is given a proof, as all of it or as a part, and the tactic `"Hole"` of [TypeTheoryTactic]() closes a goal of a [TypeTheoryProof]() with one. A hole elsewhere, or with no type expected, gives a [Failure]().
- A theorem whose proof has holes is declared after a constant <code>[TypeTheoryHole]()[*theorem*, *k*]</code> for each, in the order its proof term holds them. A hole's type is the type expected where it stands, under the variables in scope there.
- The kernel checks the theorem with its holes as it would with axioms in their place. A hole is never taken for a proof: [TypeTheoryAxiomClosure]() leaves holes out of the axioms, and <code>[Information]()[*term*, "Holes"]</code> gives the holes a term rests on, those of the theorems it uses included, by theorem, each with its statement and annotation.
- An annotation is kept as given: a string is short for <code><\|"Citation" -> *string*\|></code>, and an association, such as <code><\|"Citation" -> *refs*, "Mathlib" -> *name*\|></code> or <code><\|"Evaluation" -> [HoldForm]()[*expr*], "Value" -> *value*\|></code>, is kept as it is. <code>[Information]()[[TypeTheoryTerm]()[[TypeTheoryHole]()[*theorem*, *k*], *env*], "Annotation"]</code> gives it back.
- [TypeTheoryCheck]() replays a hole as it replays an axiom, and [Normal]() writes a theorem's proof with <code>[TypeTheoryHole]()[*annotation*]</code> where its holes stand, so its declarations declare the holes again. A saved environment keeps holes and their annotations.
- A hole shows as *hole*, with its annotation as a tooltip.

## Basic Examples

A theorem left open, with a citation:

```wl
open = TypeTheoryEnvironment[{TypeTheoryTheorem[AllZero, ForAll[{Typed[n, Naturals]}, n == 0], TypeTheoryHole["a claim left open"]]}]
```

<!-- => TypeTheoryEnvironment summary box: 171 constants -->

The environment has the theorem and its hole:

```wl
Take[Keys[open], -2]
```

<!-- => {TypeTheoryHole[AllZero, 1], AllZero} -->

The holes the theorem rests on:

```wl
Information[TypeTheoryTerm[AllZero, open], "Holes"]
```

<!-- => <|AllZero -> {<|"Hole" -> TypeTheoryHole[AllZero, 1], "Statement" -> ∀_n∶ℕ n == 0, "Annotation" -> <|"Citation" -> "a claim left open"|>|>}|> -->

## Scope

A part of a proof left to give, under a binder:

```wl
partial = TypeTheoryEnvironment[{TypeTheoryTheorem[BothZero, ForAll[{Typed[n, Naturals]}, n + 0 == n && 0 + n == n],
    Function[{Typed[n, Naturals]}, AndIntroduction[EqualityReflexivity[n], TypeTheoryHole["zero plus n, by induction"]]]]}]
```

<!-- => TypeTheoryEnvironment summary box: 171 constants -->

The hole's statement is the part left, for every *n*:

```wl
Information[TypeTheoryTerm[BothZero, partial], "Holes"][BothZero][[1, "Statement"]]
```

<!-- => ∀_n∶ℕ 0 + n == n -->

---

The tactic `"Hole"` closes a goal with a hole:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n && 0 + n == n], {
    TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Constructor"], TypeTheoryTactic["Reflexivity"], TypeTheoryTactic["Hole", "zero plus n"]
}]
```

<!-- => Proof complete with 1 hole -->

The theorem declared with the proof has the hole:

```wl
Take[Keys[TypeTheoryEnvironment[{TypeTheoryTheorem[BothZeroByTactics, proof]}]], -2]
```

<!-- => {TypeTheoryHole[BothZeroByTactics, 1], BothZeroByTactics} -->

## Properties and Relations

A theorem with a hole, and a theorem proved from it:

```wl
uses = TypeTheoryEnvironment[{
	TypeTheoryTheorem[AllZero, ForAll[{Typed[n, Naturals]}, n == 0], TypeTheoryHole["a claim left open"]],
	TypeTheoryTheorem[ThreeIsZero, 3 == 0, AllZero[3]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 172 constants -->

It inherits the hole, and rests on no axiom:

```wl
{Keys[Information[TypeTheoryTerm[ThreeIsZero, uses], "Holes"]], TypeTheoryAxiomClosure[TypeTheoryTerm[ThreeIsZero, uses]]}
```

<!-- => {{AllZero}, <||>} -->

---

The theorem's declaration writes the hole as it was written:

```wl
uses[AllZero]
```

<!-- => TypeTheoryTheorem[AllZero, ∀_n∶ℕ n == 0, hole] -->

## Possible Issues

A hole stands only in a declared theorem's proof:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[TypeTheoryHole[], 1 == 1]]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A proof with goals still open is no proof; close them, with holes where a proof is left to give:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[Unfinished, TypeTheoryProof[1 == 1, {}]]}]
```

<!-- => Failure["ProofIncomplete", ...] -->
