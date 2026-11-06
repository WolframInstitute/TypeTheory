---
Template: Symbol
Name: TypeTheoryAxiomClosure
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryAxiomClosure
Keywords: [axioms, dependencies, print axioms, trust, signature, rewrite rule, closure, holes, classical logic, choice]
SeeAlso: [TypeTheoryAxiom, TypeTheoryCheck, TypeTheoryTerm, TypeTheoryProof, TypeTheoryEnvironment, TypeTheoryRewriteRule, TypeTheoryHole]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryAxiomClosure]()[*term*]</code> gives the axioms the [TypeTheoryTerm]() *term* rests on, as <code><\|*axiom* -> *kind*, ...\|></code>.

<code>[TypeTheoryAxiomClosure]()[*proof*]</code> gives the axioms the finished [TypeTheoryProof]() *proof* rests on.

## Details & Options

- The closure follows every constant *term* mentions, then the constants in the type and value of each of those, as Lean's `#print axioms` does. A constructor or recursor leads to its inductive type, and an inductive type to its constructors.
- A constant on its own, such as <code>[TypeTheoryTerm]()["excludedMiddle"]</code>, rests on what its declaration uses: the proof of a theorem and the value of a definition, not only the statement.
- An axiom is `"Proposition"` when its type is a proposition, such as `"propositionalExtensionality"`, and `"Signature"` otherwise: an axiom of a type, such as a constant of [NonNegativeIntegers]() or a type of its own, which a theorem holds for whatever it stands for, as for a variable. `"choice"`, whose value is an element of a type, is a signature by this rule, and so is every axiom under rules without Prop.
- A rewrite rule of a constant the closure reaches is listed as `"RewriteRule"`: the kernel computes with it, so it is trusted as an axiom is.
- A theorem that rests on no axiom has the closure <code><\|\|></code>.
- A hole, <code>[TypeTheoryHole]()[*theorem*, *k*]</code>, is no axiom and is left out; <code>[Information]()[*term*, "Holes"]</code> gives the holes *term* rests on, those of the theorems it uses included.
- A finished proof rests on its own term, implicit arguments included. A proof with goals left gives a [Failure]() tagged `"ProofIncomplete"`.
- <code>[Information]()[*term*, "AxiomClosure"]</code> gives the same, and <code>[Information]()[*term*, "Constants"]</code> gives the constants the type and the value of *term* mention, those of a constant's declaration for a constant.

## Basic Examples

Excluded middle rests on the three axioms Lean's proof of it uses:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["excludedMiddle"]]
```

<!-- => <|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|> -->

---

A theorem proved by computation rests on none:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["equalitySymmetry"]]
```

<!-- => <||> -->

---

Function extensionality rests on the soundness of quotients:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["functionExtensionality"]]
```

<!-- => <|"quotientSoundness" -> "Proposition"|> -->

## Scope


An axiom rests on itself:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["propositionalExtensionality"]]
```

<!-- => <|"propositionalExtensionality" -> "Proposition"|> -->

---

Choice gives an element of a type, so it is a signature:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["choice"]]
```

<!-- => <|"choice" -> "Signature"|> -->

---

An environment with an axiom of a type and an axiom of a proposition:

```wl
signed = TypeTheoryEnvironment[{TypeTheoryAxiom[Origin, Naturals], TypeTheoryAxiom[OriginPositive, 0 < Origin]}]
```

<!-- => TypeTheoryEnvironment summary box: 232 constants -->

A term with the constant `Origin` rests on it as a signature:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Origin + 1, signed]]
```

<!-- => <|Origin -> "Signature"|> -->

The axiom about `Origin` is a proposition, and its statement mentions `Origin`:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[OriginPositive, signed]]
```

<!-- => <|OriginPositive -> "Proposition", Origin -> "Signature"|> -->

---

A finished proof rests on the axioms of its own term, implicit arguments included, which the term it reads back as leaves out:

```wl
TypeTheoryAxiomClosure[TypeTheoryProof[2 + 2 == 4, {"Decide"}]]
```

<!-- => <||> -->

---

A proof of excluded middle for every proposition, by the theorem:

```wl
classical = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]]}, a || ! a], {"Introduce"[a], TypeTheoryTactic["Apply", "excludedMiddle"]}]
```

<!-- => Proof complete -->

It rests on the axioms of the theorem:

```wl
TypeTheoryAxiomClosure[classical]
```

<!-- => <|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|> -->

---

A theorem of the integers, a quotient, rests on the soundness of quotients:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["integerAdditionCommutativity", "Integers"]]
```

<!-- => <|"quotientSoundness" -> "Proposition"|> -->

---

Homotopy type theory's circle is given by axioms, and its induction principle computes on the base point by a rewrite rule:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["circleInduction", "HomotopyTypeTheory"]]
```

<!-- => <|"circleInduction" -> "Signature", Circle -> "Signature", "circleBase" -> "Signature", "circleLoop" -> "Signature", "circleInductionBase" -> "RewriteRule"|> -->

---

Univalence is an axiom there, a signature, since those rules have no Prop:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["univalence", "HomotopyTypeTheory"]]
```

<!-- => <|"univalence" -> "Signature"|> -->

---

The evaluation of the Wolfram Language is an axiom of its environment, which the term names:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[ExpressionEvaluate]]
```

<!-- => <|ExpressionEvaluate -> "Signature"|> -->

## Properties and Relations

[Information]() gives the same closure:

```wl
Information[TypeTheoryTerm["excludedMiddle"], "AxiomClosure"] === TypeTheoryAxiomClosure[TypeTheoryTerm["excludedMiddle"]]
```

<!-- => True -->

---

The constants a statement mentions; its type, Prop, mentions none:

```wl
Information[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]], "Constants"]
```

<!-- => {ℤ_≥0, Equal, Plus} -->

---

The constants of a theorem are those of its statement and its proof, the closure's first step:

```wl
Information[TypeTheoryTerm[TwoPlusTwo, TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]], "Constants"]
```

<!-- => {Equal, ℤ_≥0, Plus, "equalityReflexivity"} -->

---

A theorem left as a hole:

```wl
later = TypeTheoryEnvironment[{TypeTheoryTheorem[Later, ForAll[{Typed[k, NonNegativeIntegers]}, k + 0 == k], TypeTheoryHole["by induction"]]}]
```

<!-- => TypeTheoryEnvironment summary box: 232 constants -->

A hole is no axiom, so it is left out of the closure:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Later, later]]
```

<!-- => <||> -->

[Information]() gives the holes:

```wl
Information[TypeTheoryTerm[Later, later], "Holes"]
```

<!-- => <|Later -> {<|"Hole" -> TypeTheoryHole[Later, 1], "Statement" -> ∀_k∶ℕ k + 0 == k, "Annotation" -> <|"Citation" -> "by induction"|>|>}|> -->

---

Every constant of the rationals rests on Lean's three axioms at most:

```wl
Union @@ Map[name |-> Keys[TypeTheoryAxiomClosure[TypeTheoryTerm[name, "Rationals"]]], Keys[TypeTheoryEnvironment["Rationals"]]]
```

<!-- => {"choice", "propositionalExtensionality", "quotientSoundness", ExpressionEvaluate} -->

## Possible Issues

The closure of a constant includes the axioms its proof uses, not only its statement's: the statement of excluded middle mentions no axiom.

```wl
TypeTheoryAxiomClosure[TypeTheoryType["excludedMiddle"]]
```

<!-- => <||> -->

---

A proof with goals left has no term yet:

```wl
TypeTheoryAxiomClosure[TypeTheoryProof[2 + 2 == 4]]
```

<!-- => Failure["ProofIncomplete", ...] -->

---

The argument is a [TypeTheoryTerm]() or a [TypeTheoryProof](); a name on its own is left as it is:

```wl
TypeTheoryAxiomClosure["excludedMiddle"]
```

<!-- => TypeTheoryAxiomClosure["excludedMiddle"] -->
