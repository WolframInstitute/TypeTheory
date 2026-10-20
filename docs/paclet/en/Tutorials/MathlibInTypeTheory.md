---
Template: TechNote
Name: MathlibInTypeTheory
Title: Mathlib in TypeTheory
Context: WolframInstitute`TypeTheory`
ContextPath: [Wolfram`LeanLink`]
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/MathlibInTypeTheory
Keywords: [Mathlib, Lean, LeanLink, import, export, natural numbers, divisibility, notation, tactics, induction, proof checking]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude]
---

[Mathlib](https://github.com/leanprover-community/mathlib4) is the mathematical library of [Lean 4](https://lean-lang.org/), whose type theory, the Calculus of Inductive Constructions, is TypeTheory's. [LeanLink](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink), the Wolfram Language link to Lean, reads Mathlib's compiled modules, and its [LeanToTypeTheory](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink#ref/LeanToTypeTheory) imports a constant of Mathlib into a [TypeTheoryEnvironment]() together with every constant it depends on, from Mathlib and from Lean's own library. TypeTheory's kernel checks each of them again. Imported, Mathlib's definitions compute and its theorems are constants like any other, which tactics apply. This tutorial imports theorems about the natural numbers from Mathlib, gives them notation, computes with them, proves new theorems with them, and has Lean check those proofs.

## Prerequisites

LeanLink, and a checkout of Mathlib built with `lake build`:

```wl
mathlibDir = FileNameJoin[{$HomeDirectory, "src", "mathlib4"}];
mathlibReady = DirectoryQ[FileNameJoin[{mathlibDir, ".lake", "build"}]]
```

<!-- => True (when Mathlib is built) -->

## Loading Mathlib

`Mathlib.Data.Nat.Init` holds the first facts Mathlib proves about the natural numbers, before its algebra. [LeanImport](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink#ref/LeanImport) loads it, with every module it imports:

```wl
lean = If[mathlibReady, LeanImport["ProjectDir" -> mathlibDir, "Imports" -> {"Mathlib.Data.Nat.Init"}], <||>]
```

<!-- => LeanEnvironment summary box: 106418 constants -->

This is one of its theorems, as Lean writes it:

```wl
lean["Nat.sq_sub_sq"]["TypeForm"]
```

<!-- => "∀ (a b : ℕ), a ^ 2 - b ^ 2 = (a + b) * (a - b)" -->

## Importing Theorems

[LeanToTypeTheory](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink#ref/LeanToTypeTheory) imports constants into a new environment, each after the constants it mentions, and TypeTheory's kernel checks every one. Here are two theorems of Mathlib, two of Lean's own library, and Lean's greatest common divisor:

```wl
mathlib = LeanToTypeTheory[lean, {"Nat.sq_sub_sq", "Nat.dvd_add_self_right", "Nat.dvd_add", "Nat.dvd_mul_left", "Nat.gcd"}]
```

<!-- => TypeTheoryEnvironment summary box: 376 constants -->

What it holds, by kind:

```wl
Information[mathlib, "Kinds"]
```

<!-- => <|"InductiveType" -> 31, "Constructor" -> 36, "Recursor" -> 31, "Definition" -> 168, "Theorem" -> 109, "Axiom" -> 1|> -->

The theorems rest on one axiom, propositional extensionality, which Lean assumes too:

```wl
Information[mathlib, "Axioms"]
```

<!-- => {"propext"} -->

[SetTypeTheoryEnvironment]() makes it the default environment, so the terms and proofs below need not name it:

```wl
SetTypeTheoryEnvironment[mathlib]
```

<!-- => TypeTheoryEnvironment summary box: 376 constants -->

A constant keeps its Lean name, as a string. The statement of `Nat.sq_sub_sq`, as TypeTheory has checked it:

```wl
TypeTheoryCheck[TypeTheoryTerm["Nat.sq_sub_sq"]]
```

<!-- => ∀_a∶Nat ∀_b∶Nat Eq[HSub.hSub[HPow.hPow[a, OfNat.ofNat[2]], HPow.hPow[b, OfNat.ofNat[2]]], HMul.hMul[HAdd.hAdd[a, b], HSub.hSub[a, b]]] -->

## Notation

A term shows a constant applied to its arguments that are not implicit. Lean's `a + b` is `HAdd.hAdd` applied to two implicit types, an implicit result type, an instance that says how to add, and `a` and `b`, so it shows as `HAdd.hAdd[a, b]`. Definitions of [MakeBoxes]() give each of Lean's operators its notation back, here with the Wolfram Language's own operators:

```wl
MakeBoxes["Eq"[a_, b_], form_] := MakeBoxes[a == b, form];
MakeBoxes["Ne"[a_, b_], form_] := MakeBoxes[a != b, form];
MakeBoxes["Iff"[a_, b_], form_] := MakeBoxes[Equivalent[a, b], form];
MakeBoxes["And"[a_, b_], form_] := MakeBoxes[a && b, form];
MakeBoxes["LE.le"[a_, b_], form_] := MakeBoxes[a <= b, form];
MakeBoxes["HAdd.hAdd"[a_, b_], form_] := MakeBoxes[a + b, form];
MakeBoxes["HSub.hSub"[a_, b_], form_] := MakeBoxes[a - b, form];
MakeBoxes["HMul.hMul"[a_, b_], form_] := MakeBoxes[a * b, form];
MakeBoxes["HPow.hPow"[a_, b_], form_] := MakeBoxes[a^b, form];
MakeBoxes["Dvd.dvd"[a_, b_], form_] := MakeBoxes[VerticalBar[a, b], form];
MakeBoxes["OfNat.ofNat"[n_], form_] := MakeBoxes[n, form];
TypeTheoryCheck[TypeTheoryTerm["Nat.sq_sub_sq"]]
```

<!-- => ∀_a∶Nat ∀_b∶Nat a^2 - b^2 == (a + b) (a - b) -->

The notation holds wherever a term shows, as in this theorem of divisibility:

```wl
TypeTheoryCheck[TypeTheoryTerm["Nat.dvd_add_self_right"]]
```

<!-- => ∀_{m ∶ Nat} ∀_{n ∶ Nat} (m | n + m ⧦ m | n) -->

## Computing

A theorem applies to arguments like a function. Applied to 7 and 3, `Nat.sq_sub_sq` proves an equation of numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm["Nat.sq_sub_sq"[7, 3]]]
```

<!-- => 7^2 - 3^2 == (7 + 3) (7 - 3) -->

Both sides compute to 40, so the same proof proves `40 == 40`:

```wl
TypeTheoryCheck[TypeTheoryTerm["Nat.sq_sub_sq"[7, 3]], TypeTheoryTerm["Eq"[40, 40]]]
```

<!-- => Success["TypeChecked", ...] -->

The import registers Lean's natural numbers as those of the environment, with the operations Lean's kernel computes on literals, so TypeTheory's kernel computes them too, with the Wolfram Language's integers. Here is Lean's greatest common divisor of Euclid's example:

```wl
WeakHeadNormalForm[TypeTheoryTerm["Nat.gcd"[1071, 462]]]
```

<!-- => 21 -->

## Proving with Mathlib's Theorems

TypeTheory does not search for instances, so a statement that uses Lean's notation is written in Lean, which finds them, and imported. [LeanImportString](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink#ref/LeanImportString) compiles a list of sources joined with newlines, here an import and two statements, the second about a function defined by recursion:

```wl
statements = "def DividesShift : Prop := ∀ a b : ℕ, a ∣ b → a ∣ b + a ∧ a ∣ b + 2 * a

def double : ℕ → ℕ
  | 0 => 0
  | n + 1 => double n + 2

def DoubleIsTwice : Prop := ∀ n : ℕ, double n = 2 * n";
stated = If[mathlibReady, LeanImportString[{"import Mathlib.Data.Nat.Init", statements}, "ProjectDir" -> mathlibDir], <||>]
```

<!-- => LeanEnvironment summary box: 3 constants -->

With the option `"Environment"`, [LeanToTypeTheory](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink#ref/LeanToTypeTheory) adds them, and `congrArg` for later, to the environment of Mathlib's theorems, which becomes the default:

```wl
SetTypeTheoryEnvironment[LeanToTypeTheory[stated, {"DividesShift", "DoubleIsTwice", "congrArg"}, "Environment" -> mathlib]]
```

<!-- => TypeTheoryEnvironment summary box: 381 constants -->

`DividesShift` is a definition, and [TypeTheoryTactic]() `"Introduce"` unfolds it to find what to introduce. `"Apply"` with `And.intro` splits the conjunction into two goals:

```wl
proof = TypeTheoryProof["DividesShift", {
    TypeTheoryTactic["Introduce", a, b, h],
    TypeTheoryTactic["Apply", "And.intro"]
}]
```

<!-- => Proof, 2 goals: a ∶ Nat, b ∶ Nat, h ∶ a | b ⊢ a | b + a; a ∶ Nat, b ∶ Nat, h ∶ a | b ⊢ a | b + 2 a -->

The first goal is `Nat.dvd_add_self_right` read from right to left, which `Iff.mpr` does. Its numbers are implicit, and unification finds them in the goal:

```wl
proof = TypeTheoryTactic["Exact", "Iff.mpr"["Nat.dvd_add_self_right", h]][proof]
```

<!-- => Proof, 1 goal: a ∶ Nat, b ∶ Nat, h ∶ a | b ⊢ a | b + 2 a -->

A number that divides two numbers divides their sum, by `Nat.dvd_add`, and `a` divides `2 a` by `Nat.dvd_mul_left`:

```wl
proof = TypeTheoryTactic["Exact", "Nat.dvd_add"[h, "Nat.dvd_mul_left"[a, 2]]][proof]
```

<!-- => Proof complete -->

## Induction

`"Induction"` splits on a variable of Lean's natural numbers as on the prelude's, with the recursor TypeTheory generated for them:

```wl
induction = TypeTheoryProof["DoubleIsTwice", {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Induction", n]
}]
```

<!-- => Proof, 2 goals: case Nat.zero ⊢ double[0] == 2 0; case Nat.succ ⊢ ∀_n∶Nat double[n] == 2 n ⇒ double[n + 1] == 2 (n + 1) -->

Both sides of the first goal compute to 0. In the second, `double[k + 1]` computes to `double[k] + 2` and `2 (k + 1)` to `2 k + 2`, and adding 2 is applying the successor twice, so `congrArg` applies it twice to the induction hypothesis:

```wl
induction = TypeTheoryProof["DoubleIsTwice", {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Induction", n],
    TypeTheoryTactic["Reflexivity"],
    TypeTheoryTactic["Introduce", k, ih],
    TypeTheoryTactic["Exact", "congrArg"["Nat.succ", "congrArg"["Nat.succ", ih]]]
}]
```

<!-- => Proof complete -->

## Back to Lean

The finished proofs are declared as theorems, under names of TypeTheory's own, in the default environment:

```wl
proved = TypeTheoryEnvironment[{TypeTheoryTheorem[DividesShiftProof, proof], TypeTheoryTheorem[DoubleIsTwiceProof, induction]}]
```

<!-- => TypeTheoryEnvironment summary box: 383 constants -->

The theorem proved by induction:

```wl
proved[DoubleIsTwiceProof]
```

<!-- => theorem DoubleIsTwiceProof : DoubleIsTwice -->

LeanLink's [TypeTheoryToLean](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink#ref/TypeTheoryToLean) writes them as Lean source, with every argument explicit. The constants that came from Lean keep their names, and the theorems are declared under the namespace `TypeTheory`:

```wl
source = TypeTheoryToLean[proved, {DividesShiftProof, DoubleIsTwiceProof}]
```

<!-- => "-- Generated by LeanLink's TypeTheoryToLean: TypeTheory declarations, for Lean's kernel to check.\n\ntheorem TypeTheory.DividesShiftProof : @DividesShift :=\n  (fun (a : @Nat) (b : @Nat) (h : ...) => ...)\n\ntheorem TypeTheory.DoubleIsTwiceProof : @DoubleIsTwice :=\n  ..." -->

Lean compiles the source after the statements, and its kernel checks the proofs, independently of TypeTheory's:

```wl
checked = If[mathlibReady, LeanImportString[{"import Mathlib.Data.Nat.Init", statements, source}, "ProjectDir" -> mathlibDir], <||>]
```

<!-- => LeanEnvironment summary box: 5 constants -->

In Lean, the theorem has the statement it had in TypeTheory:

```wl
checked["TypeTheory.DoubleIsTwiceProof"]["TypeForm"]
```

<!-- => "DoubleIsTwice" -->

The prelude is the default again with [SetTypeTheoryEnvironment]():

```wl
SetTypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 109 constants -->

## How Much of Mathlib

Every constant of Lean's prelude, `Init.Prelude`, imports and checks, all 1,381 of them, and so do the 25 modules at the bottom of Mathlib, from the logic of `Nonempty` to folds over lists, with the 5,113 constants they depend on, in about three minutes. So do 115 modules higher up, each with every constant it depends on, 61,303 distinct constants in all, among them the real and complex numbers, the exponential and trigonometric functions, derivatives, polynomials, matrices and determinants, ideals, primes and factorizations, cardinals, simple graphs, measurable, metric and inner product spaces, normed fields, compactness and the p-adic numbers. `Real.sqrt_nonneg`, that the square root of a real number is never negative, checks with the 11,177 constants it depends on, Mathlib's construction of the real numbers among them, in under seven minutes. A proof that a decision procedure such as `omega` or `grind` writes is a term of millions of nodes written out but of a few thousand distinct ones, and the import shares them as Lean does: a proof that `grind` writes in `Mathlib.Data.Int.Init` checks, with the 2,889 constants it depends on, in a minute and a half. Lean's own kernel, written in C++, checks the same cones about 130 times faster: that of `Real.sqrt_nonneg` in three seconds. LeanLink's tutorial [Checking Mathlib with TypeTheory](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink#tutorial/CheckingMathlib) checks a whole module and lists what TypeTheory does not check yet.
