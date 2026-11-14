---
Template: TechNote
Name: ProgramsAndProofs
Title: Programs and Proofs
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/ProgramsAndProofs
Keywords: [FunctionCompile, machine integers, MachineInteger, PackedArray, TypeTheoryFormalize, induction, Gauss, Nicomachus, closed form, program verification, overflow]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TypeTheoryIntroduction, TheWolframLanguage]
---

A Wolfram Language function has three readings. The Wolfram Language evaluates its definitions as rules. [FunctionCompile]() compiles them to machine code over machine types, such as 64-bit integers. And [TypeTheoryFormalize]() reads the same definitions as a definition of the type theory, a function on the natural numbers, about which a theorem can be proved and checked by the kernel. This tutorial follows one small program through all three: it compiles the program, proves what it computes, and shows where the machine and the mathematics part ways.

## The Program

The triangular numbers, 1 + 2 + ... + n, by recursion, as a Wolfram Language program would define them, with a base case for 0 and one rule for every other integer:

```wl
triangular[0] = 0;
triangular[n_Integer] := n + triangular[n - 1];
triangular[100]
```

<!-- => 5050 -->

The sums of the cubes, 1 + 8 + ... + n^3, the same way:

```wl
cubes[0] = 0;
cubes[n_Integer] := n^3 + cubes[n - 1];
cubes[10]
```

<!-- => 3025 -->

And the sum of a list, by recursion on the list:

```wl
total[{}] = 0;
total[{x_, rest___}] := x + total[{rest}];
total[{3, 1, 4, 1, 5}]
```

<!-- => 14 -->

## Machine Code

[FunctionCompile]() compiles a function over machine types. The recursion is declared with [FunctionDeclaration](), its argument and its value `"MachineInteger"`, the 64-bit integers of the machine:

```wl
compiledTriangular = FunctionCompile[
    FunctionDeclaration[machineTriangular, Typed[{"MachineInteger"} -> "MachineInteger"] @ Function[n, If[n == 0, 0, n + machineTriangular[n - 1]]]],
    Function[Typed[n, "MachineInteger"], machineTriangular[n]]
]
```

<!-- => CompiledCodeFunction[...] -->

It computes what the definitions do:

```wl
compiledTriangular[10000]
```

<!-- => 50005000 -->

Gauss's closed form, n (n + 1)/2, computes the same number without the recursion, in one multiplication; compiled, it is the fast version of the program:

```wl
compiledClosedForm = FunctionCompile[Function[Typed[n, "MachineInteger"], Quotient[n (n + 1), 2]]]
```

<!-- => CompiledCodeFunction[...] -->

```wl
compiledClosedForm[10000]
```

<!-- => 50005000 -->

The sum of a list compiles over a packed array of machine integers, with a loop:

```wl
compiledTotal = FunctionCompile[Function[Typed[data, "PackedArray"::["MachineInteger", 1]], Module[{s = 0}, Do[s += x, {x, data}]; s]]]
```

<!-- => CompiledCodeFunction[...] -->

```wl
compiledTotal[Range[1000]]
```

<!-- => 500500 -->

That the closed form and the recursion agree at a few numbers is evidence, not proof. The rest of this tutorial proves it for every number.

## The Program as Mathematics

[TypeTheoryFormalize]() reads the definitions of `triangular` as a definition of the type theory: the base case for 0 and the rule for `n - 1` are a recursion on the natural numbers, by [InductiveRecursor]():

```wl
TypeTheoryFormalize[triangular]
```

<!-- => {definition triangular := ...} -->

An environment with the three programs, each a definition the kernel has checked:

```wl
programs = TypeTheoryEnvironment[Join[TypeTheoryFormalize[triangular], TypeTheoryFormalize[cubes], TypeTheoryFormalize[total]]]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

Each is a function on the natural numbers, or on lists of them:

```wl
TypeTheoryType[triangular, programs]
```

<!-- => ℕ → ℕ -->

```wl
TypeTheoryType[total, programs]
```

<!-- => {ℕ} → ℕ -->

The kernel computes them, as the Wolfram Language does:

```wl
NormalForm[TypeTheoryTerm[triangular[100], programs]]
```

<!-- => 5050 -->

## Gauss's Formula

The statement that the closed form is right, for every natural number n:

```wl
gaussStatement = TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, 2 triangular[n] == n (n + 1)], programs]
```

<!-- => ∀_n∶ℕ 2 triangular[n] == n (n + 1) -->

The proof is by induction on n, so the proof introduces n and splits it into its two cases, 0 and k + 1:

```wl
proof = TypeTheoryProof[gaussStatement, {"Introduce"[n], "Induction"[n]}]
```

<!-- => Proof, 2 goals: case zero ⊢ 2 triangular[0] == 0 (0 + 1); case successor ⊢ ∀_n∶ℕ 2 triangular[n] == n (n + 1) ⇒ 2 triangular[n + 1] == (n + 1) ((n + 1) + 1) -->

The tactics build one term, the proof, and each goal still open is a hole in it. So far the term is a function of n that applies the recursor of the natural numbers, with the statement as its motive and a hole for each case:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 2 triangular[n1] == n1 (n1 + 1), ?1, ?2, n] -->

At 0, the definition computes, and both sides are 0:

```wl
proof = TypeTheoryTactic["RewriteRepeated", triangular][proof]
```

<!-- => Proof, 1 goal: case successor ⊢ ∀_n∶ℕ 2 triangular[n] == n (n + 1) ⇒ 2 triangular[n + 1] == (n + 1) ((n + 1) + 1) -->

The first hole is now a proof by reflexivity:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 2 triangular[n1] == n1 (n1 + 1), equalityReflexivity[2 0], ?1, n] -->

At k + 1, the definition unfolds once, triangular[k + 1] is (k + 1) + triangular[k], and the induction hypothesis `ih` gives 2 triangular[k]:

```wl
proof = TypeTheoryTactic["RewriteRepeated", triangular][TypeTheoryTactic["Introduce", k, ih][proof]]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ 2 ((k + 1) + triangular[k]) == (k + 1) ((k + 1) + 1) -->

The second case is now a function of k and of the hypothesis, with the hole inside:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 2 triangular[n1] == n1 (n1 + 1), equalityReflexivity[2 0], (k ∶ ℕ) (ih ∶ 2 triangular[k] == k (k + 1)) ↦ ?1, n] -->

What is left is algebra with the hypothesis: twice the left side is 2 (k + 1) + k (k + 1), which is (k + 1) (k + 2). `"PolynomialReduce"` finds the combination of the hypothesis that proves it:

```wl
proof = TypeTheoryTactic["PolynomialReduce"][proof]
```

<!-- => Proof complete -->

The term is whole. `"PolynomialReduce"` filled the last hole with the algebra written out: the laws of arithmetic, `"additionCommutativity"`, `"multiplicationDistributivityLeft"` and the others, joined by `"equalityTransitivity"` and applied inside a sum or a product by `"equalityCongruence"`, down to the hypothesis `ih`:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 2 triangular[n1] == n1 (n1 + 1), equalityReflexivity[2 0], (k ∶ ℕ) (ih ∶ 2 triangular[k] == k (k + 1)) ↦ equalityTransitivity[equalityTransitivity[equalitySymmetry[additionSubtractionCancellation[2 ((k + 1) + triangular[k]), 1 (k (k + 1))]], equalityCongruence[(…, ih], …], …], n] -->

That term is all there is to the proof: the tactics are only how it was written. [TypeTheoryProofTree]() reads it as a derivation, each part of the term a rule: the induction over its two cases, and under the second the 200 steps of the algebra:

```wl
tree = TypeTheoryProofTree[proof];
Counts[Cases[tree, TypeTheoryProofTree[rule_, __] :> rule, {0, Infinity}]]
```

<!-- => <|"equalityReflexivity" -> 1, "additionSubtractionCancellation" -> 2, "equalitySymmetry" -> 34, "additionCommutativity" -> 9, "equalityCongruence" -> 48, "additionAssociativity" -> 10, "equalityTransitivity" -> 61, ..., "Assumption" -> 1, "ImpliesIntro" -> 1, "ForAllIntro" -> 2, "Induction" -> 1|> -->

The kernel checks the proof again when the theorem is declared:

```wl
proved = TypeTheoryEnvironment[programs, TypeTheoryTheorem[GaussFormula, proof]];
proved[GaussFormula]
```

<!-- => theorem GaussFormula : ∀_n∶ℕ 2 triangular[n] == n (n + 1) -->

So `compiledClosedForm`, which computes `Quotient[n (n + 1), 2]`, gives `triangular[n]` for every n: n (n + 1) is even, twice `triangular[n]`, and its quotient by 2 is exact.

## The Algebra by Hand

Most of the 210 rules are the tactic's bookkeeping: `"PolynomialReduce"` proves the algebra by a general method, which normalizes both sides. By hand, the algebra is five equations. The proof starts again, with its tactics as a list, and stops at the goal that `"PolynomialReduce"` closed:

```wl
byHand = TypeTheoryProof[gaussStatement, {"Introduce"[n], "Induction"[n], "RewriteRepeated"[triangular], "Introduce"[k, ih], "RewriteRepeated"[triangular]}]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ 2 ((k + 1) + triangular[k]) == (k + 1) ((k + 1) + 1) -->

First, 2 distributes over the sum. The law is a theorem of the prelude:

```wl
programs["multiplicationDistributivityLeft"]
```

<!-- => theorem multiplicationDistributivityLeft : ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a (b + c) == a b + a c -->

Applied to 2, k + 1 and `triangular[k]`, it is an equation with the left side of the goal on its left. `"Rewrite"` replaces the left side of an equation by its right side, wherever it is in the goal:

```wl
byHand = TypeTheoryTactic["Rewrite", "multiplicationDistributivityLeft"[2, k + 1, triangular[k]]][byHand]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ 2 (k + 1) + 2 triangular[k] == (k + 1) ((k + 1) + 1) -->

In the term, a rewrite is the recursor of equality, which carries a statement along an equation. Its motive, a function of y, says that the goal with y in place of the left side implies the goal as it was. Where y is the left side itself, that is the identity p ↦ p, and the equation takes y to its right side. So the recursor turns a proof of the new goal, the hole, into a proof of the old one:

```wl
byHand["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 2 triangular[n1] == n1 (n1 + 1), equalityReflexivity[2 0], (k ∶ ℕ) (ih ∶ 2 triangular[k] == k (k + 1)) ↦ Equal_rec[ℕ, 2 ((k + 1) + triangular[k]), (y ∶ ℕ) (t ∶ 2 ((k + 1) + triangular[k]) == y) ↦ (y == (k + 1) ((k + 1) + 1) ⇒ 2 ((k + 1) + triangular[k]) == (k + 1) ((k + 1) + 1)), (p ∶ 2 ((k + 1) + triangular[k]) == (k + 1) ((k + 1) + 1)) ↦ p, 2 (k + 1) + 2 triangular[k], multiplicationDistributivityLeft[2, k + 1, triangular[k]], ?1], n] -->

Second, the hypothesis is an equation too, with 2 triangular[k] on its left, and it rewrites the same way. After it `triangular` is gone, and what is left is arithmetic:

```wl
byHand = TypeTheoryTactic["Rewrite", ih][byHand]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ 2 (k + 1) + k (k + 1) == (k + 1) ((k + 1) + 1) -->

Third, the common factor k + 1 comes out. Distributivity on the other side, `"multiplicationDistributivityRight"[2, k, k + 1]`, is the equation (2 + k) (k + 1) == 2 (k + 1) + k (k + 1). The left side of the goal is on its right, so `"equalitySymmetry"` turns the equation round first:

```wl
byHand = TypeTheoryTactic["Rewrite", "equalitySymmetry"["multiplicationDistributivityRight"[2, k, k + 1]]][byHand]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ (2 + k) (k + 1) == (k + 1) ((k + 1) + 1) -->

Fourth, the factors swap:

```wl
byHand = TypeTheoryTactic["Rewrite", "multiplicationCommutativity"[2 + k, k + 1]][byHand]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ (k + 1) (2 + k) == (k + 1) ((k + 1) + 1) -->

Fifth, the terms of 2 + k swap:

```wl
byHand = TypeTheoryTactic["Rewrite", "additionCommutativity"[2, k]][byHand]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ (k + 1) (k + 2) == (k + 1) ((k + 1) + 1) -->

The two sides are now one number written in two ways: k + 2 and (k + 1) + 1 are both the second successor of k, since addition is defined by recursion on its second argument. No law is needed for that. `"Reflexivity"` proves an equation whose sides compute to the same term:

```wl
byHand = TypeTheoryTactic["Reflexivity"][byHand]
```

<!-- => Proof complete -->

The derivation has 27 rules where the tactic's has 210: the five equations, each under one recursor of equality with its identity, an assumption under an implication, inside the same induction:

```wl
Counts[Cases[TypeTheoryProofTree[byHand], TypeTheoryProofTree[rule_, __] :> rule, {0, Infinity}]]
```

<!-- => <|"equalityReflexivity" -> 2, "Assumption" -> 6, "ImpliesIntro" -> 6, "multiplicationDistributivityLeft" -> 1, "multiplicationDistributivityRight" -> 1, "equalitySymmetry" -> 1, "multiplicationCommutativity" -> 1, "additionCommutativity" -> 1, InductiveRecursor[Equal] -> 5, "ForAllIntro" -> 2, "Induction" -> 1|> -->

The five equations can also be joined directly, in a term with no tactic. `"equalityTransitivity"` joins two equations end to end, and `"equalityCongruence"` applies a function to both sides of one: that is how the hypothesis reaches the second term of 2 (k + 1) + x, and the last equation the second factor of (k + 1) x. Each of the five steps is one line of the chain:

```wl
chain = TypeTheoryTerm[
    Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
        Function[{Typed[m, NonNegativeIntegers]}, 2 triangular[m] == m (m + 1)],
        "equalityReflexivity"[0],
        Function[{Typed[k, NonNegativeIntegers], Typed[ih, 2 triangular[k] == k (k + 1)]},
            "equalityTransitivity"[
                "multiplicationDistributivityLeft"[2, k + 1, triangular[k]],
                "equalityTransitivity"[
                    "equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, 2 (k + 1) + x], ih],
                    "equalityTransitivity"[
                        "equalitySymmetry"["multiplicationDistributivityRight"[2, k, k + 1]],
                        "equalityTransitivity"[
                            "multiplicationCommutativity"[2 + k, k + 1],
                            "equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, (k + 1) x], "additionCommutativity"[2, k]]
                        ]
                    ]
                ]
            ]
        ],
        n
    ]],
    programs
]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(m ∶ ℕ) ↦ 2 triangular[m] == m (m + 1), equalityReflexivity[0], (k ∶ ℕ) (ih ∶ 2 triangular[k] == k (k + 1)) ↦ equalityTransitivity[multiplicationDistributivityLeft[2, k + 1, triangular[k]], equalityTransitivity[equalityCongruence[(x ∶ ℕ) ↦ 2 (k + 1) + x, ih], equalityTransitivity[equalitySymmetry[multiplicationDistributivityRight[2, k, k + 1]], equalityTransitivity[multiplicationCommutativity[2 + k, k + 1], equalityCongruence[(x ∶ ℕ) ↦ (k + 1) x, additionCommutativity[2, k]]]]]], n] -->

The kernel computes what the chain leaves out: that `triangular[k + 1]` is (k + 1) + triangular[k], and that k + 2 is (k + 1) + 1. It accepts the chain as a proof of the statement:

```wl
TypeTheoryCheck[chain, gaussStatement]
```

<!-- => Success["TypeChecked", ...] -->

Its derivation has 17 rules:

```wl
Counts[Cases[TypeTheoryProofTree[chain], TypeTheoryProofTree[rule_, __] :> rule, {0, Infinity}]]
```

<!-- => <|"equalityReflexivity" -> 1, "multiplicationDistributivityLeft" -> 1, "Assumption" -> 1, "equalityCongruence" -> 2, "multiplicationDistributivityRight" -> 1, "equalitySymmetry" -> 1, "multiplicationCommutativity" -> 1, "additionCommutativity" -> 1, "equalityTransitivity" -> 4, "ImpliesIntro" -> 1, "ForAllIntro" -> 2, "Induction" -> 1|> -->

The three terms differ in length and in nothing else: each has the statement as its type, and the kernel takes any of them as the proof of the theorem.

## Nicomachus's Theorem

The sum of the first n cubes is the square of the n-th triangular number. Multiplied by 4, so that no division is needed, it is a statement about `cubes` alone, proved the same way:

```wl
nicomachus = TypeTheoryProof[
    ForAll[{n}, 4 cubes[n] == (n (n + 1))^2],
    programs,
    {"Introduce"[n], "Induction"[n], "RewriteRepeated"[cubes], "Introduce"[k, ih], "RewriteRepeated"[cubes], "PolynomialReduce"}
]
```

<!-- => Proof complete -->

With Gauss's formula, (n (n + 1))^2 is (2 triangular[n])^2, so `cubes[n]` is `triangular[n]^2`:

```wl
cubes[10] == triangular[10]^2
```

<!-- => True -->

## Summing in Parts

A sum computed in parts, each part summed on its own and the results added, is the sum of the whole: the total of a joined list is the sum of the totals. This is what lets a sum be split across chunks of an array, or across processors:

```wl
joinStatement = TypeTheoryTerm[ForAll[{Typed[a, {NonNegativeIntegers}], Typed[b, {NonNegativeIntegers}]}, total[Join[a, b]] == total[a] + total[b]], programs]
```

<!-- => ∀_a∶{ℕ} ∀_b∶{ℕ} total[Join[a, b]] == total[a] + total[b] -->

The proof is by induction on the first list. On the empty list, `"RewriteRepeated"` unfolds [Join]() and `total`, and `"Ring"` closes 0 + total[b] == total[b]. On a list with a first element x, [Join]() unfolds to put x in front of Join[rest, b], and `total` to x plus the total of that; the induction hypothesis `ih` rewrites total[Join[rest, b]], and what is left is the associativity of addition:

```wl
TypeTheoryProof[joinStatement, {
    "Introduce"[a, b], "Induction"[a],
    "RewriteRepeated"[total, Join], "Ring",
    "Introduce"[x, rest, ih], "RewriteRepeated"[total, Join], "Rewrite"[ih], "Ring"
}]
```

<!-- => Proof complete -->

The compiled sum, run on a million machine integers in ten chunks, gives the sum of the whole, as the theorem says it must:

```wl
data = RandomInteger[1000, 10^6];
Total[compiledTotal /@ Partition[data, 10^5]] == compiledTotal[data]
```

<!-- => True -->

## Where the Machine Stops

The theorems are about the natural numbers, which have no largest element; `"MachineInteger"` is a 64-bit integer, whose largest value is 2^63 - 1. The closed form multiplies before it divides, so n (n + 1) passes that bound when n is about 3 * 10^9, long before the triangular number itself does. Up to there, the compiled code is exact:

```wl
compiledClosedForm[3037000499]
```

<!-- => 4611686016981624750 -->

Past it, the multiplication overflows, the compiled code stops with an error, and the Wolfram Language evaluates the function again with its own integers, which have no bound:

```wl
compiledClosedForm[2^32]
```

<!-- => 9223372039002259456, with CompiledCodeFunction::uncomp -->

The theorem does not say that the compiled code is fast or that it does not overflow: it says what the program computes wherever the machine computes it. Where that is, is a theorem of its own, about the code the compiler runs.

## The Machine's Theorem

In the environment of the machine integers, [TypeTheoryFormalize]() reads the compiler's typed code of a definition: its steps, each an operation of the machine, which leaves the typed code with a [Failure]() where the machine would overflow. The closed form is a step for n + 1, one for the product and one for the quotient:

```wl
closedForm[n_Integer] := Quotient[n (n + 1), 2];
machine = TypeTheoryEnvironment["Machine"];
compiled = TypeTheoryFormalize[closedForm, machine]
```

<!-- => {definition closedForm : Integer64 → (Integer64 | Failure) := (n∶Integer64) ↦ confirmBind[machinePlus[n〚"integer"〛, 1], (t3∶Integer64) ↦ confirmBind[machineTimes[n〚"integer"〛, t3〚"integer"〛], (t4∶Integer64) ↦ machineQuotient[t4〚"integer"〛, 2]]]} -->

A machine integer is an integer with a proof that it is in the range of 64 bits, and `n["integer"]` is the integer of the machine integer `n`. The machine's operations take integers: `"machinePlus"[x, y]` is the machine integer of the exact sum x + y where that is in range, and the leave `Failure["IntegerOverflow", <||>]` where it is not, the type `"Integer64" | Failure`; `"confirmBind"` gives the next step the machine integer, or passes the leave on. The machine result of an exact integer is `"machineResult"`, of which `"machinePlus"[x, y]` is `"machineResult"[x + y]`. A machine result computes its integer first: a machine value is one 64-bit number, so it holds that number, the class of one pair of literals, and not the sum or the product it came from.

At 3037000500 it leaves, as the compiled code does:

```wl
closedForms = TypeTheoryEnvironment[machine, compiled];
TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[3037000500], closedForm], closedForms]]]
```

<!-- => Failure["IntegerOverflow", <||>] -->

That it never leaves below is the theorem. Its bounds are the program's own: the argument, n + 1 and the quotient are below 2^63 where n <= 3037000499, and so is the product, by `"NonlinearArithmetic"`, since 2^63 - 1 - n (n + 1) is (3037000499 - n) times 3037000500 + n plus a positive number:

```wl
bounds = TypeTheoryEnvironment[closedForms, {
    TypeTheoryTheorem["argumentBound", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 3037000499, n < 9223372036854775808]], closedForms, {"Introduce"[n, h], "LinearArithmetic"}]],
    TypeTheoryTheorem["successorBound", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 3037000499, n + 1 < 9223372036854775808]], closedForms, {"Introduce"[n, h], "LinearArithmetic"}]],
    TypeTheoryTheorem["pronicBound", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 3037000499, n (n + 1) < 9223372036854775808]], closedForms, {"Introduce"[n, h], "NonlinearArithmetic"}]]
}];
bounds = TypeTheoryEnvironment[bounds, {TypeTheoryTheorem["quotientBound",
    ForAll[{Typed[n, NonNegativeIntegers], Typed[h, n <= 3037000499]}, Quotient[n (n + 1), 2] < 9223372036854775808],
    Function[{Typed[n, NonNegativeIntegers], Typed[h, n <= 3037000499]}, "lessEqualTransitivity"["lessEqualSuccessor"["quotientLessEqual"[n (n + 1), 2]], "pronicBound"[n, h]]]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 386 constants -->

The theorem: for every n <= 3037000499, the typed code at the machine integer n is the machine integer Quotient[n (n + 1), 2], never the leave. The proof is a chain of equations, one for each step of the typed code, and the kernel computes the code between them:

- the argument is a machine integer, by `"machineResultOfNatural"`, so the first `"confirmBind"` passes it on;
- n + 1 is in range by `"successorBound"`, so `"machineResultInRange"` makes its step a machine integer;
- the product of the integers n and n + 1 is the integer of the natural number n (n + 1), by `"integerOfNaturalMultiplication"`, which is in range by `"pronicBound"`;
- the divisor 2 is not 0 by computation, and the integers' quotient of natural numbers is theirs, by `"integerQuotientOfNatural"`, in range by `"quotientBound"`.

```wl
neverDeclines = TypeTheoryProof[
    ForAll[{Typed[n, NonNegativeIntegers], Typed[h, n <= 3037000499]},
        "confirmBind"["machineResult"["integerOfNatural"[n]], closedForm] ==
            Typed["left"["subtype"["integerOfNatural"[Quotient[n (n + 1), 2]], "naturalInteger64Range"[Quotient[n (n + 1), 2], "quotientBound"[n, h]]]], "Integer64" | Failure]
    ],
    bounds,
    {"Introduce"[n, h], "Exact"[
        "equalityTransitivity"[
            "equalityCongruence"[Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, closedForm]], "machineResultOfNatural"[n, "argumentBound"[n, h]]],
            "equalityTransitivity"[
                "equalityCongruence"[
                    Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t3, "Integer64"]}, "confirmBind"["machineTimes"["integerOfNatural"[n], t3["integer"]], Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4["integer"], 2]]]]]],
                    "machineResultInRange"["integerOfNatural"[n] + 1, "naturalInteger64Range"[n + 1, "successorBound"[n, h]]]
                ],
                "equalityTransitivity"[
                    "equalityCongruence"[
                        Function[{Typed[x, Integers]}, "confirmBind"["machineResult"[x], Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4["integer"], 2]]]],
                        "equalitySymmetry"["integerOfNaturalMultiplication"[n, n + 1]]
                    ],
                    "equalityTransitivity"[
                        "equalityCongruence"[
                            Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4["integer"], 2]]]],
                            "machineResultOfNatural"[n (n + 1), "pronicBound"[n, h]]
                        ],
                        "equalityTransitivity"[
                            "equalityCongruence"[Function[{Typed[x, Integers]}, "machineResult"[x]], "integerQuotientOfNatural"[n (n + 1), 1]],
                            "machineResultOfNatural"[Quotient[n (n + 1), 2], "quotientBound"[n, h]]
                        ]
                    ]
                ]
            ]
        ]
    ]}
]
```

<!-- => Proof complete -->

A machine integer's value is an integer, a class of pairs of natural numbers, and two classes are the same integer where their pairs are related, which computation alone does not always show: n - 1 is the class of (n, 1), not of (n - 1, 0). So a theorem about the machine states the integers it computes, as this one does with the integer of a natural number, and `"Reflexivity"` does not prove that compiled code with a subtraction gives a literal: [The Integers](paclet:WolframInstitute/TypeTheory/tutorial/TheIntegers) shows the two classes of -3 that only `"quotientSoundness"` makes equal.

It rests on the integers' quotient axiom alone, as every theorem about the integers does:

```wl
TypeTheoryAxiomClosure[neverDeclines]
```

<!-- => <|"quotientSoundness" -> "Proposition"|> -->

So the compiled closed form never leaves its machine code for n <= 3037000499, and computes Quotient[n (n + 1), 2] there; at 3037000500 it leaves, and the Wolfram Language computes the call exactly instead.

## The Recursion on the Machine

The recursion has typed code too. A typed entry leaves where its recursion passes its bound, 4096 levels for a compiled definition, so the meaning of a function that calls itself takes first the levels left, a natural number: each call of itself is a level, and where none is left it leaves. The recursion of `compiledTriangular`, as a definition, beside the program `triangular` as a recursion on the natural numbers:

```wl
machineTriangular[n_Integer] := If[n == 0, 0, n + machineTriangular[n - 1]];
recursions = TypeTheoryEnvironment[bounds, Join[
    TypeTheoryFormalize[triangular, bounds, "Meaning" -> "Function", "Type" -> (NonNegativeIntegers -> NonNegativeIntegers)],
    TypeTheoryFormalize[machineTriangular, bounds]
]]
```

<!-- => TypeTheoryEnvironment summary box: 388 constants -->

Its type has the levels first:

```wl
TypeTheoryType[TypeTheoryTerm[machineTriangular, recursions]]
```

<!-- => ℕ → Integer64 → (Integer64 | Failure) -->

At 20 it needs 21 levels, one for each call down to 0, and with 20 it leaves:

```wl
TypeTheoryExpression[NormalForm[TypeTheoryTerm[{"confirmBind"["machineResult"[20], Typed[m, "Integer64"] |-> machineTriangular[21, m]], "confirmBind"["machineResult"[20], Typed[m, "Integer64"] |-> machineTriangular[20, m]]}, recursions]]]
```

<!-- => {210, Failure["RecursionLimit", <||>]} -->

The theorem: with more levels than n, and wherever `triangular[n]` fits a machine integer, the compiled recursion at a machine integer whose value is n is the machine integer of `triangular[n]`: it never leaves, and it computes the program. Four facts of arithmetic first:

```wl
recursions = TypeTheoryEnvironment[recursions, {
    TypeTheoryTheorem["notLessZero", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n < 0, False]], recursions, {"Introduce"[n, h], "LinearArithmetic"}]],
    TypeTheoryTheorem["lessOfSuccessors", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[l, NonNegativeIntegers]}, Implies[n + 1 < l + 1, n < l]], recursions, {"Introduce"[n, l, h], "LinearArithmetic"}]],
    TypeTheoryTheorem["sumBoundsRest", TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[(a + 1) + t < u, t < u]], recursions, {"Introduce"[a, t, u, h], "LinearArithmetic"}]],
    TypeTheoryTheorem["sumBoundsIndex", TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[(a + 1) + t < u, a < u]], recursions, {"Introduce"[a, t, u, h], "LinearArithmetic"}]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 392 constants -->

The proof is by induction on n, and in each case by cases on the levels. With no level, n < 0 is absurd. At 0 with a level, the test is true and the value is the machine integer 0. At k + 1 with a level, the test is false; k is a machine integer, since it is below `triangular[k + 1]`; the call of itself is the induction hypothesis at that machine integer, with a level less; and the sum is `triangular[k + 1]`, which fits. The argument is any machine integer whose value equals n as an integer, because the recursion's own argument, (k + 1) - 1, is the class of (k + 1, 1): it is the integer k by `"integerOfNaturalPredecessor"`, not by computation.

```wl
recursionComputes = TypeTheoryProof[
    ForAll[{Typed[n, NonNegativeIntegers], Typed[levels, NonNegativeIntegers], Typed[m, "Integer64"]},
        Implies[n < levels, Implies[triangular[n] < 9223372036854775808, Implies[m["integer"] == "integerOfNatural"[n],
            Exists[{Typed[v, "Integer64"]}, machineTriangular[levels, m] == Typed["left"[v], "Integer64" | Failure] && v["integer"] == "integerOfNatural"[triangular[n]]]]]]],
    recursions,
    {
        "Introduce"[n], "Induction"[n], "Introduce"[levels], "Induction"[levels],
        "Introduce"[m, h], "Exact"["falseElimination"["notLessZero"[0, h]]],
        "Introduce"[l, ihl, m, h, b, e],
        "Exact"["existsIntroduction"[
            "subtype"["integerOfNatural"[triangular[0]], "naturalInteger64Range"[triangular[0], b]],
            "andIntroduction"[
                "equalityTransitivity"[
                    "equalityCongruence"[
                        Function[{Typed[x, Integers]}, "machineIf"["integerEqual"[x, 0], "machineResult"[0], "confirmBind"["machinePlus"[x, -1], Function[{Typed[t9, "Integer64"]}, "confirmBind"[machineTriangular[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"[x, t10["integer"]]]]]]]],
                        e
                    ],
                    "machineResultOfNatural"[triangular[0], b]
                ],
                "equalityReflexivity"["integerOfNatural"[triangular[0]]]
            ]
        ]],
        "Introduce"[k, ih, levels], "Induction"[levels],
        "Introduce"[m, h], "Exact"["falseElimination"["notLessZero"[k + 1, h]]],
        "Introduce"[l, ihl, m, h, b, e],
        "Exact"[InductiveRecursor[Exists][
            Function[{w0}, Exists[{Typed[w, "Integer64"]}, machineTriangular[l + 1, m] == Typed["left"[w], "Integer64" | Failure] && w["integer"] == "integerOfNatural"[triangular[k + 1]]]],
            Function[
                {
                    Typed[v, "Integer64"],
                    Typed[hv, machineTriangular[l, "subtype"["integerOfNatural"[k], "naturalInteger64Range"[k, "sumBoundsIndex"[k, triangular[k], 9223372036854775808, b]]]] == Typed["left"[v], "Integer64" | Failure] && v["integer"] == "integerOfNatural"[triangular[k]]]
                },
                "existsIntroduction"[
                    "subtype"["integerOfNatural"[triangular[k + 1]], "naturalInteger64Range"[triangular[k + 1], b]],
                    "andIntroduction"[
                        "equalityTransitivity"[
                            "equalityCongruence"[
                                Function[{Typed[x, Integers]}, "machineIf"["integerEqual"[x, 0], "machineResult"[0], "confirmBind"["machinePlus"[x, -1], Function[{Typed[t9, "Integer64"]}, "confirmBind"[machineTriangular[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"[x, t10["integer"]]]]]]]],
                                e
                            ],
                            "equalityTransitivity"[
                                "equalityCongruence"[
                                    Function[{Typed[x, Integers]}, "confirmBind"["machineResult"[x], Function[{Typed[t9, "Integer64"]}, "confirmBind"[machineTriangular[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"["integerOfNatural"[k + 1], t10["integer"]]]]]]],
                                    "integerOfNaturalPredecessor"[k]
                                ],
                                "equalityTransitivity"[
                                    "equalityCongruence"[
                                        Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t9, "Integer64"]}, "confirmBind"[machineTriangular[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"["integerOfNatural"[k + 1], t10["integer"]]]]]]],
                                        "machineResultOfNatural"[k, "sumBoundsIndex"[k, triangular[k], 9223372036854775808, b]]
                                    ],
                                    "equalityTransitivity"[
                                        "equalityCongruence"[
                                            Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t10, "Integer64"]}, "machinePlus"["integerOfNatural"[k + 1], t10["integer"]]]]],
                                            "andEliminationLeft"[hv]
                                        ],
                                        "equalityTransitivity"[
                                            "equalityCongruence"[Function[{Typed[y, Integers]}, "machinePlus"["integerOfNatural"[k + 1], y]], "andEliminationRight"[hv]],
                                            "equalityTransitivity"[
                                                "equalityCongruence"[Function[{Typed[y, Integers]}, "machineResult"[y]], "equalitySymmetry"["integerOfNaturalAddition"[k + 1, triangular[k]]]],
                                                "machineResultOfNatural"[triangular[k + 1], b]
                                            ]
                                        ]
                                    ]
                                ]
                            ]
                        ],
                        "equalityReflexivity"["integerOfNatural"[triangular[k + 1]]]
                    ]
                ]
            ],
            ih[
                l,
                "subtype"["integerOfNatural"[k], "naturalInteger64Range"[k, "sumBoundsIndex"[k, triangular[k], 9223372036854775808, b]]],
                "lessOfSuccessors"[k, l, h],
                "sumBoundsRest"[k, triangular[k], 9223372036854775808, b],
                "equalityReflexivity"["integerOfNatural"[k]]
            ]
        ]]
    }
]
```

<!-- => Proof complete -->

```wl
TypeTheoryAxiomClosure[recursionComputes]
```

<!-- => <|"quotientSoundness" -> "Proposition"|> -->

The levels are a variable of the theorem, so it holds of a compiled definition's 4096 levels and of the deeper recursion of a program [FunctionCompile]() compiles alike: the compiled recursion computes `triangular[n]` for every n it has levels for, as long as the sum fits.

## The Loop on the Machine

A loop has typed code too. A [While]() of typed code has no bound, and a definition must end, so the meaning of a function with a loop takes fuel, a natural number: the rounds its loop may take. The sum 1 + ... + n as a loop:

```wl
whileSum[n_Integer] := Module[{s = 0, i = 1}, While[i <= n, s = s + i; i = i + 1]; s];
loops = TypeTheoryEnvironment[recursions, TypeTheoryFormalize[whileSum, recursions]]
```

<!-- => TypeTheoryEnvironment summary box: 394 constants -->

The loop is a constant of its own, `"While[whileSum]"`, by recursion on the fuel: it takes the fuel, the local it reads, n, and the locals it sets, s and i, and gives the pair of s and i it ends with, or a [Failure]():

```wl
TypeTheoryType[TypeTheoryTerm["While[whileSum]", loops]]
```

<!-- => ℕ → Integer64 → Integer64 → Integer64 → (Integer64 × Integer64 | Failure) -->

With fuel for 11 rounds the sum to 10 is 55; with 10 the loop is out of fuel, which is no value of the compiled code but the meaning given too little:

```wl
TypeTheoryExpression[NormalForm[TypeTheoryTerm[{"confirmBind"["machineResult"[10], Typed[m, "Integer64"] |-> whileSum[11, m]], "confirmBind"["machineResult"[10], Typed[m, "Integer64"] |-> whileSum[10, m]]}, loops]]]
```

<!-- => {55, Failure["OutOfFuel", <||>]} -->

A theorem about a loop is therefore about all fuel from some on. `"RewriteRepeated"` unfolds the loop by one round where its fuel is a successor, with the loop itself in the place of the next round: the test, the two steps of the body, and the pair where the test fails:

```wl
TypeTheoryProof[
    ForAll[{Typed[f, NonNegativeIntegers], Typed[n1, "Integer64"], Typed[s, "Integer64"], Typed[i, "Integer64"], Typed[b, NonNegativeIntegers], Typed[top, NonNegativeIntegers],
            Typed[hn, n1[["integer"]] == "integerOfNatural"[top]], Typed[hi, i[["integer"]] == "integerOfNatural"[b]], Typed[hle, Not[b <= top]]},
        "While[whileSum]"[f + 1, n1, s, i] == Typed["left"["pair"[s, i]], CartesianProductType["Integer64", "Integer64"] | Failure]],
    loops,
    {"Introduce"[f, n1, s, i, b, top, hn, hi, hle], "RewriteRepeated"["While[whileSum]"]}
]
```

<!-- => Proof, 1 goal: f ∶ ℕ, n1 ∶ Integer64, s ∶ Integer64, i ∶ Integer64, b ∶ ℕ, top ∶ ℕ, hn ∶ n1〚"integer"〛 == ↑top, hi ∶ i〚"integer"〛 == ↑b, hle ∶ ¬b ≤ top ⊢ machineIf[integerLessEqualQ[i〚"integer"〛, n1〚"integer"〛], confirmBind[machinePlus[s〚"integer"〛, i〚"integer"〛], (t6∶Integer64) ↦ confirmBind[machinePlus[i〚"integer"〛, 1], (t8∶Integer64) ↦ While[whileSum][f, n1, t6, t8]]], left[(s, i)]] == left[(s, i)] -->

The proof needs the order of the integers decided on natural numbers, both ways, and the machine's sum of two natural numbers whose sum fits:

```wl
loops = TypeTheoryEnvironment[loops, {
    TypeTheoryTheorem["integerLessEqualQOfNatural",
        ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies[m <= n, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "true"]],
        Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[h, m <= n]},
            InductiveRecursor[Exists][
                Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, n == m + k]] |-> "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "true",
                {Typed[k, NonNegativeIntegers], Typed[e, n == m + k]} |-> "equalitySubstitution"[
                    "equalitySymmetry"[e],
                    "equalitySubstitution"[
                        "equalitySymmetry"["integerOfNaturalAddition"[m, k]],
                        "integerLessEqualQSelfAddition"["integerOfNatural"[m], k],
                        P -> Function[{Typed[y, Integers]}, "integerLessEqualQ"["integerOfNatural"[m], y] == "true"]
                    ],
                    P -> Function[{Typed[x, NonNegativeIntegers]}, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[x]] == "true"]
                ],
                "lessEqualWitness"[m, n, h]
            ]
        ]
    ],
    TypeTheoryTheorem["integerLessEqualQNotOfNatural",
        ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies[Not[m <= n], "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "false"]],
        Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[h, Not[m <= n]]},
            InductiveRecursor[Booleans][
                Function[{Typed[b, Booleans]}, Implies["integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == b, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "false"]],
                Function[{Typed[e, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "false"]}, e],
                Function[{Typed[e, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "true"]},
                    "falseElimination"[h["integerOfNaturalLessEqual"[m, n, "integerLessEqualQTrue"["integerOfNatural"[m], "integerOfNatural"[n], e]]]]],
                "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]]
            ]["equalityReflexivity"["integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]]]]
        ]
    ],
    TypeTheoryTheorem["machinePlusOfNatural",
        ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[h, a + b < 9223372036854775808]},
            "machinePlus"["integerOfNatural"[a], "integerOfNatural"[b]] == Typed["left"["subtype"["integerOfNatural"[a + b], "naturalInteger64Range"[a + b, h]]], "Integer64" | Failure]],
        Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[h, a + b < 9223372036854775808]},
            "equalityTransitivity"[
                "equalityCongruence"[Function[{Typed[x, Integers]}, "machineResult"[x]], "equalitySymmetry"["integerOfNaturalAddition"[a, b]]],
                "machineResultOfNatural"[a + b, h]
            ]
        ]
    ]
}]
```

<!-- => TypeTheoryEnvironment summary box: 397 constants -->

And facts of arithmetic about the rounds and the bounds, each by a tactic:

```wl
loops = TypeTheoryEnvironment[loops, {
    TypeTheoryTheorem["roundContinues", TypeTheoryProof[ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), j + 1 <= k]], loops, {"Introduce"[j, d, k, e], "LinearArithmetic"}]],
    TypeTheoryTheorem["roundStops", TypeTheoryProof[ForAll[{Typed[j, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j, Not[j + 1 <= k]]], loops, {"Introduce"[j, k, e, h], "LinearArithmetic"}]],
    TypeTheoryTheorem["roundsLeft", TypeTheoryProof[ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), k == (j + 1) + d]], loops, {"Introduce"[j, d, k, e], "LinearArithmetic"}]],
    TypeTheoryTheorem["counterBound", TypeTheoryProof[ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), Implies[k + 1 < 9223372036854775808, (j + 1) + 1 < 9223372036854775808]]], loops, {"Introduce"[j, d, k, e, b], "LinearArithmetic"}]],
    TypeTheoryTheorem["commutedBound", TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[(a + 1) + t < u, t + (a + 1) < u]], loops, {"Introduce"[a, t, u, h], "LinearArithmetic"}]],
    TypeTheoryTheorem["zeroPlus", TypeTheoryProof[ForAll[{Typed[t, NonNegativeIntegers]}, t == 0 + t], loops, {"Introduce"[t], "LinearArithmetic"}]],
    TypeTheoryTheorem["zeroBound", TypeTheoryProof[0 < 9223372036854775808, loops, {"Decide"}]],
    TypeTheoryTheorem["oneBound", TypeTheoryProof[1 < 9223372036854775808, loops, {"Decide"}]],
    TypeTheoryTheorem["triangularStep", TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers]}, triangular[a] <= triangular[a + 1]], loops, {"Introduce"[a], "RewriteRepeated"[triangular], "LinearArithmetic"}]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 406 constants -->

The triangular numbers grow, so each one on the way is below the last, which fits:

```wl
loops = TypeTheoryEnvironment[loops, {
    TypeTheoryTheorem["triangularMonotone", TypeTheoryProof[ForAll[{Typed[b, NonNegativeIntegers], Typed[a, NonNegativeIntegers]}, triangular[a] <= triangular[a + b]], loops, {"Introduce"[b], "Induction"[b], "Introduce"[a], "Exact"["lessEqualReflexivity"], "Introduce"[c, ih, a], "Exact"["lessEqualTransitivity"[ih[a], "triangularStep"[a + c]]]}]]
}];
loops = TypeTheoryEnvironment[loops, {
    TypeTheoryTheorem["triangularBoundAt", TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == a + d, Implies[triangular[k] < 9223372036854775808, triangular[a] < 9223372036854775808]]], loops, {"Introduce"[a, d, k, e, b], "Rewrite"[e, "At" -> b], "Exact"["lessEqualTransitivity"["lessEqualSuccessor"["triangularMonotone"[d, a]], b]]}]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 408 constants -->

One round. Where the counter b is at most n, the loop with a unit of fuel more is the loop at the machine integers of a + b and b + 1: the round unfolds, the hypotheses rewrite the locals to the natural numbers they are, the test is true, and the two sums are machine integers. Where b is past n, the test is false and the loop gives the pair as it is:

```wl
loops = TypeTheoryEnvironment[loops, {
    TypeTheoryTheorem["whileRound", TypeTheoryProof[ForAll[{Typed[f, NonNegativeIntegers], Typed[n1, "Integer64"], Typed[s, "Integer64"], Typed[i, "Integer64"], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[top, NonNegativeIntegers],
            Typed[hn, n1[["integer"]] == "integerOfNatural"[top]], Typed[hs, s[["integer"]] == "integerOfNatural"[a]], Typed[hi, i[["integer"]] == "integerOfNatural"[b]],
            Typed[hle, b <= top], Typed[h1, a + b < 9223372036854775808], Typed[h2, b + 1 < 9223372036854775808]},
        "While[whileSum]"[f + 1, n1, s, i] == "While[whileSum]"[f, n1,
            "subtype"["integerOfNatural"[a + b], "naturalInteger64Range"[a + b, h1]],
            "subtype"["integerOfNatural"[b + 1], "naturalInteger64Range"[b + 1, h2]]]], loops, {"Introduce"[f, n1, s, i, a, b, top, hn, hs, hi, hle, h1, h2], "RewriteRepeated"["While[whileSum]"], "Rewrite"[hi], "Rewrite"[hn], "Rewrite"[hs],
        "Rewrite"["integerLessEqualQOfNatural"[b, top, hle]], "Rewrite"["machinePlusOfNatural"[a, b, h1]], "Rewrite"["machinePlusOfNatural"[b, 1, h2]], "Reflexivity"}]],
    TypeTheoryTheorem["whileStop", TypeTheoryProof[ForAll[{Typed[f, NonNegativeIntegers], Typed[n1, "Integer64"], Typed[s, "Integer64"], Typed[i, "Integer64"], Typed[b, NonNegativeIntegers], Typed[top, NonNegativeIntegers],
            Typed[hn, n1[["integer"]] == "integerOfNatural"[top]], Typed[hi, i[["integer"]] == "integerOfNatural"[b]], Typed[hle, Not[b <= top]]},
        "While[whileSum]"[f + 1, n1, s, i] == Typed["left"["pair"[s, i]], CartesianProductType["Integer64", "Integer64"] | Failure]], loops, {"Introduce"[f, n1, s, i, b, top, hn, hi, hle], "RewriteRepeated"["While[whileSum]"], "Rewrite"[hi], "Rewrite"[hn],
        "Rewrite"["integerLessEqualQNotOfNatural"[b, top, hle]], "Reflexivity"}]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 410 constants -->

The invariant: after j rounds the sum is `triangular[j]` and the counter j + 1. With d rounds left, n == j + d, and fuel above d, the loop ends with the sum `triangular[n]`. The proof is by induction on the rounds left, and in each case by cases on the fuel: without fuel its bound is absurd; with none left to do, the loop stops; with a round left, `"whileRound"` rewrites the loop to the next round, where the hypothesis of the induction applies at the counter j + 1 with a unit of fuel less:

```wl
invariant = TypeTheoryProof[
    ForAll[{Typed[top, NonNegativeIntegers], Typed[n1, "Integer64"]},
        Implies[n1[["integer"]] == "integerOfNatural"[top], Implies[triangular[top] < 9223372036854775808, Implies[top + 1 < 9223372036854775808,
            ForAll[{Typed[d, NonNegativeIntegers], Typed[j, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[s, "Integer64"], Typed[i, "Integer64"]},
                Implies[top == j + d, Implies[d < fuel, Implies[s[["integer"]] == "integerOfNatural"[triangular[j]], Implies[i[["integer"]] == "integerOfNatural"[j + 1],
                    Exists[{Typed[v, "Integer64"], Typed[w, "Integer64"]},
                        "While[whileSum]"[fuel, n1, s, i] == Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[triangular[top]]]]]]]]]]]],
    loops,
    {
        "Introduce"[top, n1, hn, bT, bN, d], "Induction"[d],
        (* no round left: without fuel the bound on it is absurd; with fuel the loop stops with s *)
        "Introduce"[j, fuel], "Induction"[fuel],
        "Introduce"[s, i, e, h], "Exact"["falseElimination"["notLessZero"[0, h]]],
        "Introduce"[f, ihf, s, i, e, h, hs, hi],
        "Exact"["existsIntroduction"[s, "existsIntroduction"[i, "andIntroduction"[
            "whileStop"[f, n1, s, i, j + 1, top, hn, hi, "roundStops"[j, top, e]],
            "equalitySubstitution"["equalitySymmetry"[e], hs, P -> Function[{Typed[x, NonNegativeIntegers]}, s[["integer"]] == "integerOfNatural"[triangular[x]]]]
        ]]]],
        (* a round left: one round, then the hypothesis of the induction at the next counter and a unit of fuel less *)
        "Introduce"[d1, ihd, j, fuel], "Induction"[fuel],
        "Introduce"[s, i, e, h], "Exact"["falseElimination"["notLessZero"[d1 + 1, h]]],
        "Introduce"[f, ihf, s, i, e, h, hs, hi],
        "Rewrite"["whileRound"[f, n1, s, i, triangular[j], j + 1, top, hn, hs, hi, "roundContinues"[j, d1, top, e],
            "commutedBound"[j, triangular[j], 9223372036854775808, "triangularBoundAt"[j + 1, d1, top, "roundsLeft"[j, d1, top, e], bT]],
            "counterBound"[j, d1, top, e, bN]]],
        "Apply"[ihd[j + 1]],
        "Exact"["roundsLeft"[j, d1, top, e]],
        "Exact"["lessOfSuccessors"[d1, f, h]],
        "Exact"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, "integerOfNatural"[x]], "additionCommutativity"[triangular[j], j + 1]]],
        "Reflexivity"
    }
]
```

<!-- => Proof complete -->

```wl
loops = TypeTheoryEnvironment[loops, {TypeTheoryTheorem["whileInvariant", invariant]}]
```

<!-- => TypeTheoryEnvironment summary box: 411 constants -->

The function starts the loop at 0 and 1 and gives the first of the pair. So for every fuel above n, wherever `triangular[n]` and n + 1 fit a machine integer, the compiled loop at a machine integer whose integer is n gives a machine integer whose integer is `triangular[n]`:

```wl
loops = TypeTheoryEnvironment[loops, {
    TypeTheoryTheorem["whileSumOfLoop", TypeTheoryProof[ForAll[{Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"], Typed[v, "Integer64"], Typed[w, "Integer64"]},
        Implies[
            "While[whileSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
                Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure],
            whileSum[fuel, n] == Typed["left"[v], "Integer64" | Failure]]], loops, {"Introduce"[fuel, n, v, w, h], "Exact"["equalityCongruence"[
        Function[{Typed[r, CartesianProductType["Integer64", "Integer64"] | Failure]},
            "confirmBind"[r, Function[{Typed[state, CartesianProductType["Integer64", "Integer64"]]}, Typed["left"[state[["first"]]], "Integer64" | Failure]]]],
        h]]}]]
}];
loops = TypeTheoryEnvironment[loops, {
    TypeTheoryTheorem["whileSumComputes",
    ForAll[{Typed[top, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"]},
        Implies[n[["integer"]] == "integerOfNatural"[top], Implies[triangular[top] < 9223372036854775808, Implies[top + 1 < 9223372036854775808, Implies[top < fuel,
            Exists[{Typed[v, "Integer64"]}, whileSum[fuel, n] == Typed["left"[v], "Integer64" | Failure] && v[["integer"]] == "integerOfNatural"[triangular[top]]]]]]]],
    Function[{Typed[top, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"], Typed[hn, n[["integer"]] == "integerOfNatural"[top]],
            Typed[bT, triangular[top] < 9223372036854775808], Typed[bN, top + 1 < 9223372036854775808], Typed[hf, top < fuel]},
        InductiveRecursor[Exists][
            Function[{Typed[t, Exists[{Typed[v, "Integer64"]}, Exists[{Typed[w, "Integer64"]},
                "While[whileSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
                    Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[triangular[top]]]]]},
                Exists[{Typed[v, "Integer64"]}, whileSum[fuel, n] == Typed["left"[v], "Integer64" | Failure] && v[["integer"]] == "integerOfNatural"[triangular[top]]]],
            Function[{Typed[v, "Integer64"], Typed[hv, Exists[{Typed[w, "Integer64"]},
                "While[whileSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
                    Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[triangular[top]]]]},
                InductiveRecursor[Exists][
                    Function[{Typed[t, Exists[{Typed[w, "Integer64"]},
                        "While[whileSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
                            Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[triangular[top]]]]},
                        Exists[{Typed[v1, "Integer64"]}, whileSum[fuel, n] == Typed["left"[v1], "Integer64" | Failure] && v1[["integer"]] == "integerOfNatural"[triangular[top]]]],
                    Function[{Typed[w, "Integer64"], Typed[hw,
                        "While[whileSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
                            Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[triangular[top]]]},
                        "existsIntroduction"[v, "andIntroduction"["whileSumOfLoop"[fuel, n, v, w, hw[["left"]]], hw[["right"]]]]],
                    hv
                ]],
            "whileInvariant"[top, n, hn, bT, bN, top, 0, fuel,
                "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]],
                "zeroPlus"[top], hf, "equalityReflexivity"["integerOfNatural"[0]], "equalityReflexivity"["integerOfNatural"[1]]]
        ]
    ]
]
}]
```

<!-- => TypeTheoryEnvironment summary box: 413 constants -->

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["whileSumComputes", loops]]
```

<!-- => <|"quotientSoundness" -> "Proposition"|> -->

The fuel is a variable of the theorem with only a lower bound, so more fuel changes nothing: the compiled loop, which takes as many rounds as it needs, computes the sum. The recursion and the loop compute the same number, the one the program was proved to compute.

A [Do]() is a loop of the same kind. The compiler keeps its counter in a local and the iterator's symbol in step with it, and the meaning reads the iterator as that counter. So the `Do` is the [While]() the compiler wrote for it:

```wl
doSum[n_Integer] := Module[{s = 0}, Do[s += i, {i, n}]; s];
counted = TypeTheoryEnvironment[loops, TypeTheoryFormalize[doSum, loops]]
```

<!-- => TypeTheoryEnvironment summary box: 415 constants -->

Its arguments are the fuel, the end and the step of the range, which it reads, and s and the counter, which it sets:

```wl
TypeTheoryType[TypeTheoryTerm["While[doSum]", counted]]
```

<!-- => ℕ → Integer64 → Integer64 → Integer64 → Integer64 → (Integer64 × Integer64 | Failure) -->

```wl
TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[10], Typed[m, "Integer64"] |-> doSum[11, m]], counted]]]
```

<!-- => 55 -->

The counter's step is a sum of the machine like any other. A `Do` whose range ends at 2^63 - 1 leaves after its last round, where the Wolfram Language's `Do` finishes, so a theorem about a `Do` carries, as `"whileSumComputes"` does for the loop above, that the end and the step add up below 2^63.
