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

<!-- => Proof, 2 goals: case zero ⊢ 2 triangular[0] == 0 (0 + 1); case successor ⊢ ∀_n∶ℕ 2 triangular[n] == n (n + 1) ⇒ 2 triangular[n + 1] == (n + 1) (n + 1 + 1) -->

At 0, the definition computes, and both sides are 0:

```wl
proof = TypeTheoryTactic["Simplify", {triangular}][proof]
```

<!-- => Proof, 1 goal: case successor ⊢ ∀_n∶ℕ 2 triangular[n] == n (n + 1) ⇒ 2 triangular[n + 1] == (n + 1) (n + 1 + 1) -->

At k + 1, the definition unfolds once, triangular[k + 1] is k + 1 + triangular[k], and the induction hypothesis `ih` gives 2 triangular[k]:

```wl
proof = TypeTheoryTactic["Simplify", {triangular}][TypeTheoryTactic["Introduce", k, ih][proof]]
```

<!-- => Proof, 1 goal: k ∶ ℕ, ih ∶ 2 triangular[k] == k (k + 1) ⊢ 2 (k + 1 + triangular[k]) == (k + 1) (k + 1 + 1) -->

What is left is algebra with the hypothesis: twice the left side is 2 (k + 1) + k (k + 1), which is (k + 1) (k + 2). `"PolynomialReduce"` finds the combination of the hypothesis that proves it:

```wl
proof = TypeTheoryTactic["PolynomialReduce"][proof]
```

<!-- => Proof complete -->

The kernel checks the proof again when the theorem is declared:

```wl
proved = TypeTheoryEnvironment[programs, TypeTheoryTheorem[GaussFormula, proof]];
proved[GaussFormula]
```

<!-- => theorem GaussFormula : ∀_n∶ℕ 2 triangular[n] == n (n + 1) -->

So `compiledClosedForm`, which computes `Quotient[n (n + 1), 2]`, gives `triangular[n]` for every n: n (n + 1) is even, twice `triangular[n]`, and its quotient by 2 is exact.

## Nicomachus's Theorem

The sum of the first n cubes is the square of the n-th triangular number. Multiplied by 4, so that no division is needed, it is a statement about `cubes` alone, proved the same way:

```wl
nicomachus = TypeTheoryProof[
    ForAll[{n}, 4 cubes[n] == (n (n + 1))^2],
    programs,
    {"Introduce"[n], "Induction"[n], "Simplify"[{cubes}], "Introduce"[k, ih], "Simplify"[{cubes}], "PolynomialReduce"}
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

The proof is by induction on the first list. On the empty list, `"Simplify"` unfolds [Join]() and `total`, and `"Ring"` closes 0 + total[b] == total[b]. On a list with a first element x, [Join]() unfolds to put x in front of Join[rest, b], and `total` to x plus the total of that; the induction hypothesis `ih` rewrites total[Join[rest, b]], and what is left is the associativity of addition:

```wl
TypeTheoryProof[joinStatement, {
    "Introduce"[a, b], "Induction"[a],
    "Simplify"[{total, Join}], "Ring",
    "Introduce"[x, rest, ih], "Simplify"[{total, Join}], "Rewrite"[ih], "Ring"
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

<!-- => 9223372039002259456, with CompiledCodeFunction::uncomp: IntegerOverflow -->

The theorem does not say that the compiled code is fast or that it does not overflow: it says what the program computes wherever the machine computes it. A type of the machine integers, numbers modulo 2^64, would let a theorem say where that is. That type, and compiling a definition and reading it as mathematics in one step, are the next steps, with the typed entries of the WolframKernel project's compiler.
