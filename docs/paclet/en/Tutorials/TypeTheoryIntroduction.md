---
Template: TechNote
Name: TypeTheoryIntroduction
Title: Getting Started with TypeTheory
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TypeTheoryIntroduction
Keywords: [type theory, getting started, terms, computation, environments, inductive types, tactics, induction, proof]
RelatedGuides: [TypeTheory]
---

TypeTheory is a proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written in the Wolfram Language. This tutorial writes terms with built-in symbols, computes with them, declares theorems, definitions and inductive types, and proves a theorem by induction one tactic at a time. Terms, proofs and declarations that name no environment are in the prelude, an environment of logic, equality and the natural numbers.

## Terms and Their Types

A term is written with built-in symbols, and [TypeTheoryTerm]() holds it. Here is the statement that adding zero to any natural number gives it back:

```wl
statement = TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

The term has to be held, because the Wolfram Language evaluates the same expression to [True]() at once:

```wl
ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]
```

<!-- => True -->

A statement is a type, and its type is the universe of propositions. [TypeTheoryCheck]() gives the type of a term:

```wl
TypeTheoryCheck[statement]
```

<!-- => Prop -->

[TypeOf]() gives the type of a term written out, here a function from natural numbers to natural numbers:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + n]]]
```

<!-- => ℕ → ℕ -->

## Computation

Terms compute. [WeakHeadNormalForm]() applies the function to its argument and adds the literals:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + n][21]]]
```

<!-- => 42 -->

Addition is defined by recursion on its second argument, so `n + 0` computes to `n` even for a variable `n`, and [DefinitionallyEqualQ]() sees it:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + 0]],
    TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n]]
]
```

<!-- => True -->

But `0 + n` is stuck: the recursion has nothing to work on until `n` is known. Equations like this need a proof by induction, which comes below:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, 0 + n]],
    TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n]]
]
```

<!-- => False -->

## Declaring Theorems and Definitions

Declarations, such as [TypeTheoryTheorem](), are inert until [TypeTheoryEnvironment]() checks them, which gives a new environment: the prelude extended with them. Here `2 + 2 == 4` is proved by computation, with [EqualityReflexivity]():

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 32 constants -->

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

A proof of the wrong statement is rejected, with the reason:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]}]
```

<!-- => Failure["TypeMismatch", ...]: EqualityReflexivity[4] has type 4 == 4, but the expected type is 2 + 2 == 5 -->

[Append]() adds a declaration to an environment. A [TypeTheoryDefinition]() unfolds when terms compute:

```wl
doubled = Append[arithmetic, TypeTheoryDefinition[Doubled, Function[{Typed[n, NonNegativeIntegers]}, n + n]]];
WeakHeadNormalForm[TypeTheoryTerm[Doubled[Doubled[5]], doubled]]
```

<!-- => 20 -->

Environments never change, so `arithmetic` is as it was:

```wl
KeyExistsQ[arithmetic, Doubled]
```

<!-- => False -->

## Inductive Types

[TypeTheoryInductiveType]() declares a type by its constructors. Binary trees are either a leaf or a node with two subtrees:

```wl
trees = TypeTheoryEnvironment[{TypeTheoryInductiveType[BinaryTree, TypeUniverse[1], {
    BinaryLeaf -> BinaryTree,
    BinaryNode -> ForAll[{Typed[left, BinaryTree], Typed[right, BinaryTree]}, BinaryTree]
}]}];
Keys[trees][[-4 ;;]]
```

<!-- => {BinaryTree, BinaryLeaf, BinaryNode, InductiveRecursor[BinaryTree]} -->

Declaring the type also generated its recursor, [InductiveRecursor](), which is how functions on trees recurse and how proofs about them go by induction. Its type has a case for each constructor:

```wl
TypeOf[TypeTheoryTerm[InductiveRecursor[BinaryTree], trees]]
```

<!-- => ∀_m∶(BinaryTree → Sort u) m[BinaryLeaf] → (∀_left∶BinaryTree ∀_right∶BinaryTree m[left] → m[right] → m[BinaryNode[left, right]]) → ∀_t∶BinaryTree m[t] -->

Counting the nodes of a tree: a leaf has one, and a node one more than its two subtrees together:

```wl
trees = Append[trees, TypeTheoryDefinition[NodeCount, Typed[
    Function[{Typed[tree, BinaryTree]}, InductiveRecursor[BinaryTree][
        Function[{Typed[t, BinaryTree]}, NonNegativeIntegers],
        1,
        Function[{Typed[left, BinaryTree], Typed[right, BinaryTree], Typed[l, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, l + r + 1],
        tree
    ]],
    TypeSpecifier[{BinaryTree} -> NonNegativeIntegers]
]]];
WeakHeadNormalForm[TypeTheoryTerm[NodeCount[BinaryNode[BinaryLeaf, BinaryNode[BinaryLeaf, BinaryLeaf]]], trees]]
```

<!-- => 5 -->

## Proofs with Tactics

Now for `0 + n == n`. [TypeTheoryProof]() starts a proof with the statement as its one goal:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n]]
```

<!-- => Proof, 1 goal: ⊢ ∀_n∶ℕ 0 + n == n -->

A [TypeTheoryTactic]() works on the first goal. `"Introduce"` takes the variable `n` into the context, and `"Induction"` on `n` leaves a goal for each constructor of the natural numbers:

```wl
proof = TypeTheoryTactic["Induction", n][TypeTheoryTactic["Introduce", n][proof]]
```

<!-- => Proof, 2 goals: case NaturalNumberZero ⊢ 0 + 0 == 0; case NaturalNumberSuccessor ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

The first goal, `0 + 0 == 0`, holds by computation:

```wl
proof = TypeTheoryTactic["Reflexivity"][proof]
```

<!-- => Proof, 1 goal: case NaturalNumberSuccessor ⊢ ∀_n∶ℕ 0 + n == n ⇒ 0 + (n + 1) == n + 1 -->

In the second, `"Introduce"` names the number `k` and the induction hypothesis `ih`, which says `0 + k == k`. The goal reads `0 + (k + 1) == k + 1`, where `k + 1` is how <code>[NaturalNumberSuccessor]()[k]</code> shows. Addition recurses on its second argument, so the goal computes to `(0 + k) + 1 == k + 1`, which [EqualityCongruence]() proves from `ih`:

```wl
proof = TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]][TypeTheoryTactic["Introduce", k, ih][proof]]
```

<!-- => Proof complete -->

The tactics built a proof term, an application of the recursor of the natural numbers:

```wl
proof["Term"]
```

<!-- => (n ∶ ℕ) ↦ ℕ_rec[(n1 ∶ ℕ) ↦ 0 + n1 == n1, EqualityReflexivity[0 + 0], (k ∶ ℕ) (ih ∶ 0 + k == k) ↦ EqualityCongruence[NaturalNumberSuccessor, ih], n] -->

Nothing a tactic did is trusted. Declaring the theorem has the kernel check the finished term:

```wl
proved = TypeTheoryEnvironment[{TypeTheoryTheorem[AdditionZeroLeft, proof]}];
proved[AdditionZeroLeft]
```

<!-- => theorem AdditionZeroLeft : ∀_n∶ℕ 0 + n == n -->

A theorem applies like a function, here to `7`:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroLeft[7], proved]]
```

<!-- => 0 + 7 == 7 -->

## Checking an Environment Again

An environment is a handle to a store of definitions, which could in principle be changed by hand. [TypeTheoryCheck]() replays every declaration of an environment from scratch and compares the results with what is stored:

```wl
TypeTheoryCheck[proved]
```

<!-- => True -->

[Normal]() gives the declarations themselves, the prelude's included, written out exactly, so an environment can be saved and rebuilt from them on the empty environment, checking every declaration again:

```wl
rebuilt = TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[proved]];
rebuilt[AdditionZeroLeft]
```

<!-- => theorem AdditionZeroLeft : ∀_n∶ℕ 0 + n == n -->

## Lean

The Calculus of Inductive Constructions is also the type theory of [Lean 4](https://lean-lang.org/). [LeanLink](https://www.wolframcloud.com/obj/wolframinstitute/LeanLink), the Wolfram Language link to Lean, translates declarations both ways: Lean theorems such as `Nat.zero_add` import into a [TypeTheoryEnvironment](), where this kernel checks them again, and theorems proved here export as Lean source that Lean's kernel accepts.
