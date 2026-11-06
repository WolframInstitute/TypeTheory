---
Template: TechNote
Name: Elaboration
Title: Elaboration
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/Elaboration
Keywords: [elaboration, type inference, implicit arguments, metavariables, universe levels, overloads, holes, compiler types, TypeSpecifier, formalization]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, InstancesAndCoercions, ThePrelude, RulesAndComputation, ProgramsAndProofs]
---

A term is written as a Wolfram Language expression: `Function[{Typed[n, NonNegativeIntegers]}, n + 1]` uses the built-in heads [Function](), [Typed]() and [Plus](), held so that none of them evaluates. Elaboration turns that surface term into a core term of the type theory: it resolves each name, fills in the arguments left out, decides the types and universe levels nobody wrote, and chooses between the meanings of overloaded names. The elaborator is not trusted. Everything it produces is checked again by the kernel, so a mistake in elaboration gives a [Failure](), never a false theorem.

## From Surface Term to Core Term

[TypeTheoryType]() elaborates a term and gives its type:

```wl
TypeTheoryType[Typed[n, NonNegativeIntegers] |-> n + 1]
```

<!-- => ℕ → ℕ -->

The type is read back into surface syntax and shown in mathematical notation, so it can be used as a term again.

## Names

A name is a variable that a binder in scope introduces, or a constant that the environment declares. `"equalityReflexivity"` is a constant of the prelude, and its argument 2 gives the type `2 == 2`:

```wl
TypeTheoryType["equalityReflexivity"[2]]
```

<!-- => 2 == 2 -->

A constant may be named by a string as well as by a symbol. The prelude's Booleans are the string-named constants `"true"` and `"false"`:

```wl
TypeTheoryType["true"]
```

<!-- => 𝔹 -->

A name that is neither a variable in scope nor a declared constant is refused:

```wl
TypeTheoryType[undeclaredName]
```

<!-- => Failure["ElaborationFailed", ...]: undeclaredName is not a term of the type theory -->

A symbol whose value is a [TypeTheoryTerm]() stands for that term, so terms can be built in steps:

```wl
reflexivity = TypeTheoryTerm["equalityReflexivity"[2]];
TypeTheoryType["equalitySymmetry"[reflexivity]]
```

<!-- => 2 == 2 -->

Code copied from a documentation page holds `PacletSymbol[paclet, name]` where a symbol stood, the paclet often guarded by an `If` that installs it. A term stores the symbol each `PacletSymbol` names instead, without loading or evaluating anything, so the copied code works as written:

```wl
PacletSymbol["WolframInstitute/TypeTheory", "TypeTheoryType"][PacletSymbol["WolframInstitute/TypeTheory", "TypeTheoryTerm"][PacletSymbol["WolframInstitute/TypeTheory", "NaturalNumberPredecessor"][3]]]
```

<!-- => ℕ -->

## Implicit Arguments

[Length]() takes the type of the list's elements as an implicit argument, which nobody writes. Elaboration puts a metavariable in its place, an unknown, and unification solves it from the list:

```wl
TypeTheoryType[Length[{1, 2, 3}]]
```

<!-- => ℕ -->

The elaborated term computes in the kernel:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[{1, 2, 3}]]]
```

<!-- => 3 -->

## Lists, Sequences and Their Types

`List` and `Sequence` are each a type and its elements, as the Wolfram Language writes both with one head. Where a type is expected, as the type of a binder, `{A}` is the type of the lists of `A`, and `Sequence[A, B]` the type of the sequences of an `A` and a `B`; elsewhere `{a, b}` is a list and `Sequence[a, b]` a sequence. In a term on its own, where nothing decides, the elements do, elaborated once: types make the type, so a type that [TypeTheoryType]() gives reads back as itself:

```wl
{TypeTheoryType[{1, 2}], TypeTheoryType[{NonNegativeIntegers}]}
```

<!-- => {{ℕ}, Type} -->

A function of the type theory is curried: `f[a, b]` is `f[a][b]`, each argument filling the next binder. A Wolfram Language function is applied to a sequence instead, `f[a, b]` giving `f` the sequence of `a` and `b`, so a binder of a type `Sequence[...]` takes the arguments that are left as one `Sequence`. One argument that is a sequence already, as the tail of `"sequencePrepend"`, is the sequence itself; it is elaborated once, and its type tells which:

```wl
pairs = TypeTheoryEnvironment[{TypeTheoryAxiom[sum, Sequence[NonNegativeIntegers, NonNegativeIntegers] -> NonNegativeIntegers]}];
DefinitionallyEqualQ[TypeTheoryTerm[sum[1, 2], pairs], TypeTheoryTerm[sum[Sequence[1, 2]], pairs]]
```

<!-- => True -->

A sequence of any number of elements of one type is of the type `A...`, as the pattern `p...` takes any number of expressions, and is written held, `Unevaluated[a, b, ...]`, as the Wolfram Language holds the arguments it passes on, and shown in brackets, `[a, b, ...]`. The last explicit binder of a function, if its type is `A...`, takes the arguments that are left as one sequence, each an `A` or a sequence spliced in, a variable of that type, `Unevaluated[...]`, or `Sequence @@ l` of a list; a binder of that type before others takes one argument, as any binder does, so a recursor's case of type `A...` is no sequence of the arguments after it. The Wolfram Language's own [Construct]() is applied so, `Construct[h, a, b]` building the expression `h[a, b]`:

```wl
{TypeTheoryType[Construct], NormalForm[TypeTheoryTerm[Construct[f, 1, Unevaluated[2, 3]]]]}
```

<!-- => {Expressions → Expressions... → Expressions, f[1, 2, 3]} -->

A bare arrow has one domain, so `{A} -> B` is a function of lists of `A`; a function of several arguments is curried, `A -> B -> C`, of a sequence, `Sequence[A, B] -> C`, of any number of arguments, `A... -> C`, or written as the compiler writes it, `TypeSpecifier[{A, B} -> C]`.

## Binders Without Types

A variable written without a type gets a metavariable for its type, solved by the uses of the variable. Here `x + 0` makes `x` a natural number, and the statement is a proposition:

```wl
TypeTheoryType[ForAll[{x}, x + 0 == x]]
```

<!-- => Prop -->

Where nothing decides the type, it is asked for by name:

```wl
TypeTheoryType[ForAll[{a}, a == a]]
```

<!-- => Failure["ElaborationFailed", ...]: The type of the variable a is needed: write Typed[x, type]. -->

## Universe Levels

A variable whose type is a sort, but whose level nothing decides, gets the level that the declaration allows. A theorem's statement is a proposition where it can be, as Lean elaborates a theorem's type against Prop, so `p` here is a proposition:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfImplication, ForAll[{p}, Implies[p, p]], {p, h} |-> h]}][SelfImplication]
```

<!-- => theorem SelfImplication : ∀_p∶Prop p ⇒ p -->

A level still undecided becomes a universe parameter of the declaration, `"u_1"`, as Lean binds one:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfEquality, ForAll[{A, Typed[y, A]}, y == y], {A, Typed[y, A]} |-> "equalityReflexivity"[y]]}][SelfEquality]
```

<!-- => theorem SelfEquality : ∀_A∶Sort u_1 ∀_y∶A y == y -->

A term on its own has no universe parameters, so an undecided level there is that of Type:

```wl
TypeTheoryType[a |-> Function[Typed[z, a], z]]
```

<!-- => ∀_a∶Type a → a -->

## Overloaded Names

[True](), [False](), [Not](), [And]() and [Or]() are the propositions and also the operations of the Booleans. The type that is expected decides:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]]
```

<!-- => false -->

Where nothing decides, elaboration says so instead of guessing:

```wl
TypeTheoryType[True && False]
```

<!-- => Failure["Ambiguous", ...]: say which with Typed[True && False, TypeUniverse[0]] or Typed[True && False, Booleans] -->

Instance arguments, found among the instances of a class, and coercions, inserted where a term has another type than the one expected, are [Instances and Coercions](paclet:WolframInstitute/TypeTheory/tutorial/InstancesAndCoercions).

## Holes

A proof can leave a part for later with [TypeTheoryHole](), as Lean's `sorry`. The kernel checks the rest, and the hole is recorded, never taken for a proof:

```wl
later = TypeTheoryEnvironment[{TypeTheoryTheorem[Later, ForAll[{Typed[k, NonNegativeIntegers]}, k + 0 == k], TypeTheoryHole["by induction"]]}];
Information[TypeTheoryTerm[Later, later], "Holes"]
```

<!-- => <|Later -> {<|"Hole" -> TypeTheoryHole[Later, 1], "Statement" -> ∀_{k∶ℕ} k + 0 == k, "Annotation" -> <|"Citation" -> "by induction"|>|>}|> -->

## Formalizing Wolfram Language Definitions

[TypeTheoryFormalize]() applies elaboration to the definitions of a Wolfram Language function. The compiler of the WolframKernel project reads the definitions, their left sides as match programs and their right sides as Core, and each definition that fits a shape the type theory has becomes a term: a single definition, structural recursion on a list or on a natural number, conditions and [If](). Elaboration then types the term. A function on integers is a definition that computes:

```wl
square[x_Integer] := x^2 + 1;
integers = TypeTheoryEnvironment["Integers"];
TypeTheoryFormalize[square, integers]
```

<!-- => {definition square := (x ∶ ℤ) ↦ x^2 + 1} -->

A function of strings is typed the same way, over [Strings](), the type of the strings, each string literal a constant of it:

```wl
greeting[s_] := StringJoin["Hello, ", s];
TypeTheoryType[greeting, TypeTheoryEnvironment[integers, TypeTheoryFormalize[greeting, integers]]]
```

<!-- => Strings → Strings -->

A function whose definitions do not fit, here because [Style]() has no signature, is an axiom that the Wolfram Language computes and the kernel never runs:

```wl
styled[x_] := Style[x, Bold];
Last[TypeTheoryFormalize[styled, integers]]
```

<!-- => axiom styled : Expressions → Expressions -->

A function has a second meaning, its rules, which every definition with a deterministic pattern has, whatever its body: with `"Meaning" -> "Rules"`, [TypeTheoryFormalize]() reads the match program of each rule as a match of the prelude, and the rules as a definition of type `Expressions -> Option[Expressions]`, the expression that an expression rewrites to. Nothing is elaborated but the term, and the types are those of expressions, so it is faithful to the Wolfram Language where the first meaning is mathematical. [The Wolfram Language](paclet:WolframInstitute/TypeTheory/tutorial/TheWolframLanguage) tutorial reads the rules of a function:

```wl
reversed[s_] := StringReverse[s];
Last[TypeTheoryFormalize[reversed, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[reversed] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (s ∶ Expressions) ↦ MatchValue[StringReverse[s]]] /; ¬AtomQ[expression] ∧ Decide[Length[Arguments[expression]] == 1]] -->

## Typing in the Compiler and in Mathematics

The Wolfram Language has two type systems that share names: the compiler's, which [FunctionCompile]() uses to choose machine code, and the type theory's, in which a type is a mathematical statement of what a term is. Both write a function type with [TypeSpecifier]() or `->`, so the difference is easy to miss: [TypeOf]() gives the compiler's type of an expression, and [TypeTheoryType]() the type theory's type of a term.

The compiler's [TypeOf]() types an expression by how its values are stored. A machine integer is an `Integer64`:

```wl
TypeOf[Typed[1, "MachineInteger"]]
```

<!-- => TypeSpecifier["Integer64"] -->

A function on machine integers has a function type of machine integers:

```wl
TypeOf[Typed[x, "MachineInteger"] |-> x + 1]
```

<!-- => TypeSpecifier[{"Integer64"} -> "Integer64"] -->

The same function in the type theory has a type of integers, the mathematical ones:

```wl
TypeTheoryType[Typed[x, Integers] |-> x + 1, integers]
```

<!-- => ℤ → ℤ -->

A compiled function works on the values its type admits and refuses the others before running:

```wl
increment = FunctionCompile[Typed[x, "MachineInteger"] |-> x + 1];
{increment[2^62], increment[1/2]}
```

<!-- => {4611686018427387905, Failure["ArgumentType", ...]} -->

The natural numbers of the type theory have no bound: the successor of 2^63 - 1 is 2^63, computed by the kernel:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, x + 1][2^63 - 1]]]
```

<!-- => 9223372036854775808 -->

The compiler's types describe arrays by their element type and rank, the shape of the memory:

```wl
TypeOf[Typed[{1, 2, 3}, "PackedArray"::["MachineInteger", 1]]]
```

<!-- => TypeSpecifier[TypeSpecifier["PackedArray"]["Integer64", 1]] -->

The type theory has types that no compiler type has: a statement is a type, a proposition, whose elements are its proofs:

```wl
TypeTheoryType[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]
```

<!-- => Prop -->

| | The compiler | The type theory |
|---|---|---|
| What a type is | how a value is stored: `"Integer64"`, `"Real64"`, `"PackedArray"::["Integer64", 1]` | what a term is: ℤ, ℚ, `{A}`, `Vector[A, n]`, `2 + 2 == 4` |
| Its purpose | choosing machine code and memory layout | stating and checking mathematics |
| Numbers | bounded machine numbers; a compiled function refuses an argument of another type before running | the integers and rationals themselves, without bound |
| Function types | `TypeSpecifier[{a, b} -> c]`, arguments as a list | `a -> b -> c`, curried, and dependent: `ForAll[{Typed[n, NonNegativeIntegers]}, Vector[A, n]]`, whose result depends on the argument; `Sequence[a, b] -> c` of a sequence, and `a... -> c` of any number of arguments |
| Polymorphism | `ForAllType[a, {a} -> a]`, each use specialized to machine code | `ForAll[{TypedImplicit[a, TypeUniverse[u + 1]]}, a -> a]`, one term for every type, at every universe level |
| Constraints | conditions of `ForAllType` on a type variable | classes and their instances, found by elaboration |
| Propositions and proofs | none | a proposition is a type, and a proof is a term of that type |
| Inference | forward, from the types of the arguments and of the built-ins | unification of metavariables: implicit arguments, untyped binders, universe levels |
| A type error | a failure of compilation, or a refused argument | a [Failure]() of elaboration; the kernel accepts nothing it has not checked |
| What runs | machine code | reduction in the kernel, or the Wolfram Language for an axiom with an `"Implementation"` |
| Pattern matching | a match program, compiled to code that tests and binds the parts of the call | a term of the monad of matches, `Match[A]`, whose first result is the rule applied: a function's rules have type `Expressions -> Option[Expressions]` |

Both hold their argument: [TypeOf]() types the expression as the compiler would, and [TypeTheoryType]() elaborates it as a term of the type theory. A [TypeTheoryTerm]() kept in a variable stands for the term it holds:

```wl
TypeTheoryType[reflexivity]
```

<!-- => 2 == 2 -->

The compiler of the WolframKernel project has types of its own, of the same kind as [FunctionCompile]()'s: how values are stored, inferred to choose code. [TypeTheoryFormalize]() reads its match programs and Core, which say what a definition does, and leaves the types to elaboration, which gives the mathematical ones. With `"Meaning" -> "Rules"`, it reads the match programs as matches instead, one instruction of the compiler a constant of the type theory, so that both describe the same matching.
