---
Template: TechNote
Name: Elaboration
Title: Elaboration
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/Elaboration
Keywords: [elaboration, type inference, implicit arguments, metavariables, universe levels, overloads, holes, compiler types, TypeSpecifier, formalization]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, InstancesAndCoercions, ThePrelude, RulesAndComputation]
---

A term is written as a Wolfram Language expression: `Function[{Typed[n, NonNegativeIntegers]}, n + 1]` uses the built-in heads [Function](), [Typed]() and [Plus](), held so that none of them evaluates. Elaboration turns that surface term into a core term of the type theory: it resolves each name, fills in the arguments left out, decides the types and universe levels nobody wrote, and chooses between the meanings of overloaded names. The elaborator is not trusted. Everything it produces is checked again by the kernel, so a mistake in elaboration gives a [Failure](), never a false theorem.

## From Surface Term to Core Term

[TypeOf]() elaborates a term and gives its type:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + 1]]]
```

<!-- => ℕ → ℕ -->

The type is read back into surface syntax and shown in mathematical notation, so it can be used as a term again.

## Names

A name is a variable that a binder in scope introduces, or a constant that the environment declares. [EqualityReflexivity]() is a constant of the prelude, and its argument 2 gives the type `2 == 2`:

```wl
TypeOf[TypeTheoryTerm[EqualityReflexivity[2]]]
```

<!-- => 2 == 2 -->

A constant may be named by a string as well as by a symbol. The prelude's Booleans are the string-named constants `"true"` and `"false"`:

```wl
TypeOf[TypeTheoryTerm["true"]]
```

<!-- => 𝔹 -->

A name that is neither a variable in scope nor a declared constant is refused:

```wl
TypeOf[TypeTheoryTerm[undeclaredName]]
```

<!-- => Failure["ElaborationFailed", ...]: undeclaredName is not a term of the type theory -->

A symbol whose value is a [TypeTheoryTerm]() stands for that term, so terms can be built in steps:

```wl
reflexivity = TypeTheoryTerm[EqualityReflexivity[2]];
TypeOf[TypeTheoryTerm[EqualitySymmetry[reflexivity]]]
```

<!-- => 2 == 2 -->

Code copied from a documentation page holds `PacletSymbol[paclet, name]` where a symbol stood. A term stores the symbol it names instead, without loading or evaluating anything:

```wl
TypeTheoryTerm[PacletSymbol["WolframInstitute/TypeTheory", "EqualityReflexivity"][2]]
```

<!-- => EqualityReflexivity[2] -->

## Implicit Arguments

[Length]() takes the type of the list's elements as an implicit argument, which nobody writes. Elaboration puts a metavariable in its place, an unknown, and unification solves it from the list:

```wl
TypeOf[TypeTheoryTerm[Length[{1, 2, 3}]]]
```

<!-- => ℕ -->

The elaborated term computes in the kernel:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Length[{1, 2, 3}]]]
```

<!-- => 3 -->

## Binders Without Types

A variable written without a type gets a metavariable for its type, solved by the uses of the variable. Here `x + 0` makes `x` a natural number, and the statement is a proposition:

```wl
TypeOf[TypeTheoryTerm[ForAll[{x}, x + 0 == x]]]
```

<!-- => Prop -->

Where nothing decides the type, it is asked for by name:

```wl
TypeOf[TypeTheoryTerm[ForAll[{a}, a == a]]]
```

<!-- => Failure["ElaborationFailed", ...]: The type of the variable a is needed: write Typed[x, type]. -->

## Universe Levels

A variable whose type is a sort, but whose level nothing decides, gets the level that the declaration allows. A theorem's statement is a proposition where it can be, as Lean elaborates a theorem's type against Prop, so `p` here is a proposition:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfImplication, ForAll[{p}, Implies[p, p]], Function[{p, h}, h]]}][SelfImplication]
```

<!-- => TypeTheoryTheorem[SelfImplication, ∀_{p∶Prop} p ⇒ p, ...] -->

A level still undecided becomes a universe parameter of the declaration, `"u_1"`, as Lean binds one:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfEquality, ForAll[{A, Typed[y, A]}, y == y], Function[{A, Typed[y, A]}, EqualityReflexivity[y]]]}][SelfEquality]
```

<!-- => TypeTheoryTheorem[SelfEquality, ∀_{A∶Sort u_1} ∀_{y∶A} y == y, ...] -->

A term on its own has no universe parameters, so an undecided level there is that of Type:

```wl
TypeOf[TypeTheoryTerm[Function[{a}, Function[Typed[z, a], z]]]]
```

<!-- => ∀_{a∶Type} a → a -->

## Overloaded Names

[True](), [False](), [Not](), [And]() and [Or]() are the propositions and also the operations of the Booleans. The type that is expected decides:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]]
```

<!-- => false -->

Where nothing decides, elaboration says so instead of guessing:

```wl
TypeOf[TypeTheoryTerm[True && False]]
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

<!-- => {TypeTheoryDefinition[square, Function[{Typed[x, Integers]}, x^2 + 1]]} -->

A function whose definitions do not fit, here because [StringReverse]() has no signature, is an axiom that the Wolfram Language computes and the kernel never runs:

```wl
reversed[s_] := StringReverse[s];
Last[TypeTheoryFormalize[reversed, integers]]
```

<!-- => TypeTheoryAxiom[reversed, "Expressions" -> "Expressions", "Implementation" -> reversed] -->

## Typing in the Compiler and in Mathematics

The Wolfram Language has two type systems that share names: the compiler's, which [FunctionCompile]() uses to choose machine code, and the type theory's, in which a type is a mathematical statement of what a term is. Both write a function type with [TypeSpecifier]() or `->`, and both answer [TypeOf](), so the difference is easy to miss.

The compiler's [TypeOf]() types an expression by how its values are stored. A machine integer is an `Integer64`:

```wl
TypeOf[Typed[1, "MachineInteger"]]
```

<!-- => TypeSpecifier["Integer64"] -->

A function on machine integers has a function type of machine integers:

```wl
TypeOf[Function[Typed[x, "MachineInteger"], x + 1]]
```

<!-- => TypeSpecifier[{"Integer64"} -> "Integer64"] -->

The same function in the type theory has a type of integers, the mathematical ones:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[x, Integers]}, x + 1], integers]]
```

<!-- => ℤ → ℤ -->

A compiled function works on the values its type admits and refuses the others before running:

```wl
increment = FunctionCompile[Function[Typed[x, "MachineInteger"], x + 1]];
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
TypeOf[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]]
```

<!-- => Prop -->

| | The compiler | The type theory |
|---|---|---|
| What a type is | how a value is stored: `"Integer64"`, `"Real64"`, `"PackedArray"::["Integer64", 1]` | what a term is: ℤ, ℚ, `Lists[A]`, `Vector[A, n]`, `2 + 2 == 4` |
| Its purpose | choosing machine code and memory layout | stating and checking mathematics |
| Numbers | bounded machine numbers; a compiled function refuses an argument of another type before running | the integers and rationals themselves, without bound |
| Function types | `TypeSpecifier[{a, b} -> c]`, arguments as a list | `a -> b -> c`, curried, and dependent: `ForAll[{Typed[n, NonNegativeIntegers]}, Vector[A, n]]`, whose result depends on the argument |
| Polymorphism | `ForAllType[a, {a} -> a]`, each use specialized to machine code | `ForAll[{TypedImplicit[a, TypeUniverse[u + 1]]}, a -> a]`, one term for every type, at every universe level |
| Constraints | conditions of `ForAllType` on a type variable | classes and their instances, found by elaboration |
| Propositions and proofs | none | a proposition is a type, and a proof is a term of that type |
| Inference | forward, from the types of the arguments and of the built-ins | unification of metavariables: implicit arguments, untyped binders, universe levels |
| A type error | a failure of compilation, or a refused argument | a [Failure]() of elaboration; the kernel accepts nothing it has not checked |
| What runs | machine code | reduction in the kernel, or the Wolfram Language for an axiom with an `"Implementation"` |

[TypeOf]() is the compiler's function, which TypeTheory gives a meaning for a [TypeTheoryTerm](). Once the compiler has loaded it, it holds its argument, so it must be given the term itself; a term kept in a variable is elaborated by [TypeTheoryCheck]() instead:

```wl
TypeTheoryCheck[reflexivity]
```

<!-- => 2 == 2 -->

The compiler of the WolframKernel project has types of its own, of the same kind as [FunctionCompile]()'s: how values are stored, inferred to choose code. [TypeTheoryFormalize]() reads its match programs and Core, which say what a definition does, and leaves the types to elaboration, which gives the mathematical ones.
