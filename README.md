# TypeTheory

A proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written
in the Wolfram Language. Terms are ordinary Wolfram Language expressions built from built-in symbols
(`Function`, `Typed`, `ForAll`, `Implies`, `Equal`, `Plus`, ...). A small trusted kernel checks them,
and tactics build proofs step by step in a notebook.

> Status: **prototype.** The kernel, inductive families with generated recursors, structures with
> projections, elaboration, a prelude of logic, equality, natural numbers, decisions and lists, and
> eighteen tactics, four of them Wolfram oracles, work and are tested. It is pure Wolfram Language, with no native library underneath,
> and it does not depend on Lean. LeanLink's `LeanToTypeTheory` and `TypeTheoryToLean` translate
> declarations between Lean and TypeTheory; through them this kernel checks all of Lean's
> `Init.Prelude`, 147 modules of Mathlib, from the logic of `Nonempty` to the complex numbers,
> derivatives, logarithms and real powers, inner product spaces and the p-adic numbers, and the 11,177
> constants under `Real.sqrt_nonneg`.

## Loading

Install the published paclet:

```wolfram
PacletInstall[ResourceObject["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Paclet/WolframInstitute/TypeTheory"]]
Needs["WolframInstitute`TypeTheory`"]
```

Or from a checkout:

```wolfram
PacletDirectoryLoad["path/to/TypeTheory/TypeTheory"]
Needs["WolframInstitute`TypeTheory`"]
```

Loading takes about three and a half seconds, most of them building the prelude through the kernel.

## Documentation

The [documentation site](https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory) has a reference
page for every symbol, a guide, and the tutorials *Getting Started with TypeTheory*, *The Prelude*,
*Instances and Coercions*, *The Integers*, *Rules and Computation*, *Erased and Affine Variables*, *Homotopy Type Theory*,
*Cubical Type Theory* and *Mathlib in TypeTheory*. The pages are
literate Markdown in [docs/paclet/en](docs/paclet/en), written to
[docs/paclet/en/DOC_GUIDE.md](docs/paclet/en/DOC_GUIDE.md), and
[PacletPage](https://www.wolframcloud.com/obj/wolframinstitute/PacletPage) builds and publishes them:

```bash
wl -f build_docs.wls             # evaluate the pages into notebooks under TypeTheory/Documentation
wl -f release.wls --dry-run      # build and check the site and the paclet archive, deploying nothing
wl -f release.wls                # publish the site and the paclet, as wolframinstitute
```

## A first session

A term carries the environment its constants come from. Without one, it is in the prelude, an
environment of logic, equality and the natural numbers:

```wolfram
TypeOf[TypeTheoryTerm[2 + 3]]
(* ℕ, that is TypeTheoryTerm[NonNegativeIntegers, prelude] *)

WeakHeadNormalForm[TypeTheoryTerm[2 + 3]]
(* 5 *)
```

Declarations are inert constructors until an environment checks them. `TypeTheoryEnvironment[{...}]`
gives the prelude extended with them, and `Append` extends any environment; neither changes the old one:

```wolfram
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}];
arithmetic[TwoPlusTwo]
(* theorem TwoPlusTwo : 2 + 2 == 4 *)

TypeTheoryEnvironment[{TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]}]
(* Failure["TypeMismatch", ...]: EqualityReflexivity[4] has type 4 == 4, but the expected type is 2 + 2 == 5 *)
```

A proof by induction, one tactic at a time:

```wolfram
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n]];
proof = TypeTheoryTactic["Introduce", n][proof];
proof = TypeTheoryTactic["Induction", n][proof];        (* goals 0 + 0 == 0 and 0 + n == n ⇒ 0 + (n + 1) == n + 1 *)
proof = TypeTheoryTactic["Reflexivity"][proof];         (* 0 + 0 == 0 by computation *)
proof = TypeTheoryTactic["Introduce", k, ih][proof];    (* ih : 0 + k == k *)
proof = TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]][proof];

proved = TypeTheoryEnvironment[{TypeTheoryTheorem[ZeroLeftIdentity, proof]}];
TypeTheoryCheck[TypeTheoryTerm[ZeroLeftIdentity[7], proved], TypeTheoryTerm[0 + 7 == 7]]
(* Success["TypeChecked", ...] *)
```

In a notebook a proof shows its open goals, each as a list of hypotheses over the goal. A term shows
in mathematical notation, with `∧`, `∨`, `¬`, and the natural numbers as `0` and `n + 1` as Lean shows
them; a declaration shows as its keyword, its name and its type.

## The language

| Surface term | Meaning |
| --- | --- |
| `Function[{Typed[x, A], ...}, b]` | a function |
| `ForAll[{Typed[x, A], ...}, B]` | a dependent function type, or a universal statement |
| `Implies[A, B]`, `TypeSpecifier[{A, ...} -> B]`, `A -> B` | a function type whose result does not depend on the argument |
| `TypedImplicit[x, A]` | an implicit binder, filled in by elaboration; `Annotation[Typed[x, A], kind]` with `"StrictImplicit"` or `"InstanceImplicit"` gives the other kinds, an instance-implicit one filled in by an instance |
| `Exists[{Typed[x, A]}, p]` | an existential statement |
| `Typed[e, A]` | `e`, checked against `A` |
| `With[{x = v}, b]` | `b` with `x` standing for `v` |
| `TypeUniverse[level]` | a universe: `TypeUniverse[0]` is Prop, `TypeUniverse[1]` is Type, `TypeUniverse[u + 1]` |
| `f[a, b]` | application, curried, with implicit arguments filled in |
| `Construct[f, a, b]` | application with every argument given, implicit ones included |
| `Subscript[c, level, ...]` | the constant `c` at explicit universe levels |
| `t[[i]]` | field `i` of `t`, whose type is a structure |
| `0`, `1`, `2`, ... | natural number literals |
| `RightTee[{Typed[x, A], ...}, B]` | a goal, read as `ForAll` |

Any other symbol or string is a bound variable or a declared constant. A symbol whose value is a
`TypeTheoryTerm` stands for that term, one whose value is a finished `TypeTheoryProof` stands for its
proof, and one whose value is a declared constant stands for it, as `Naturals = NonNegativeIntegers`
does.

`TypeTheoryTerm` has the `HoldFirst` attribute. It has to: `ForAll[Typed[x, A], B]` on its own evaluates
to `B`, and `n + 0 == n` to `True`. The declaration constructors and `TypeTheoryProof` hold their terms
for the same reason. Names are kept in `HoldComplete` throughout, so a symbol with a value never
evaluates inside a term.

## Environments

| Constructor | Declares |
| --- | --- |
| `TypeTheoryAxiom[name, type]` | an axiom |
| `TypeTheoryDefinition[name, value]` | a definition; `value` may be `Typed[v, type]`; `"Instance" -> True` makes it an instance of its type's class, and `"Coercion" -> True` a coercion |
| `TypeTheoryTheorem[name, statement, proof]` | a theorem; `TypeTheoryTheorem[name, proof]` takes the statement of a finished proof |
| `TypeTheoryInductiveType[name, type, {c -> type, ...}]` | an inductive type with its constructors and its recursor `InductiveRecursor[name]`; `{name -> type, ...}` declares mutually inductive types |
| `TypeTheoryNaturalNumbers[type, zero, successor, <\|role -> operation, ...\|>]` | the natural numbers that literals belong to, and the operations computed on literals |
| `TypeTheoryRewriteRule[name, ForAll[binders, lhs -> rhs]]` | a computation rule for an axiom, where the rules allow it |
| `TypeTheoryQuotients[]` | the quotient types of Lean's kernel; `TypeTheoryQuotients[equality, {type, introduction, lift, induction}]` under other names |
| `TypeTheoryCubical[sum]` | the interval, paths, transport, composition and Glue types of cubical type theory, where the rules are cubical |

`TypeTheoryEnvironment[{declaration, ...}]` adds declarations in turn to the default environment, which is
also the environment of any term or proof that names none: the prelude, until
`SetTypeTheoryEnvironment[env]` makes `env` the default (`SetTypeTheoryEnvironment["Prelude"]` sets it
back, and `Block[{$TypeTheoryEnvironment = env}, ...]` sets it for one computation). `TypeTheoryEnvironment[env, {declaration, ...}]` adds
them to `env`, `Append[env, declaration]` adds one, `TypeTheoryEnvironment[]` is empty,
`TypeTheoryEnvironment["Prelude"]` is the prelude itself, `TypeTheoryEnvironment["Constructive"]` is
the prelude without its axioms, `TypeTheoryEnvironment["HomotopyTypeTheory"]` is homotopy type theory,
`TypeTheoryEnvironment["Cubical"]` is cubical type theory, and
`TypeTheoryEnvironment[rules]` is the empty environment of the given `TypeTheoryRules`. An environment behaves like an association of
its constants: `env[name]` gives the declaration that introduced `name`, and `Keys`, `Length`,
`KeyExistsQ`, `Normal` and `Information` work as expected. `Normal[env]` gives the declarations, the
prelude's included, written out exactly, so `TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[env]]`
rebuilds it.

An environment is a handle to a store: a symbol of its own whose DownValues hold the constants, the
Wolfram Language's own way of storing definitions. The handle is small, so terms and proofs carry it. A
store is never changed once built, and it lasts for the session.

### The integers

`TypeTheoryEnvironment["Integers"]` is the prelude with the integers, built and checked the first time it
is asked for: classes of pairs of natural numbers (a, b), standing for a - b, a quotient type. The
operations are lifted from pairs, and the laws of a commutative ring, `IntegerAdditionCommutativity`
through `IntegerDistributivity`, are proved by the tactics themselves: `"Induction"` on each class,
`QuotientSoundness`, and `"Ring"` on the pairs. With those laws, `"Ring"` proves any identity of
commutative rings over the integers by normal forms of its own, as it does over the natural numbers;
`IntegerEqualityDecidable` decides their equations, so `"Decide"` proves a closed one. There `+`, `*`,
`-`, `^`, the comparisons and negative literals are the integers' wherever the types say so, and a
natural number coerces to an integer:

```wl
integers = TypeTheoryEnvironment["Integers"];
TypeOf[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[n, Naturals]}, 2 x - 7 <= x + n], integers]]   (* ℤ → ℕ → Prop *)
```

Squares are at least 0, `IntegerSquareNonnegative`, and `IntegerLessEqualOfMultiple` gives `x <= y` from
`(d + 1) (y - x) == s` with `0 <= s`. `"SumOfSquares"` proves an inequality with them: Wolfram finds `d`
and a sum `s` of squares of polynomials, by exact linear algebra on a Gram matrix and, where it has free
entries, `SemidefiniteOptimization`; `"Ring"` proves the equation:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x y + y z + z x <= x^2 + y^2 + z^2], integers, {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["SumOfSquares"]                     (* 2 (x^2 + y^2 + z^2 - x y - y z - z x), a sum of three squares *)
}]
```

### Quantities

Under `TypeTheoryRules["CalculusOfInductiveConstructions", "Quantities" -> True]` a binder may carry a
quantity, `Typed[x, A, 0]` or `Typed[x, A, 1]`: the code that runs never uses an erased variable, and uses
an affine one at most once, as in BendTT's affine type theory. The kernel counts the uses of each variable
outside the types, and function types differ by their quantities. The rules only reject more, so they are
as consistent as without quantities:

```wl
affine = TypeTheoryTranslate[TypeTheoryEnvironment["Prelude"], TypeTheoryRules["CalculusOfInductiveConstructions", "Quantities" -> True]]["Environment"];
TypeTheoryEnvironment[affine, {TypeTheoryDefinition[Twice, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[f, TypeSpecifier[{A} -> A], 1], Typed[x, A]}, f[f[x]]]]}]
(* Failure["QuantityExceeded", ...]: f has quantity 1, but the code that runs uses it more than once *)
```

### Cubical type theory

`TypeTheoryEnvironment["Cubical"]` follows cubical type theory, after Cohen, Coquand, Huber and Mörtberg: a
path is a function of an interval, function extensionality and path induction are terms, transport and
composition compute by the type, and univalence is a path of Glue types along which transport applies the
equivalence. It has no axiom, so transport along univalence computes:

```wl
cubical = TypeTheoryEnvironment["Cubical"];
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "true"], cubical]]   (* "false" *)
```

### Instances and coercions

Elaboration fills in what Lean's type classes and coercions do. An argument of an instance-implicit
binder, `Annotation[Typed[h, class], "InstanceImplicit"]`, is a variable bound by such a binder, or else
the first definition declared with `"Instance" -> True` whose type unifies with the binder's, the latest
declared first, its own instance arguments found in turn. A term whose type does not unify with the one
expected is passed through a definition declared with `"Coercion" -> True` from the one type to the
other, or a chain of at most three. The kernel checks every term elaboration builds with them:

```wl
coerced = TypeTheoryEnvironment[{
    TypeTheoryDefinition[NaturalOfBoolean, Function[{Typed[b, Booleans]},
        InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Naturals], 0, 1, b]], "Coercion" -> True]
}];
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberSuccessor["true"], coerced]]   (* NaturalOfBoolean["true"] + 1 *)
WeakHeadNormalForm[TypeTheoryTerm[Decide[2 < 3 && 4 != 5]]]                    (* "true", by the instances of Decidable *)
```

## The prelude

The prelude is the default environment, that of every term, proof and declaration list that names
none, unless `SetTypeTheoryEnvironment` sets another. Each of its
169 constants is checked by the kernel when the paclet loads. It is classical, as Lean's library is:
three constants are axioms, Lean's three, propositional extensionality, the soundness of quotients and
choice, and function extensionality and the excluded middle are proved from them. `TypeTheoryEnvironment["Constructive"]` is the prelude without the
axioms and what is proved from them, to prove theorems without axioms or to assume others. The tutorial
*The TypeTheory Prelude* on the documentation site goes through all of it.

- **Logic:** `True` (`TrueIntroduction`), `False` (`FalseElimination`), `Not`, `And` (`AndIntroduction`,
  `AndEliminationLeft`, `AndEliminationRight`), `Or` (`OrIntroductionLeft`, `OrIntroductionRight`),
  `Equivalent` (`EquivalentIntroduction`, `EquivalentForward`, `EquivalentBackward`, with reflexivity,
  symmetry and transitivity) and `Exists` (`ExistsIntroduction`).
- **Equality:** `Equal` (`EqualityReflexivity`, `EqualitySymmetry`, `EqualityTransitivity`,
  `EqualityCongruence`, `EqualitySubstitution`) and `Unequal`, `x != y`.
- **Functions:** `Identity` and `Composition`.
- **Quotients:** the quotient types of Lean's kernel, `QuotientType[r]`, with `QuotientIntroduction`,
  `QuotientLift` and `QuotientInduction`, declared by `TypeTheoryQuotients[]`: a lift computes on a
  class, and `QuotientSoundness`, Lean's `Quot.sound`, is an axiom.
- **Natural numbers:** `NonNegativeIntegers`, or `Naturals` for short, with `NaturalNumberZero`, `NaturalNumberSuccessor` and
  `NaturalNumberPredecessor`, registered so that literals are natural numbers; `Plus`, `Times`, `Power`
  and `Subtract` (which stops at 0), each by recursion on its second argument as in Lean, and computed
  on literals with integers, as Lean's kernel computes them with GMP; `LessEqual`,
  inductive as Lean's `Nat.le` (`LessEqualReflexivity`, `LessEqualStep`), with `Less`, `GreaterEqual`
  and `Greater`.
- **Theorems about them:** commutativity, associativity and distributivity of addition and
  multiplication, the zero, one and successor laws, cancellation of subtraction and of a positive factor,
  the laws of powers, injectivity of the successor, the order's transitivity, antisymmetry,
  irreflexivity and totality, and sums and multiples of inequalities.
- **Booleans:** `Booleans`, with the constants `"false"` and `"true"`, and `"not"`, `"and"` and `"or"`,
  named by strings, by cases on the first argument as Lean's `Bool`. `True`, `False`, `Not`, `And` and
  `Or` stand for them where a Boolean is expected, and they show as `true`, `false`, `!`, `&&` and `||`.
- **Decisions:** `Decidable` (`DecidableFalse`, `DecidableTrue`), a class as Lean's, with `Decide[p]`
  giving the Boolean of the decision of `p`, found among the instances, and `DecideSoundness` the proof
  from one that computes to `"true"`, as Lean's `decide` and `of_decide_eq_true`. The instances
  `NaturalNumberEqualityDecidable` and `LessEqualDecidable` decide `==` and `<=` of natural numbers
  through the Boolean comparisons `"equal"` and `"lessEqual"`, which the kernel computes on literals;
  `NotDecidable`, `AndDecidable` and `OrDecidable` combine decisions, and `"trueDecidable"`,
  `"falseDecidable"` and `"booleanEqualityDecidable"` decide `True`, `False` and equations of Booleans.
- **Pairs, sums, options and lists:** `CartesianProduct` (`Pair`), `DisjointUnion` (`LeftInjection`,
  `RightInjection`), `Option` (`OptionNone`, `OptionSome`) and `Lists` (`EmptyList`, `ListPrepend`), as
  Lean's `Prod`, `Sum`, `Option` and `List`; `Join`, `Length`, `Map`, `Append` and `Reverse` on lists,
  and their laws `JoinEmptyRight`, `JoinAssociativity`, `LengthJoin`, `LengthMap`, `MapJoin`,
  `MapComposition`, `ReverseJoin`, `ReverseReverse` and `LengthReverse`.
- **Classical logic:** `Nonempty` (`NonemptyIntroduction`) and `Subtype` (`SubtypeIntroduction`); the
  axioms `PropositionalExtensionality`, `QuotientSoundness` and `Choice`; `ChosenWitness` with
  `ChosenWitnessProperty`; and the theorems `FunctionExtensionality`, proved from the soundness of
  quotients as Lean proves it, `ExcludedMiddle`, proved by Diaconescu's argument, and
  `DoubleNegationElimination`.

The elaborator reads `a - b` as `Subtract[a, b]` and `a && b && c` as `a && (b && c)` for propositions
and `(a && b) && c` for Booleans. `True`, `False`, `Not`, `And` and `Or` are propositions or Booleans, as
the type decides: propositions where a type or `Prop` is expected, Booleans where `Booleans` is, and
otherwise whatever the arguments or the term's use allow. A term nothing decides, such as
`True == False`, is ambiguous and gives a `Failure`, and `Typed[True, Booleans]` says which it is.

## Rules and homotopy type theory

The rules the kernel checks by are a value, `TypeTheoryRules`, which every environment carries:
`"CalculusOfInductiveConstructions"` for the prelude, `"MartinLofTypeTheory"`, which has no Prop, and
`"CubicalTypeTheory"`, Martin-Löf type theory with the primitives of cubical type theory. The setting
`"Quantities"` adds binders of quantity 0 and 1 to any of them.
Without Prop every universe is `Type u`, no two proofs of an equality are made equal, recursors
eliminate into `Type u`, and a theorem may state any type. `TypeTheoryEnvironment[rules]` starts an
environment of given rules, and the setting `"RewriteRules"` allows `TypeTheoryRewriteRule` declarations,
which give an axiom computation rules that weak head normalization and definitional equality use.

`TypeTheoryEnvironment["HomotopyTypeTheory"]` is homotopy type theory as in the HoTT book, on Martin-Löf
rules with rewrite rules: `True`, `False` and `Not` as types; `Equal` as the type of paths, with path
induction as its recursor; `Transport` and the operations on paths, which compute on reflexivity;
bi-invertible equivalences and the axiom `Univalence`, with `UniverseNotSet` proved from it; and the
circle, by axioms, with the rewrite rule `CircleInductionBase` making induction compute on its base
point. On the prelude's rules the same declarations with an equality in Prop prove False, which is why
the HoTT rules refuse one.

`TypeTheoryTranslate[environment, rules]` moves declarations between rules: it replays them on the
empty environment of `rules`, whose kernel checks each again, and leaves out what does not check with
whatever mentions it. Where the rules lose Prop, Prop becomes `Type` and a universe level `l` becomes
`max(l, 1)`, recursor levels following; where they gain it, theorems become definitions. The
constructive prelude translates to Martin-Löf type theory but for the quotient types, and homotopy type
theory to the calculus of inductive constructions with rewrite rules. Axioms are kept only with
`"Axioms" -> True`, since propositional extensionality, for one, does not hold of types.

## Tactics

`TypeTheoryTactic[name, arguments...][proof]` works on the first goal of a `TypeTheoryProof`:

| Tactic | Effect |
| --- | --- |
| `"Introduce", x, ...` | moves the variables or hypotheses of a universal statement, implication or `Not` into the context |
| `"Exact", term` | solves the goal with a term |
| `"Apply", term` | solves the goal with a term applied to new goals, as many as its conclusion needs |
| `"Reflexivity"` | solves `a == b` when the two sides are equal by computation |
| `"Induction", x` | one goal per constructor of the type of `x`, with induction hypotheses; the indices of an inductive family must be variables, and the hypotheses that depend on `x` are generalized; on a class of a quotient, one goal for the class of an element |
| `"Cases", x` | one goal per constructor of the type of `x`, without induction hypotheses |
| `"Generalize", h, ...` | moves the hypotheses `h, ...`, with those that depend on them, back into the goal |
| `"Constructor"` | applies the first constructor of the goal's inductive type that applies |
| `"Assumption"` | solves the goal with a hypothesis |
| `"Rewrite", h` | rewrites the goal with the equation `h`, left to right, or right to left with `"RightToLeft"`; `"At" -> k` rewrites the hypothesis `k` instead |
| `"Change", statement` | replaces the goal by a statement equal to it by computation |
| `"Simplify", {h, ...}` | rewrites with the equations until none applies, unfolds each definition among them where it computes, and closes an equation whose sides are equal by computation |
| `"Decide"` | proves a closed statement by computing its decision, the instance of `Decidable` that elaboration finds: the prelude's decide `==` and `<=` of natural numbers and the connectives |
| `"Ring"` | proves an equation of natural numbers that holds in every commutative semiring, by normal forms with proofs from the prelude's laws |
| `"FindInstance"` | proves an existential statement over the natural numbers with witnesses that Wolfram's `FindInstance` finds |
| `"PolynomialReduce"` | proves an equation from the equations among the hypotheses, by a polynomial combination whose cofactors Wolfram finds |
| `"LinearArithmetic"` | proves an inequality, an equation or `False` from the inequalities and equations among the hypotheses, by a linear combination whose multipliers Wolfram finds |
| `"FindEquationalProof"` | proves an equation from equations for all values among the hypotheses, by replaying the proof Wolfram's `FindEquationalProof` finds |
| `"SumOfSquares"` | proves an inequality of integers, or of natural numbers, in `TypeTheoryEnvironment["Integers"]` by a sum of squares that Wolfram finds, a positive multiple of the larger side less the smaller |

`TypeTheoryProof[statement, env, {tactic1, tactic2, ...}]` runs a list of tactics. Nothing a tactic does
is trusted: the finished term is checked by the kernel when the theorem is added to an environment.

`"Simplify"` unfolds a definition by recursion where it computes, as Lean's `simp [f]` does, and folds
its recursive calls back, so the laws of lists go through with induction and simplification alone:

```wolfram
TypeTheoryProof[ForAll[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]], Typed[c, Lists[Naturals]]}, Join[Join[a, b], c] == Join[a, Join[b, c]]], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Induction", a],
    TypeTheoryTactic["Simplify", {Join}],                (* Join[EmptyList, m] is m *)
    TypeTheoryTactic["Introduce", x, rest, ih],
    TypeTheoryTactic["Simplify", {Join, ih}]             (* Join[ListPrepend[x, l], m] is ListPrepend[x, Join[l, m]] *)
}]
```

`"FindInstance"`, `"PolynomialReduce"`, `"LinearArithmetic"`, `"FindEquationalProof"` and `"SumOfSquares"`
ask Wolfram for what a proof needs: witnesses, the cofactors or multipliers of a combination of the
hypotheses, a proof by completion from equational hypotheses, or a sum of squares. The kernel checks the proof built from the answer:

```wolfram
TypeTheoryProof[Exists[{Typed[x, Naturals], Typed[y, Naturals]}, And[x^2 + y^2 == 25, 0 < x, x < y]], {
    TypeTheoryTactic["FindInstance"]                     (* x = 3, y = 4, checked by computing *)
}]
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x + y == 10, Implies[x == 2 y + 1, x y == 21]]], {
    TypeTheoryTactic["Introduce", x, y, h, k],
    TypeTheoryTactic["PolynomialReduce"]                 (* cofactors over thirds, checked by "Ring" *)
}]
```

## How it works

```
TypeTheory/Kernel/
  Terms/CoreTerms.wl           core terms (locally nameless) and universe levels
  Terms/SurfaceSyntax.wl       held syntax trees; reading core terms back, for display or exactly
  Terms/Formatting.wl          notebook display of terms, declarations and proofs
  Checking/Rules.wl            the rules an environment is checked by: TypeTheoryRules
  Checking/TypeChecking.wl     the kernel: inference, reduction, definitional equality, projections
  Checking/InductiveTypes.wl   checking inductive families and generating recursors
  Checking/NaturalNumbers.wl   registering the natural numbers for literals
  Checking/Quotients.wl        the quotient types of Lean's kernel, and their computation
  Checking/Quantities.wl       binder quantities and the live check of erased and affine variables
  Checking/Cubical.wl          the interval, paths, transport, composition and Glue types
  Checking/Environment.wl      environments as stores of definitions, and kernel failures
  Checking/Declarations.wl     the declaration constructors and environments built from them
  Checking/Queries.wl          TypeOf, TypeTheoryCheck, DefinitionallyEqualQ, WeakHeadNormalForm, environments as associations
  Elaboration/Elaboration.wl   implicit arguments, instances, coercions, universe levels, unification
  Proofs/ProofStates.wl        proof states and tactics
  Proofs/Ring.wl               polynomial identities, with proofs from the prelude's laws
  Proofs/Equational.wl         the proofs of FindEquationalProof, replayed
  Proofs/SumsOfSquares.wl      sums of squares of polynomials, found from Gram matrices
  Library/Prelude.wl           the prelude
  Library/HomotopyTypeTheory.wl  the homotopy type theory environment
  Library/Integers.wl          the integers, a quotient, with their laws proved by the tactics
  Library/Cubical.wl           the cubical environment: paths, equivalences and univalence that computes
```

The trusted part is `CoreTerms.wl`, `TypeChecking.wl`, `InductiveTypes.wl`, `NaturalNumbers.wl`,
`Quotients.wl`, `Quantities.wl`, `Cubical.wl`, `Environment.wl` and the core declaration functions: about
4,000 lines with their comments and usage messages, a thousand of them the cubical rules, which an
environment uses only under cubical rules. Elaboration and tactics produce terms that the kernel checks again with no metavariables
left, so a mistake outside the kernel can make a proof fail but cannot make a false statement a theorem.
Kernel answers are `Failure` objects, never messages.

A store can be changed by hand. `TypeTheoryCheck[environment]` replays every declaration from scratch
and compares each stored record with the record that checking it produces, so a forged theorem or
recursor is caught. See [docs/notes/Kernel.md](docs/notes/Kernel.md) for the design decisions, and
[docs/research/TypeTheoryEngine.html](docs/research/TypeTheoryEngine.html) for the full design.

## Tests

```bash
wolframscript -f scripts/run_tests.wls
```

The suite has 296 tests in `TypeTheory/Tests/`, mirroring the kernel layout. They include rejecting
forged declarations: a wrong proof, a negative occurrence, an oversized universe, large elimination
from `Or`, data projected out of a proof, `Type : Type`, a lift of a quotient whose proof is wrong, an
equality that is not the identity type, a definition that copies an affine variable, a recursion on an
affine number, a transport along a line that is not constant on its face, and tampered environment
records; and, on the prelude's rules, the HoTT library proving False with an equality in Prop.

## Not yet

- The rationals, as a quotient of the integers; deciding the order of the integers; sums of squares with
  rational coefficients, and inequalities from hypotheses by the Positivstellensatz.
- Induction on mutual or nested types, and on indexed families whose indices are not variables, in the
  tactic.
- Composition in a universe and higher inductive types in the cubical rules, so that transport along a
  concatenation of univalence paths computes; truncations; BendTT's own relaxations, a universe in itself
  and no positivity, which its consistency proof covers and these rules do not.
- Higher-order unification beyond patterns.
- A compiled kernel (`FunctionCompile` over an array encoding of terms).
