# Changelog

Changes to TypeTheory, gathered by week. A week runs Monday to Sunday (ISO 8601) and the newest comes first.
Each entry names the versions released in that week; releases are tagged `v<version>` from 0.15.0 on, and
`git log v0.38.0..v0.39.0` gives the commits of one. An entry is a summary, not a list of commits: several
commits and releases that build one feature are one line.

## 2026-W46 (November 9 to 15), in progress

Versions 0.35.0 to 0.42.2.

### Added

- **Compiled code as mathematics.** `TypeTheoryFormalize[f, "Machine"]` reads more of what the compiler
  produces: a recursion, which is proved to compute the mathematical recursion; `While` loops, each a
  constant by recursion on fuel; an `If` whose branch sets a local; a `Do` with an iterator; a loop that
  calls its function; functions that call each other. A compiled loop is proved to compute the triangular
  number.
- A machine result computes its integer first, so a stored value is a literal and stays small.
- The tactic `"RewriteRepeated"`, which replaces `"Simplify"`, and a proof tree for every proof, not only
  those of propositional logic.
- The holes of a proof's term are numbered as its goals and show their goal on mouseover.
- The parts of a structure by name, `s["element"]`, shown `s〚element〛`.
- Arguments by name, `f[x, n -> 2]`, after the positional ones; implicit arguments by plain application.
- A recursion unfolds at `k + 1` and where it gives a function.
- `TraditionalForm` of a term shows it for reading: `f(x)`, `=`, and a recursor as a table of its cases. A
  constant shows by the notation `TraditionalForm` has for it, the Wolfram Language's own for one of its
  symbols, `r_d(n)` for `SquaresR[d, n]` and `a mod b` for `Mod[a, b]`, or a rule of `MakeBoxes` given for
  `TraditionalForm`; its arguments keep the order they are written in.
- **The machine reals.** `TypeTheoryEnvironment["MachineReals"]`, the 64-bit reals as rationals with a
  witness the kernel checks, with typed code on machine reals read from compiled code, which
  `TypeTheoryFormalize[f, "Machine"]` reads there by itself; `NormalForm[term, "Implementations" -> True]`
  computes implemented axioms. The edges of real arithmetic were run against compiled code on arm64 and
  x86-64.
- The rounding of the machine reals has its specification, the axiom `"real64ResultNearest"`: the nearest machine
  real, the even one of two as near, and the leave from 2^1024 - 2^970 on. Sums and products of machine reals are
  proved commutative. `"real64NearestQ"` is the Boolean the kernel computes for a rational and a machine real,
  whether the real is the rounding of the rational; `scripts/real64_nearest_grid.wl` holds it to the machine. The
  implementation of the rounding computes by integers.
- **The order of the rationals.** It is total, transitive and antisymmetric, sums keep it and so do products by a
  nonnegative rational, and its Booleans decide it, so `"Decide"` proves an inequality of numbers. From it, three
  properties of the rounding of the machine reals are theorems: a machine real is its own rounding, the rounding is
  monotone, and a result is within half the distance of any two machine reals around the rational.
- `"Ring"` proves an equation of rationals from the rationals' own laws, as it does for integers: a term that is no
  sum or product is an atom, and an identity in four variables, which through the classes of pairs took gigabytes,
  takes hundredths of a second, and one that does not hold is refused at once. An equation that holds by the
  arithmetic of fractions is still left to the classes. The rationals' library has the twelve laws it lacked.
- The tactic `"Have"` states a step on the way: `"Have"[e, statement]` makes the statement a goal to prove first, and
  the goal goes on with it as the hypothesis `e`. `"Cases"` splits a proof though the goal has no copy of it, so a
  fact is used for its cases, `"Cases"["lessEqualTotality"[m, n]]`.
- `"Cases"` and `"Induction"` split on a term that is no hypothesis, `"Cases"[Decide[n <= m]]`: every copy
  of the term in the goal becomes a variable, and each case is stated with its recursors computed.

### Changed

- `NormalForm` gives a natural number over a part that does not compute as that part and a number, one form however
  it is written: `(k + 1) + 1` and the successor of the successor of `k` normalize to `k + 2`, where they gave two
  successors. `k + 1000000` is its own normal form, where it was a failure of the recursion limit, as was the normal
  form of a machine operation on an integer that does not compute.
- A sum in a sum shows its parentheses: `(k + 1) + 1` and `k + (1 + 1)` are different terms.
- Pages, usage messages and comments describe each feature on its own terms; comparisons with Lean remain
  only where Lean is the subject.

### Fixed

- **`TypeTheoryCheck` accepted a record without its value (0.16.0 to 0.42.1).** Where the compiled kernel has its
  library, the check of an environment passed a record of a theorem, an opaque constant or a definition that had no
  value: a theorem of any statement, with no proof, was reported as checked. Measured on 0.42.1; the code that makes
  it is in every release from 0.16.0. It takes a store or a saved file changed by hand; no declaration, import or
  saved environment of TypeTheory writes such a record, so an environment built from declarations was not affected.
  The compiled program is now run only on an input in which every reference is one and every constant it checks has
  what it checks; otherwise the other kernel, which always refused such a record, answers.
  `TypeTheoryCheck[environment, Method -> "Symbolic"]` was never affected. From 0.43.0 the compiled program refuses
  such an input itself as well: it reads every row as that check does, a field that a row's kind does not use is 0,
  the order names every constant once, and a constant is declared only on a success that its check returns.
- **A forged rewrite-rule index (0.6.0 to 0.42.2).** Under rules with rewrite rules, a store changed by hand, and from
  0.16.0 a saved file read with `"Check" -> True`, could file a rewrite rule under another axiom: `TypeTheoryCheck`
  reported it checked, and that axiom then computed by the rule. A rule is now taken only for the constant its left
  side names, a store makes its indexes from its records and takes none from a file, and `TypeTheoryCheck` compares
  every key a store makes from its records with the one its replay makes. Environments built by declarations were not
  affected; of the libraries, only HomotopyTypeTheory has rewrite rules.
- **`TypeTheoryCheck` compares every record whole.** After the compiled kernel every record is declared again and
  compared with the environment's, as `Method -> "Symbolic"` does: on 0.42.2 a definition whose `"Instance"` or
  `"Coercion"` was turned by hand passed, since only inductive types and quotients were declared again.
  `scripts/kernel_agreement_fuzz.wls` runs the two methods on records changed one at a time.
- The term of a proof by `"LinearArithmetic"` or `"NonlinearArithmetic"` checks against its statement, as the term of
  any finished proof does, and its axiom closure computes: the certificate left out a predicate that no elaboration
  finds again.
- `Normal` writes the fields of a constructor with their names, `Typed["fst", "α"]`, where it wrote an arrow and the
  name was lost: an environment rebuilt from `Normal` read a projection by its index and showed it so, or showed
  the name of an arrow's own binder, a blank. The binder of an arrow names no field now.
- A rule is data before it names an argument; arguments by name come last.
- A bound variable that another symbol shadows shows by its name.
- `TraditionalForm` writes `=` also where a notebook writes the equation's sign as one character.
- A term shows the names that are strings without quotes in an input cell too, where a document typesets
  a term as written.
- A notation that gives an `InterpretationBox` or a `TemplateBox` shows inside a term: the display's rewrites of
  boxes stayed unevaluated in boxes that hold their parts, a red box in a notebook.
- A saved environment reads under another engine of the Wolfram Language than the one that saved it: the hash that
  names the kernel's sources is of bytes, where it was of an expression, which each engine hashes its own way, and
  the file was checked again in full.
- A tactic that compares two terms answers in time: `"Reflexivity"` on
  `Quotient[k + 12, 12] == Quotient[k, 12] + 1` took half an hour to say no, and takes 23 ms.

### Performance

- A beta reduction computes the operations on literals that it builds.
- The compiled kernel takes an environment with a natural number literal of 2^62 or more, which it declined whole: the
  literal is an opaque constant there, and the few records that need its value are checked by the other kernel. A
  batch of 11,899 constants of Mathlib's lowest modules, six of them with such a literal (`UInt64.size` among them),
  imports in 10 s where it took 569 s.
- The compiled kernel checks the defining equations of the registered operations of the natural numbers, as theorems
  in its one pass, and a check does not compare them a second time: 80 ms less in every check of a cone of Mathlib on
  Wolfram 15. The compiled program is unchanged.
- A registration's defining equations are compared with the kernel's caches: 160 ms less in every check of
  an environment that registers the natural numbers' operations, as a cone of Mathlib does.

### Documentation

- Programs and Proofs: the recursion on the machine, Gauss's formula by tactics with the term at each
  step and by hand one rewrite at a time, and a recursion whose result's type depends on the number.

## 2026-W45 (November 2 to 8)

Versions 0.18.0 to 0.34.0. Version 0.17.1 was not published.

### Added

- **Display.** Constants named by symbols show in bold; bound variables, universe levels and unsolved
  metavariables in colors; every part of a term shows its type on mouseover. Function types read back as
  bare arrows, and a level that nothing decides is `Prop`, a universe parameter or `Type`.
- **Wolfram Language functions as constants.** An axiom names the function that computes it
  (`"Implementation"`). `TypeTheoryFormalize` makes a function's definitions a constant: structural
  recursion on lists and on natural numbers, also with other arguments, and conditions and `If` by the
  decision of the condition.
- **The Wolfram Language in the prelude.** Expressions as data, with atoms and strings that `SameQ` and
  rewriting compute on in the kernel; the rules of a symbol as matches (`Match`, `MatchValue`, `MatchSum`,
  `MatchPart`), translated from every pattern; `List` and `Sequence`, each a type and its elements; lists
  built from `{}` by `Prepend`; sequences of any length, `A...`, with `Construct` and `Arguments`.
- Sums of types, `A | B`; computations that may fail, `A | Failure`, with `Enclose` and `Confirm`;
  associations, `Association[K, V]`, with `Missing`.
- `TypeTheoryType` gives the type of a term and holds its expression. Tactics are written
  `"Name"[arguments]`. Constructors, theorems and axioms are named by strings; a lone string names a
  constant, with `FromString` and `TypeHint` for the other readings. `Unevaluated` is the one head that
  quotes. Pure functions of slots, and more types that elaboration infers.
- `NormalForm` reduces a term in every part; `ExpressionEvaluate`; `TypeTheoryExpression`, the Wolfram
  Language reading of a term as it is written.
- `TypeTheoryProofTree[proof]`; the tactic `"NonlinearArithmetic"`; a rejected proof says why.
- A library environment is given by its name wherever an environment is.
- **Kernel.** The offset rule compares `x + k` with `y + k'` without counting; addition reduces by its
  equations; a registered operation is checked by its equations or named in the axiom closure; the order
  of the integers is decided.
- `Quotient` and `Mod` of natural numbers and of integers, rounded as the Wolfram Language rounds them.
- **The machine.** `TypeTheoryEnvironment["Machine"]`, the 64-bit integers of the compiler's typed code,
  and `TypeTheoryFormalize[f, "Machine"]`, a function as its compiled code computes it, with `Quotient`,
  `Mod` and recursion.

### Fixed

- With no front end a term's boxes are those a terminal prints as text, and a failure's message prints
  as text.
- A normal form holds no beta-redex and elaborates again to its type.
- Definitional equality never walks a literal, and running out of recursion is no answer.
- Checks and definitions coerce their values; an ascription has the type it is given; unknown methods and
  rules fail.
- A term read in another environment keeps the meaning of its constants.
- A proof's display holds a handle to the proof, not its term.

### Documentation

- New tutorials: Elaboration, The Wolfram Language, Patterns and Rewriting, Programs and Proofs, and
  Paradoxes, from unsound environments.
- Every symbol page expanded to all its sections, by real uses, and reread against its outputs.

## 2026-W44 (October 26 to November 1)

Versions 0.15.0 to 0.17.0.

### Added

- Environments save to WXF files, and the libraries load from them.
- **A compiled kernel** checks environments about a hundred times faster; a list of declarations is
  checked at once with `Method -> "Compiled"`.
- `TypeTheoryAxiomClosure` gives the axioms a term rests on.
- Theorems with holes, proofs left to give, which a theorem keeps with the annotation it is declared with.
- A declaration overloads an arithmetic operation.
- `CartesianProductType` and `DisjointUnionType`; products, sums, pairs, lists, dependent sums and subtypes
  display in notation; a list written as a term is the list of its elements; a type shows in bold.
- A binder without a type takes the type its body gives it.
- A proof of propositional logic gives its natural-deduction tree, and the tactic `"Classical"` proves
  classical propositional logic.

### Fixed

- `"Rewrite"` and `"Induction"` pass the right motive universe under rules without `Prop`; `"Rewrite"`
  takes an instance equal by computation and compares candidates without unfolding a definition.
- A saved environment is checked before anything in it evaluates, and reading one runs nothing an
  annotation holds.
- A recursion too deep for the Wolfram Language's stack is a failure, not a crash.
- The axiom closure of a finished proof is of its own term.

### Performance

- Definitional equality decides in a fixed order and infers types only inside checks; an application's
  type is inferred along its spine at once; a check remembers its universe instantiations.
- The compiled kernel's input is built as packed tables, a kind of row at a time.
- The paclet loads without loading `TypeOf`'s own implementation.

### Documentation

- Design notes on definitional equality and on the costs of evaluation; more examples on 127 symbol
  pages, every output read against its hint.

## 2026-W43 (October 19 to 25)

Versions 0.8.0 to 0.14.0.

### Added

- **Tactics.** `"Rewrite"`, also in a hypothesis, `"Cases"`, `"Generalize"`, `"Change"`, `"Simplify"` and
  `"Decide"`; and tactics that ask the Wolfram Language for what the kernel then checks: `"FindInstance"`,
  `"Ring"`, `"PolynomialReduce"`, `"LinearArithmetic"`, `"FindEquationalProof"` and `"SumOfSquares"`.
- **The prelude** decides propositions (`Decidable`, `Decide`) and has pairs, sums, options and lists.
- Instances and coercions in elaboration; decisions are found as instances.
- **Quotient types** in the kernel, with induction on the classes of a quotient.
- **The integers**, a quotient of pairs of natural numbers, with their equations decided and `"Ring"` over
  them; **the rationals**, a quotient over the integers, with their inverse.
- Mutual and nested inductive types.
- Registered operations on natural numbers compute on literals with integers.
- **Quantities**: erased and affine binders, checked by the kernel.
- **Cubical type theory**: the interval, paths, transport, composition, and Glue types with univalence
  that computes.
- `TypeTheoryTranslate` moves declarations between the rules of two type theories.
- Opaque definitions; definitional heights, and lazy unfolding of definitions in the kernel.
- `SetTypeTheoryEnvironment` and `$TypeTheoryEnvironment`; a declaration takes a core term as it is.

### Changed

- The Booleans' constants are named by strings.

### Performance

- A term given in full skips elaboration; the kernel remembers what it computed in a check; substitution
  keeps the sharing of a term; an environment shares the records of the one it extends.

### Documentation

- New tutorials: Mathlib in TypeTheory, with 147 modules of Mathlib checked; Rules and Computation;
  Instances and Coercions; The Integers; The Rationals; Quantities; Cubical Type Theory. Notation for
  constants with `MakeBoxes` and `Format`.

## 2026-W42 (October 12 to 18)

Versions 0.1.0 to 0.7.0, all on October 18.

### Added

- **The engine**: a kernel for the Calculus of Inductive Constructions in pure Wolfram Language, with
  elaboration, tactics and proof states.
- Environments are explicit values built from declarations (`TypeTheoryAxiom`, `TypeTheoryDefinition`,
  `TypeTheoryTheorem`, `TypeTheoryInductiveType`), and the prelude is the environment that is not given.
- A classical prelude, and a constructive environment without it.
- The Booleans, with `True`, `And` and the other connectives overloaded by type.
- The rules of a type theory are a value every environment carries (`TypeTheoryRules`); rewrite rules;
  the homotopy type theory environment, with univalence and the circle.
- `TypedImplicit`, `Naturals`, and symbols whose value is a constant stand for it.
- A check that passes gives a `Success`, and a proof displays as itself.

### Documentation

- The README, the kernel design notes and the design document; reference pages, a guide and the first
  tutorials (an introduction, The Prelude, Homotopy Type Theory), published with PacletPage.
