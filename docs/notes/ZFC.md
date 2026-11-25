# ZFC in TypeTheory: Aczel's model, and set.mm's axioms as theorems

`TypeTheoryEnvironment["ZFC"]` (`TypeTheory/Kernel/Library/ZFC.wl`) is the prelude with a model of ZFC. No declaration
of the file is an axiom: every axiom of ZFC, and every axiom of set.mm, Metamath's database of ZFC, is a theorem proved
from the prelude's three axioms, `"propositionalExtensionality"`, `"quotientSoundness"` and `"choice"`. The tests ask
that the environment's axioms are the prelude's and give the closure of each axiom.

## The model

A pre-set is a well-founded tree: a small type of indices `α : TypeUniverse[1]` and a function from it to pre-sets,
`"preSet"[α, f]`, the W-type the kernel accepts as a recursive field `(i : α) -> "PreSet"`. Two pre-sets are equivalent
when each element of either is equivalent to some element of the other, `"preSetEquivalent"`, defined by recursion on
the first and cases on the second. A set is a class, `"Set" = QuotientType["preSetEquivalent"]`, and membership
`Element[a, b]` is lifted through both arguments with `QuotientLift`, so that on classes of pre-sets it computes:
`Element[⟦x⟧, ⟦"preSet"[α, f]⟧]` is `Exists[{i : α}, "preSetEquivalent"[x, f[i]]]` with no proof.

`"Set"` lives in `TypeUniverse[2]`, one universe above the index types: a pre-set quantifies over the small types, so it
cannot be one of them. This is forced, as it is for Lean's `ZFSet.{0} : Type 1`.

Every construction is a range: `"setRange"[α, F]`, the set of the values of `F : α -> "Set"` on a small type, built by
choosing a representative of each value (`"setRepresentative"`, by `ChosenWitness`). `"elementOfRange"` gives its
members; with `"setIndex"` and `"setElement"` every set is the range of its own elements. The empty set is the range of
an empty subtype, pairs of `Booleans`, unions of a `"DependentPair"` of indices, power sets of the predicates on the
indices, separation of a subtype, replacement of the subtype of the indices where a value exists, with the chosen value.

| axiom | theorem | from |
|---|---|---|
| extensionality | `"extensionality"` | `"quotientSoundness"`, exactness by transport of a lifted predicate |
| regularity | `"regularity"` | `"elementInduction"`: induction on pre-sets under `QuotientInduction`, then classically |
| infinity (set.mm's form) | `"infinity"` | the range of `"singletonIterate"[x, n]` over the natural numbers |
| replacement | `"replacement"` | the range of chosen values; functionality makes any value equal to the chosen one |
| choice (set.mm's form) | `"choiceAxiom"` | the pairs `{w, c(w)}`; uniqueness from `"elementIrreflexive"`, `"elementAsymmetric"` and `"chosenElementCongruence"` (proof irrelevance) |

## Classes and set.mm's vocabulary

set.mm is a theory of classes: `x = y` is `( cv x ) = ( cv y )` and `x e. y` is `( cv x ) e. ( cv y )`. A class is a
predicate, `"Class" = "Set" -> Prop`; `cv` is `"setClass"[x]`, the class of the members of `x`; `A = B` is `==` of
classes; `A e. B` is `"classElement"[A, B]`, `Exists[{a}, A == "setClass"[a] && B[a]]`; `{ x | ph }` is
`"classAbstraction"[Function[...]]`. The translation must be compositional (a special case for `x e. y` would break
substitution), so set.mm's `x e. y` is `"classElement"["setClass"[x], "setClass"[y]]`, which is not `Element[x, y]` but
equivalent to it. Two equalities of functions carry one to the other:

- `"classElementFunction"`: `(B, z) |-> "classElement"["setClass"[z], B]` equals `(B, z) |-> B[z]`;
- `"setClassEqualFunction"`: `(x, y) |-> "setClass"[x] == "setClass"[y]` equals `(x, y) |-> x == y`.

`setmmTheorem[label, statement, proof]` uses them: the held statement with every `"classElement"["setClass"[t], B]`
replaced by `K[B, t]` is the motive of one `"equalitySubstitution"`, and with every `"setClass"[a] == "setClass"[b]` also
replaced by `L[a, b]` that of a second; at the right-hand functions the statement is about `Element` and `==` of sets,
which the model's theorem proves. So `"ax-pow"` is `"powerSet"` and `"elementOfPower"`, and so on.

## set.mm's axioms, under their labels

The axioms are stated exactly as MetamathLink translates them, in higher-order abstract syntax:

- a setvar variable is a bound variable of type `"Set"`; a wff or class variable is a parameter, a function of the
  setvar variables of the frame it has no `$d` with, in the order of the frame's floating hypotheses;
- each essential hypothesis and the conclusion are closed over the frame's setvar variables:
  `ForAll[{φ, ...}, Implies[ForAll[setvars, e1], ... ForAll[setvars, c]]]`;
- the primitive connectives are native: `wn` `Not`, `wi` `Implies`, `wb` `Equivalent`, `wa` `And`, `wo` `Or`, `wal`
  `ForAll`, `wex` `Exists`, `wtru` `True`, `wfal` `False`.

`"ax-mp"`, `"ax-1"`..`"ax-3"`, `"df-bi"`, `"df-an"`, `"df-or"`, `"df-tru"`, `"df-fal"`, `"df-ex"`, `"ax-gen"`,
`"ax-4"`..`"ax-13"`, `"df-clab"`, `"df-cleq"`, `"df-clel"`, `"ax-ext"`, `"ax-rep"`, `"ax-sep"`, `"ax-nul"`, `"ax-pow"`,
`"ax-pr"`, `"ax-un"`, `"ax-reg"`, `"ax-inf"`, `"ax-ac"`. `"wsb"`, set.mm's substitution `[ t / x ] ph`, is defined as
`df-sb` defines it, so that `df-clab` can be stated. The justification hypotheses of `df-sb`, `df-cleq` and `df-clel`
are premises the proofs do not use. The intuitionistic axioms (`ax-1`, `ax-2`, `ax-gen`, `ax-4`, ...) need no axiom at
all; `ax-3` and the definitions of the connectives need the classical ones.

The axioms set.mm derives itself are not here: `ax-inf2` and the axioms of the complex numbers (`ax-cnex` ...
`ax-pre-sup`) are proved by set.mm's own theorems `axinf2`, `axcnex` ... before it states them, and MetamathLink proves
each axiom by its theorem. `ax-cc`, `ax-dc` and `ax-ac2` are proved after they are stated (`axcc` ...); `ax-groth`, the
Tarski-Grothendieck axiom, needs an inaccessible cardinal and is not provable in this model.

## MetamathLink

The translation lives outside TypeTheory, in the MetamathLink paclet, as the Lean bridge lives in LeanLink. It reads a
database with `ResourceFunction["MetamathImport"]`, parses statements with a grammar built from the syntax axioms,
decodes compressed proofs, and builds proof terms that TypeTheory's kernel checks again. A `df-` axiom whose left side
is a new syntax axiom applied to distinct variables becomes a `TypeTheoryDefinition` and a theorem proved by
reflexivity. Where a proof applies an assertion with the same variable for two setvar variables (set.mm's bundled
theorems), which in higher-order abstract syntax is another statement, MetamathLink proves the variant by the
assertion's own proof with the variables merged.
