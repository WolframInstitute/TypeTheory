# ZFC in TypeTheory: Aczel's model, and set.mm's axioms as theorems

`TypeTheoryEnvironment["ZFC"]` (`TypeTheory/Kernel/Library/ZFC.wl`) is the prelude with a model of ZFC. No declaration
of the file is an axiom: every axiom of ZFC is a theorem proved from the prelude's three axioms,
`"propositionalExtensionality"`, `"quotientSoundness"` and `"choice"`. The tests ask that the environment's axioms are
the prelude's and give the closure of each axiom.

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
| infinity (x in a set where every member is in another member) | `"infinity"` | the range of `"singletonIterate"[x, n]` over the natural numbers |
| replacement | `"replacement"` | the range of chosen values; functionality makes any value equal to the chosen one |
| choice (one member of each nonempty member of x, unique) | `"choiceAxiom"` | the pairs `{w, c(w)}`; uniqueness from `"elementIrreflexive"`, `"elementAsymmetric"` and `"chosenElementCongruence"` (proof irrelevance) |

## Classes

A class is a predicate, `"Class" = "Set" -> Prop`: `"setClass"[x]` is the class of the members of `x`, `==` is equality
of classes, `"classElement"[A, B]` is `Exists[{a}, A == "setClass"[a] && B[a]]`, `A` a set and a member of `B`, and
`"classAbstraction"[P]` is the class `{x | P[x]}`. `"classElement"["setClass"[x], "setClass"[y]]` is not
`Element[x, y]` but equivalent to it, and two equalities of functions carry statements about classes of sets to
statements about sets:

- `"classElementFunction"`: `(B, z) |-> "classElement"["setClass"[z], B]` equals `(B, z) |-> B[z]`;
- `"setClassEqualFunction"`: `(x, y) |-> "setClass"[x] == "setClass"[y]` equals `(x, y) |-> x == y`.

A statement in the class vocabulary with every `"classElement"["setClass"[t], B]` replaced by `K[B, t]` is the motive of
one `"equalitySubstitution"` along the first, and with every `"setClass"[a] == "setClass"[b]` replaced by `L[a, b]` that
of a second; at the right-hand functions it is a statement about `Element` and `==` of sets, which the model proves.

## Metamath

The classes are the vocabulary of set.mm, Metamath's database of ZFC, whose `x e. y` is `( cv x ) e. ( cv y )`. The
MetamathLink paclet, kept outside TypeTheory as LeanLink is, states set.mm's axioms under their labels over this
environment and proves each from the model's theorems by the substitutions above, with no axiom of its own, and
translates set.mm's proofs to proof terms that TypeTheory's kernel checks.
