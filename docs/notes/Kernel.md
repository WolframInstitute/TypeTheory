# Kernel design notes

Decisions behind the prototype's kernel and elaborator, and the gaps they leave. The full design,
including the Lean bridge and the compiled kernel, is
[docs/research/TypeTheoryEngine.html](../research/TypeTheoryEngine.html).

## Representation

Core terms are locally nameless. Bound variables are de Bruijn indices, free variables are integers
naming entries of a local context (`<|id -> <|"Name", "Type", "Binder"|>|>`), and going under a binder
opens it with a fresh free variable. The kernel never handles loose indices, and alpha-equivalent terms
are identical expressions, so `SameQ` and `Association` keys compare them structurally.

Every name is held, `HoldComplete[name]`, in binders and in constant references, because the prelude's
constants are built-in symbols (`Equal`, `Plus`) and user names may have values.

A universe level is normalized to a maximum of components, each an integer or a base with an offset.
`levelEquivalentQ` compares normal forms. `levelLessEqualQ` is sound but incomplete: it can reject a
true inequality between levels with parameters, which would reject a valid declaration, never accept a
false one.

## The kernel

`inferType` checks: an application checks its argument, a binder checks that its domain is a type, a
local definition checks its value. Proof irrelevance, K-like reduction, η for structures and unit types
ask types too (`typeQuery`). Inside a declaration's check they infer them without checking, as Lean's
kernel does in infer-only mode: arguments are not checked against their binders, nor domains as types,
nor local values against their types. That is sound only where every term compared is checked or a
reduct of a checked term. A declaration's check is such a place, since it checks the type before the
value and each subterm before comparing the types of its parts. `withCheckedTerms` marks such a place:
the declarations, inductive blocks, quotients and cubical primitives, and `DefinitionallyEqualQ`, whose
terms are checked as their elaboration finishes. Elsewhere, in the elaborator and in tactics, the
queries check. A type inferred without checking goes to a cache of its own, so a check never takes it
for a checked one. Every call of `definitionallyEqualQ` outside `TypeChecking.wl` says in a comment
which of the two its terms are. A test in `Queries.wlt` forges theorems whose ill-typed proof is reached
only through proof irrelevance, and the declaration's own check catches each one.

Reduction is β, ζ, δ for definitions (theorems and opaque definitions are never unfolded), ι, K-like ι,
and the registered operations on natural number literals, on integers. Definitional equality decides
in Lean's order. First come `SameQ`, sorts, literals and binders. Then each side is reduced without
unfolding a definition, and the reducts are compared again if either changed. Where neither changes,
proof irrelevance answers for proofs: True for proofs of one proposition, False for proofs of two
different ones. Otherwise Lean's lazy delta reduction runs, and finally η, literals against
constructors, spines, η for structures and unit types. Lazy delta reduction unfolds one definition
at a time: of two definitions at the heads of the sides, the higher one, where a definition's height
is one more than the greatest height of the definitions its value mentions, or both at the same
height. As in Lean's kernel it is a loop that compares the sides between steps only by identity, and
by their arguments where one definition is at both heads, from the first pair on. It stops when
neither side has a definition at its head, and that last pair is compared in full. Proof irrelevance
is not asked again between steps, since unfolding leaves a proof a proof of the same proposition.
The kernel remembers inferred types, weak head normal forms and definitional equalities for the
length of a check.

A kernel failure is `Throw[Failure[tag, ...], $kernelFailureTag]`. Every exported function catches it
with `catchKernelFailure`, so a user sees a `Failure` and never a message.

## Inductive families

`declareInductiveType` follows Lean 4's kernel for a single family without nesting:

- the type is a telescope of parameters and indices ending in a sort;
- each constructor takes the parameters first, with the same types, and ends in the type applied to
  those parameters;
- the type occurs strictly positively, and never in an index of a constructor's result;
- fields live in universes no larger than the type's, unless the type is a proposition.

The recursor eliminates into any universe unless the type may be a proposition and has more than one
constructor, or a field that is neither a proof nor an index of the result. A proposition with one
constructor and no fields, such as `Equal`, gets K-like reduction. The recursor type and its reduction
rules are built with free variables and abstracted at the end, and both are type-checked before they
are added.

Mutual and nested families are rejected: nesting is caught as a non-positive occurrence.

## Natural numbers

The literal extension computes `m + n` on integers, so the kernel must know that this agrees with the
registered addition. `registerNaturalNumbers` therefore checks the shape of the type and its two
constructors, and requires addition to be, up to bound variable names, exactly
`Function[{m, n}, InductiveRecursor[type][Function[t, type], m, Function[{k, r}, successor[r]], n]]`.
Any other operation on literals (subtraction, multiplication, comparison) needs the same treatment: a
canonical definition to compare against.

## Environments

An environment is a value. Declaring returns a new environment; `$TypeTheoryEnvironment` is just the
default, which the `Declare` functions update on success. `TypeTheoryCheck[environment]` replays each
record in order with the core declaration functions and requires the regenerated records to be
identical. Constructors and recursors are regenerated with their inductive type, and the natural
numbers are registered again as soon as the constants they name exist. This is the defense against a
hand-written environment; the tests forge a theorem statement, a recursor and the addition.

## Elaboration

The elaborator is untrusted and its output is always re-checked. Its state is bound with `Block` for
one elaboration: metavariable types and assignments, level assignments, the local context and the scope
of names.

- A metavariable has no local context of its own. A solution that names a variable from inside a
  binder can therefore escape it. The two mitigations are filling solved metavariables into binder types
  before abstracting (`instantiateContext`) and the kernel's final check, which reports any escape that
  remains. Lean's delayed assignments are the real fix.
- Unification is first-order with a fallback to weak head normal form, plus higher-order patterns:
  `?f[x1, ..., xn] =?= t` with distinct context variables solves `?f` as a function.
- Assigning a metavariable unifies its type with its solution's type, which solves universe levels.
- In an application, an argument whose expected type has an unsolved metavariable at its head waits
  until the application's type has been unified with the expected type.

## Proof states

A goal is a metavariable of the proof state, with a context, a type and, after induction, the
constructor it came from. "Introduce" records its solution as `pendingAbstraction[context, ids, body]`,
which becomes a function only once `body` is complete. This is the prototype's stand-in for delayed
assignments. Goals may mention other goals; the elaborator sees their types through
`$goalMetavariableTypes`, and a solution it finds for one of them is kept.
