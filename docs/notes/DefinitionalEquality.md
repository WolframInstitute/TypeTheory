# Definitional equality: Lean's caches and TypeTheory's

This note compares how Lean 4's kernel decides definitional equality, and what it remembers while
doing so, with `TypeChecking.wl`. It covers each cache's contents and key, how long an entry stays
valid, what Lean's caches save that TypeTheory's `{environment, a, b}` cache does not, and the order
of the checks. Lean's sources are `src/kernel/type_checker.cpp`, `type_checker.h`, `equiv_manager.cpp`
and `declaration.cpp`, at the tags v4.29.0 and v4.35.0. The equivalence manager is in the first and
gone by the second.

## 1. Lean's state, and how long it lives

`type_checker::state` holds every cache. `environment::add` makes a new `type_checker`, so a new
state, for each declaration it adds (`environment.cpp`). Every cache therefore lives for the
check of one declaration, as TypeTheory's `withKernelCaches` does. The state holds:
- `m_infer_type[2]`, the inferred types, one table for checking and one for infer-only inference;
- `m_whnf_core` and `m_whnf`, the weak head normal forms without and with δ;
- `m_unfold`, the instantiated bodies of unfolded constants;
- the equivalence manager (v4.29.0), replaced by the success set `m_success` (v4.35.0);
- the failure set `m_failure`, in both versions.

An entry stays valid across local contexts for the same reason TypeTheory gives in
`TypeChecking.wl`. Kernel terms hold no metavariables, and a free variable is fresh for each binder
opened, with one fixed type. So a term means the same wherever it occurs within one declaration's
check, and `is_def_eq`'s answer is a function of its two arguments. Lean's v4.35.0 header states this
argument for its pair sets.

## 2. The equivalence manager (to v4.29.0)

**Contents.** A union-find over expressions: a node for each expression met, looked up through a
hash map keyed by structural equality, merged by rank.

**When entries are added.** Only on success. The public `is_def_eq(t, s)` calls `is_def_eq_core`, and
when that returns true it merges the classes of `t` and `s` (`add_equiv`). Failures are never added.

**When it is asked.** `quick_is_def_eq` asks it first, through `is_equiv(t, s, use_hash)`:
- the first check of `is_def_eq_core` asks with `use_hash = true`, so terms of different hashes are
  not equivalent there, which keeps that check cheap;
- the check after `whnf_core` and the check after each lazy-δ step ask without hashes.

**What it decides.** `is_equiv_core` answers, in order:
- pointer-equal terms are equivalent;
- bound variables are equivalent when their indices are;
- terms whose classes share a root are equivalent;
- otherwise it walks both terms structurally (application: function and argument; binder: domain and
  body; constant: name and levels; projection; let; literal; sort). If the walk succeeds, it merges
  the roots, so the structural equality is remembered too.

It therefore decides equality modulo the congruence closure of the equalities proven so far, with no
reduction at all.

**What it saves:**
- symmetry and transitivity of proven pairs;
- congruence: `f a` against `f c` succeeds at once by the structural walk when `a ≡ c` was proven;
- repeated structural comparisons of large equal terms.

**Why v4.35.0 dropped it.** Its header comment, paraphrased: `is_def_eq` is sound but incomplete,
so as a procedure it is not transitive. Closing its successes under transitivity made the
results depend on the order of the checks. Plain pair sets replace it, and keep the results
independent of that order.

## 3. The success set (v4.35.0)

**Contents.** Unordered pairs `{t, s}` for which `is_def_eq` succeeded. A pair is stored with the
term of smaller hash first. On equal hashes both orders are looked up.

**When entries are added.** After every successful public `is_def_eq`, as `add_equiv` was.

**When it is asked.** In `quick_is_def_eq`, beside `t == s`. That is at the start of `is_def_eq_core`,
after `whnf_core`, and after every lazy-δ step.

**What it saves.** A repeat of a proven pair, in either order, at any of those three points.

## 4. The failure set (both versions)

**Contents.** Unordered pairs `{t_n, s_n}` as in §3. These are not failures of `is_def_eq` in
general, only failures of one shortcut inside `lazy_delta_reduction_step`.

**The shortcut.** It applies when both sides are applications whose heads are the same definition
(the same declaration object) with regular hints at the same height:
- if the pair failed before, the step skips straight to unfolding both sides;
- otherwise it compares the universe levels and then the arguments (`is_def_eq_args`, each argument
  through `is_def_eq`, so their successes are cached);
- if that comparison fails, the pair is recorded.

**What it saves.** The argument comparison of a stuck pair met again, in another branch or another
round. A failing argument comparison can be long, since each argument may unfold far before it
fails.

## 5. TypeTheory's cache

**Contents.** `$definitionalEqualityCache`, an `Association` keyed by the ordered list
`{environment, a, b}`, holding `True` or `False` for the whole of
`definitionallyEqualCases[environment, context, a, b]`. Unlike Lean's sets it holds failures of the
whole procedure, not only of one shortcut.

**When it is asked.** At `definitionallyEqualQ`'s entry only, after `a === b`.

**Lifetime.** One `withKernelCaches` block, one declaration's check, as Lean's state.

Compared with Lean's caches:
1. **No symmetry.** `{environment, b, a}` is another key, so `b ≡ a` is decided again after `a ≡ b`.
   Storing and looking up the pair in a canonical order fixes it, for example the two terms in
   `Order` order.
2. **No lookup between lazy-δ steps.** `lazyDeltaEqualQ` compares each new pair only by identity.
   Lean asks its success set after every unfold. Looking each new pair up in the cache:
   - **True** ends the loop: the pair was proven.
   - **False** ends it too, with `False`: unfolding preserves definitional equality, and the
     cached value was computed for that very pair.
3. **The argument shortcut is cheaper in Lean, but no different in kind.** `sameHeadArgumentsEqualQ` is
   not cached as a whole. Every argument comparison is, `True` or `False`, so a repeat costs two
   spines and one lookup per argument up to the failing one, against Lean's single pair lookup.
   That is a constant factor.
4. **Congruence.** TypeTheory gets it through `sameHeadArgumentsEqualQ` and the per-argument cache,
   at the cost of spines and lookups. Lean's current kernel has no congruence closure either, and
   still checks the two `IntermediateField` constants in milliseconds, so the closure is not what
   they need.
5. **The environment in the key.** It is fixed within a check, so it only adds work to each lookup:
   hashing a list that holds the whole environment, and comparing it. Measure whether Wolfram
   caches that hash and shares the object, so it costs nothing, or not. If not, key on `{a, b}`
   inside the block.

The caches account for constant factors. Minutes against milliseconds on constants that pass
under eager unfolding point instead at the order of unfolding: §6.

## 6. The order of the checks

| Lean, `is_def_eq_core` | TypeTheory, `definitionallyEqualQ` |
|---|---|
| 1. quick: success set (or equivalence manager); binders, sorts, literals of the same kind | `===`, the cache; `definitionallyEqualCases`' rules for sorts, literals and binders |
| 2. `decide`: if `t` has no free variables (or under `eagerReduce`) and `s` is `Bool.true`, `whnf(t)` and compare with `Bool.true` | none |
| — | the same constant applied to equal arguments (`sameHeadArgumentsEqualQ`), before any reduction |
| 3. `whnf_core` of both, without δ and with cheap projections; the quick check again if either changed | `reducedEqualQ`: `reducedHeadWithoutUnfolding` of both, without δ, but its projection case (`reduceProjection`) reduces the structure by `weakHeadNormalForm`, δ included, as Lean's `whnf_core` with `cheap_proj = false` would; the whole of `definitionallyEqualQ` if either changed |
| 4. proof irrelevance | `proofIrrelevantEqualQ`, before reduction |
| 5. lazy δ: hints order the unfolding; a projection application on one side is unfolded before the definition on the other; the argument shortcut with the failure set; offsets of `Nat.succ`; the quick check after each step | `lazyDeltaEqualQ`: heights only; no projection rule, nor a need for one, since 3 reduced every projection it could; the argument comparison at the same height, but for the first step; identity between steps |
| 6. the same constant with equal levels; the same free variable | in `headsEqualQ`, under `spinesEqualQ` |
| 7. projections of the same index: `lazy_delta_proj_reduction` of the structures | `headsEqualQ` compares the structure terms, but only of projections whose structures 3 left stuck |
| 8. `whnf_core` with projections reduced by `whnf`; again from the top if either changed | none at this point |
| 9. `is_def_eq_app` on the weak head normal forms | `spinesEqualQ` in `normalFormsEqualQ` |
| 10. η, η for structures, string literals, unit-like types | `etaEqualQ`, `structureEtaQ`, `literalEqualQ`, `unitEqualQ` |

The differences that can cost minutes:
- **Projections (3, 7).** TypeTheory reduces a projection's structure with δ at the step where
  Lean uses cheap projections.
  - **No case for Lean's projection rule.** Lean's `try_unfold_proj_app` reduces a projection
    application before the definition on the other side (its comment's case is
    `expensive_term =?= instFoo.1 a`). In TypeTheory, `instFoo.1 a` is reduced before lazy δ
    begins.
  - **The risk runs the other way.** For `x.i =?= y.i`, with `x` and `y` different terms that are
    equal, TypeTheory unfolds both structures in full. Lean compares `x` with `y` first, lazily
    (`lazy_delta_proj_reduction`), and reduces them only if that fails. Instance projections are
    everywhere in `IntermediateField`, so this is the first thing to test on the two constants.
- **Hint kinds (5).** In Lean's `compare` (`declaration.cpp`):
  - two regular definitions unfold the higher first, or both at equal height;
  - an abbreviation unfolds before a regular definition;
  - a definition with opaque hints unfolds last;
  - two of one kind other than regular unfold together.

  TypeTheory has heights only. Check what the Mathlib import does with `ReducibilityHints.abbrev`
  and `ReducibilityHints.opaque`.
  - **Opaque hints.** Lean's `is_delta` unfolds every constant with a value. A definition with
    opaque hints is still unfolded, unlike an `opaque` declaration, which TypeTheory's `"Opaque"`
    kind matches.
  - **Theorems.** Lean also unfolds theorems, which `get_hints` gives opaque hints, so they unfold
    last. TypeTheory never unfolds a theorem (`Kernel.md`). Proof irrelevance decides most
    comparisons of proofs, so this rarely matters.
- **`decide` (2).** The five `decide` proofs on `ZMod` characters are the shape Lean's shortcut serves:
  `Eq.refl true : decide p = true`, decided by evaluating the closed side in one `whnf`.
  `TypeChecking.wl` has no such path, so the comparison runs through lazy δ.
- **Arguments before reduction.** `sameHeadArgumentsEqualQ` runs first on every pair whose head is
  a constant, recursors and constructors included. Lean compares same-head arguments only inside
  lazy δ, for definitions at equal height, and on weak head normal forms (`is_def_eq_app`). A
  recursor application that ι-reduces at once is compared argument by argument first.

## 7. What to try, in order

1. Projections of the same index compared by their structures before either is reduced. That
   takes projections left unreduced in `reducedHeadWithoutUnfolding`, as Lean's cheap projections
   are. Measure it on `IntermediateField.Lifts.le_union` and `exists_lift_of_splits'`.
2. Hint kinds from the import, abbreviations first and opaque hints last, if the import drops them.
3. The `decide` shortcut, on the five `ZMod` constants.
4. The cache, keyed by an ordered pair without the environment, and asked between lazy-δ steps.
5. The failure set for `sameHeadArgumentsEqualQ` inside `lazyDeltaStep`, if the profile still shows
   repeated argument comparisons after 1–4.

Lean's union-find closure is not worth adding: its own kernel no longer has it.
