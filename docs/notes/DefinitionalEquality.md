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

**Types inferred without checking.** The type queries inside a check infer only (§6, row 4), and
remember what they infer in a cache of their own, `$uncheckedTypeCache`, as Lean's second
`m_infer_type` table does. A checked type answers such a query, never the other way.

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
| 3. `whnf_core` of both, without δ and with cheap projections; the quick check again if either changed | `reducedEqualQ`: `reducedHeadWithoutUnfolding` of both, without δ, but its projection case (`reduceProjection`) reduces the structure by `weakHeadNormalForm`, δ included, as Lean's `whnf_core` with `cheap_proj = false` would; the whole of `definitionallyEqualQ` if either changed |
| 4. proof irrelevance | `proofIrrelevance` in `reducedEqualQ`, where neither side reduced; inside a check its type queries infer only (`typeQuery`) |
| 5. lazy δ: hints order the unfolding; a projection application on one side is unfolded before the definition on the other; the argument shortcut with the failure set; offsets of `Nat.succ`; the quick check after each step | `lazyDeltaEqualQ`: a projection function is an abbreviation (`"Hint" -> "Abbreviation"`), which unfolds before a regular definition, two of them together; of two regular definitions the higher first; no projection rule, nor a need for one, since 3 reduced every projection it could; the arguments of one regular definition at both heads, from the first step on (`sameHeadArgumentsEqualQ` in `lazyDeltaStep`); identity between steps |
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
  - **Structures compared in full.** For `x.i =?= y.i`, with `x` and `y` different terms that are
    equal, TypeTheory unfolds both structures in full. Lean compares `x` with `y` first, lazily
    (`lazy_delta_proj_reduction`), and reduces them only if that fails.

  Lean's cheap projections and projection rule together gain nothing on `le_union` (§7.2), where
  the abbreviation hints decide.
- **Hint kinds (5).** In Lean's `compare` (`declaration.cpp`):
  - two regular definitions unfold the higher first, or both at equal height;
  - an abbreviation unfolds before a regular definition;
  - a definition with opaque hints unfolds last;
  - two of one kind other than regular unfold together.

  TypeTheory has heights, and the abbreviation hint of a projection function, which it finds by
  the shape of its value (`projectionFunctionQ`). Lean's other hints come with the import (§7.4):
  those of `abbrev` definitions and of parent projections that are not subobjects, and the opaque
  hints.
  - **Opaque hints.** Lean's `is_delta` unfolds every constant with a value. A definition with
    opaque hints is still unfolded, unlike an `opaque` declaration, which TypeTheory's `"Opaque"`
    kind matches.
  - **Theorems.** Lean also unfolds theorems, which `get_hints` gives opaque hints, so they unfold
    last. TypeTheory never unfolds a theorem (`Kernel.md`). Proof irrelevance decides most
    comparisons of proofs, so this rarely matters.
- **`decide` (2).** The five `decide` proofs on `ZMod` characters are the shape Lean's shortcut serves:
  `Eq.refl true : decide p = true`, decided by evaluating the closed side in one `whnf`.
  `TypeChecking.wl` has no such path, so the comparison runs through lazy δ.

## 7. Measurements, and the order from here

### 7.1 Five checks under five variants

These are the slow failing checks the documentation's examples met, with one passing check for
comparison. All ran in one Wolfram 15.1.0 kernel, with a peak of 777 MB, each variant installed
over the eager order's definitions. Every variant gives every check the same answer.

| Check | Eager order | Projections | Irrelevance first | Irrelevance first, infer-only | Lean's order |
|---|---|---|---|---|---|
| a rational lemma applied to the wrong side (`TypeMismatch`) | 100 s | 105 s | 112 s | 37 s | 2.3 s |
| the integer lemma, likewise | 3.8 s | 4.0 s | 4.2 s | 1.6 s | 0.35 s |
| `3/4 + -3/4` against 0 (`False`) | 55 s | 55 s | 55 s | 1.4 s | 0.48 s |
| a cancellation off by one (`TypeMismatch`) | 103 s | 118 s | 116 s | 42 s | 4.4 s |
| the rational lemma on the right side (passes) | 0.07 s | 0.07 s | 0.07 s | 0.05 s | 0.04 s |

The variants:
- **Eager order:** same-head arguments compared and proof irrelevance asked before any
  reduction, with type queries that check each term again. The others are written over it.
- **Projections:** projections of one field compared by their structures and arguments before
  either is reduced (§6).
- **Irrelevance first:** proof irrelevance is asked before anything else. It answers `False` for
  proofs of two different propositions, as Lean's `is_def_eq_proof_irrel` does, and only then
  come same-head arguments, projections and reduction.
- **Infer-only:** the type queries of proof irrelevance and reduction infer without checking,
  from a cache of their own (§1).
- **Lean's order:** irrelevance first with infer-only queries, then projections and reduction.
  Same-head arguments are compared only inside lazy δ, for one definition at both heads, from the
  first step on.

What they show:
- **Failures carry the cost.** The passing check is fast under every variant.
- **Irrelevance first needs infer-only queries.** It buys nothing while its type queries check
  each term again. With infer-only queries it gives up to 40×, and Lean's order brings the rest:
  11× to 115× against the eager order.
- **The projection rule moves none of these.** Its case is `le_union`'s chain of structure
  comparisons (§7.2), where it takes the eager order's root from over 300 s to 181 s.

The kernel decides in Lean's own order (§6): reduction without unfolding, then proof irrelevance
where neither side reduces, then lazy δ, with infer-only queries inside a check. It takes the four
failing checks in 0.39 s, 0.14 s, 0.09 s and 1.69 s, 27× to 611× faster than the eager order.

### 7.2 `le_union`'s root

`IntermediateField.Lifts.le_union` is the check that took minutes. Its root alone, after its cone
of 5005 constants is imported (185 s under Lean's order, 206 s under the eager order), each order
run once in one kernel, every answer the same:

| Order | The root |
|---|---|
| eager order | over 300 s |
| Lean's order | 170.6 s |
| Lean's order, cheap projections | 178.9 s |
| Lean's order, projection functions as abbreviations | 14.5 s |
| both | 14.2 s |
| Lean | 22 ms |

- **Cheap projections:** reduction without unfolding reduces a projection's structure without δ,
  lazy δ unfolds a projection application before the definition on the other side
  (`try_unfold_proj_app`), and a last pass reduces projections in full before the spines are
  compared (§6, rows 3, 5 and 8).
- **Projection functions as abbreviations:** a definition whose value projects a field out of its
  last argument unfolds before a regular definition, and two of them unfold together without
  their arguments compared, as Lean's hints order its structure projections. `x.toRingHom`
  against a long composition then reads the field before the composition unfolds, where heights
  alone unfold the higher composition first.

The kernel has the abbreviations. In three warm runs of `typetheory_benchmark.wls` the root takes
14.1 s: 10.17 s of checking, 462× Lean's 22 ms, and 3.95 s of translating.

### 7.3 Whole cones against Lean

LeanLink's `typetheory_benchmark.wls` checks the cone of a declaration, every constant it depends
on, in TypeTheory and in Lean's kernel. The times are of checking, the median of three warm runs,
which agree within 3% but for one run of `binaryRec` with the abbreviations, 9.2 s.

| Cone | Constants | Eager order | Spine | And Lean's order | And the abbreviations | Lean | TypeTheory / Lean |
|---|---|---|---|---|---|---|---|
| `binaryRec` | 721 | 8.93 s | 7.82 s | 7.07 s | 7.51 s | 60 ms | 125× |
| `omega` | 1008 | 12.01 s | 11.02 s | 10.59 s | 10.52 s | 75 ms | 140× |
| `balanceL` | 1544 | 24.8 s | 22.14 s | 21.38 s | 21.35 s | 170 ms | 126× |

The spine is the inference of an application's type along its spine at once (`spineType`), as
Lean's kernel infers one: each argument is checked against its binder's domain with the arguments
before it put in, and the codomain is instantiated with all of them once at the end. Taken one
argument at a time, a spine of n arguments cost n substitutions of its function type's telescope.

What they show:
- **The spine gives 8% to 12%, and Lean's order 3% to 10% more.** These cones pass, so failing
  comparisons, where Lean's order gives its 27× to 611×, are rare in them.
- **The abbreviations cost `binaryRec` 6%,** beyond the runs' spread (its fastest run went from
  7.01 s to 7.42 s), and move the other two by under 1%. Where a projection function unfolds
  first, heights may have decided sooner; the profile is to show whether that is the cause.
- **The rest of the gap is elsewhere,** in parts no measurement has divided yet: inference that
  checks, the infer-only queries, weak head normal forms, instantiation, and hashing the caches'
  keys (§5, item 5).

### 7.4 The order from here

1. **A profile of `balanceL`'s check,** dividing its 21 s among the parts §7.3 names, and of
   `binaryRec`'s 6%.
2. **Hint kinds from the import:** Lean's `ReducibilityHints`, passed by the bridge as a role of
   `TypeTheoryDefinition` and kept through replay, so that every abbreviation Lean has unfolds
   first and opaque hints unfold last.
3. **The `decide` shortcut,** on the five `ZMod` constants.
4. **The cache,** keyed by an ordered pair without the environment, and asked between lazy-δ steps.
5. **The failure set inside `lazyDeltaStep`,** if the profile still shows repeated argument
   comparisons.
6. **Literal arithmetic for closed rational terms,** as Lean's kernel computes `Nat` literals, if
   failing comparisons of numerals stay slow.

Neither Lean's union-find closure, which its own kernel no longer has, nor cheap projections
(§7.2) is worth adding.
