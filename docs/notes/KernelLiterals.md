# Large literals in elaboration and definitional equality: design note

Status: proposal for review (Stephen), 2026-11-06. Items (1) and (2) of the TypeTheory kernel findings.

## What the measurements show

The two items have different causes, and only (2) is in the trusted kernel.

**(1) `Typed[2^k, Integers]`: elaboration reduces without caches.**
- Case: `TypeTheoryType[Typed["equalityReflexivity"["true"], "integerLessEqualQ"[Typed[5, Integers], Typed[2^k, Integers]] == "true"], env]`.
- Time: 1.0 s at k = 11, 2.0 s at k = 12, 31 s at k = 16.
- Calls to `weakHeadNormalForm` grow as 2^k: 1465, 5345 and 20745 at k = 6, 8 and 10. `definitionallyEqualQ` stays at 30 calls.
- Every one of those calls runs with `$weakHeadNormalFormCache` inactive. The stacks show `finishElaboration` → `propositionPreferred` → `finishApplication`: elaboration unifying the application's type with the expected one. The final kernel check makes none of them.
- `integerPower` on quotient classes builds pairs whose components repeat the term below. Without a cache, each projection reduces that term again, so the work doubles at each step.
- With the kernel's caches around the same query, it takes 0.02 s at k = 12, 0.03 s at k = 16 and 0.08 s at k = 63.

**(2) A literal offset in definitional equality: a descent of c steps.**
- `DefinitionallyEqualQ` of `m |-> (0 + (m + c)) + 0` and `m |-> m + c` takes 0.17, 0.33, 0.56 and 0.84 s at c = 250, 500, 1000 and 2000: linear in c.
- Inside the `LinearArithmetic` lemma at c = 2^63, 15 s hold 207595 calls to `weakHeadNormalForm` and 207559 literal operations, one step each, without end.
- The heads are equal (`Plus`) and the arguments differ, so `+` unfolds. It recurses on its second argument, the literal, one successor at a time: `m + c` is `successor[m + (c - 1)]`, and so on c times, down to `0 + m` against `m`, which isn't definitional anyway.
- Caching does not help: each step's term is new.
- Lean's kernel meets the same shape and avoids it with an offset rule (`is_def_eq_offset_nat`): it compares `x + k` with `y + k'` by their offsets, without unfolding k times.

## Routes

**(1): elaboration only, no trusted code changed.**
- Elaboration runs each kernel query it makes (`weakHeadNormalForm`, `inferType`, `definitionallyEqualQ`) in a fresh cache scope of its own: `Block`ed caches, `<||>`, per query.
- `unify` already does this for one call (`Elaboration.wl`, `withKernelCaches[definitionallyEqualQ[…]]`).
- Why per query: reduction reads `$metavariableAssignments` (`TypeChecking.wl`, `reduceSpine` of an assigned metavariable), and assignments change and are undone between queries (`attemptOrRestore`). Within one query they don't change, since no query assigns. So an entry made in a query is valid for the whole of that query.
- The check in `finishElaboration` gets a fresh scope too. Today it calls `withKernelCaches`, which reuses an enclosing scope; it should `Block` the caches to `<||>`, so the trusted check never reads an entry made during elaboration.
- Soundness: the trusted code is unchanged, and so are its results. A cache entry is a result the kernel's own functions derived, keyed by structural identity (`{environment, term}`, `{environment, a, b}`), and used only inside the query that derived it. Elaboration's output is still checked by the kernel, from empty caches.

**(2): your route (b) narrowed to an offset rule, in the trusted kernel.** Route (a) does not apply: no subterm repeats in the descent.
- **Scope:** a new case of `definitionallyEqualCases` for the registered natural numbers only, as Lean's.
- **Offset form:** a term written as a base and an offset, `offset[t] = {base, k}`, read off by:
  - a literal n is `{zero, n}`;
  - `successor[t]` is `offset[t]` with k + 1;
  - the registered `Plus[t, n]`, with n a literal, is `offset[t]` with k + n;
  - anything else is `{t, 0}`.
- **The rule:** for `a` and `b` with offsets `{x, k}` and `{y, k'}`, at least one offset nonzero, and k ≤ k' (symmetric otherwise), `a ≡ b` iff `x ≡ y + (k' − k)` written back in offset form. With both bases `zero`, that is `k == k'`. An offset smaller than both sides compares the bases at once. The literal arithmetic is on k and k' only, Wolfram Language integers, as the registered operations already compute on literals.
- **Agreement with unfolding:** each step of the rule is a step the kernel takes itself:
  - `Plus[t, n + 1]` unfolds by the definition of `Plus`, recursion on its second argument, to `successor[Plus[t, n]]`;
  - `successor[s] ≡ successor[s']` iff `s ≡ s'`, by constructor injectivity in defeq: same constructor, compare arguments;
  - a literal `n + 1` is `successor[n]` (`NaturalNumbers.wl`).

  So the rule decides what k ↑ k' steps of unfolding would decide, and doesn't decide anything else.
- **The test of agreement**, as you asked:
  - Small range: every pair of terms from bases {zero, x, y, successor[x], x + y} with offsets 0..12, built in each of the three offset forms, compared with the rule on and off. The off path is today's unfolding, which terminates in this range. The results must be equal.
  - Random large: offsets up to 2^64, checked by an independent route. Two terms with a common base and offsets k and k' must be equal iff k == k'; with different variable bases, never.
  - Forged-proof tests: an equation that holds only after a nonzero offset difference, `x + 5 == x + 6`, must stay rejected. So must `Typed["equalityReflexivity"[x + 5], x + 5 == y + 5]` for distinct variables x and y.

## Acceptance

- `2^16` under a second, and `2^63` finishing: (1).
- The `c = 9223372036854775808` lemma under a set memory cap, `MemoryConstrained` inside plus the outside footprint watchdog: (2).
- The whole TypeTheory suite unchanged, today 456 of 456.

Order: (1) first, since it touches no trusted code; then (2), after this note is reviewed.
