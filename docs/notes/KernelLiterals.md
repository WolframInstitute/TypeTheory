# Large literals in elaboration and definitional equality: design note

Status: (1) built (4c9cdc8). (2) built and approved by Stephen, 2026-11-07: the offset rule, read through Plus, the registration check that justifies it, and literal values read by offsets (see Result of (2)). Items (1) and (2) of the TypeTheory kernel findings.

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

## Result of (1)

A fresh cache per query was not enough: 2^12 still took 2.0 s and 2^16 31 s. The repeated work spans queries, as
unify asks about the same closed subterms again and again. The condition that is safe is narrower: cache only terms
with no metavariable, whose reduction and type no assignment changes, for the whole elaboration
(`$cacheClosedTermsOnly`). The trusted check after elaboration starts from fresh caches. Measured: 2^12 in 0.05 s, 2^16
in 0.06 s, 2^63 in 0.3 s. Checked: with `TYPETHEORY_CHECK_QUERIES=True` every elaboration asserts that no cache
remembers a term with a metavariable, and the suite passes 456/456 with it on. The suite run with elaboration's caching
on and forced off (`TYPETHEORY_ELABORATION_CACHES=Off`) logs 2460 checked results, which are byte for byte the same
once the identifiers and Module symbols are numbered by first appearance.

## Result of (2)

Built as in the routes below, with one more change the lemma showed. The c = 2^63 lemma did not finish with the rule
alone. Its descent was in the literal extension: to compute `0 + (m + c)`, `literalOperationResult` asks whether `m + c`
is a literal, and `literalValue` took its weak head normal form and peeled successors one at a time, 2^63 of them,
before it reached the base `m` and gave None.

`literalValue` now reads a term's offset first, with the reading of the rule, `{base, k}`, and then reduces the base and
reads it again: the value is k over zero, k more than the base's value, or None once a base reduces no further and is
no literal, zero or successor. Each step is literal semantics, the constructor, or one of the two equations of addition.
**So the registration check carries `literalValue` too:** an addition that fails the equations would make the literal
values wrong, not only the definitional equalities. The `reduced === base` check stops the loop on a stable weak head
normal form. It is complete because a stuck base made the old loop end in None as well.

Measured, with the values injected by `With`:
- the measured case, `(0 + (m + c)) + 0` against `m + c`: 0.007 s at c = 2000 and at c = 2^63 (0.84 s at c = 2000 before);
- (1): 2^12, 2^16 and 2^63 in about 0.01 s each;
- the c = 2^63 lemma: 0.035 s, under a 2 GB memory limit; with the rule alone it aborted at 60 s. It is a test in
  `Checking/NaturalNumbers.wlt`.

`scripts/offset_agreement.wls` checks the agreement: the 38025 pairs of the test of agreement below, with the rule on and
off, agree, 801 of them equal; the literal values of their 195 terms and of the 38025 sums agree with peeling, 1560
integers and 36660 None; and 120 terms with random offsets up to 2^64, which peeling cannot finish, have the offsets'
sums for values. The suite has the pairs of offsets 0 to 4. Elaboration's `unify` gives two terms with no metavariable
to the kernel's definitional equality, so a forged `x + 2^63 == x + 2^63 + 1` is a type mismatch, not a recursion limit.

Two corrections followed, approved 2026-11-07. `literalValue` recursed once per reduction, so a value many
reductions deep, as `Twice[1000]` of a recursion by two successors, reached the recursion limit: it now reads in a loop,
as the old peeling did. And `literalValues` gives None at once when an argument is stuck, read without reducing: a
variable without a value, a successor of one, or a sum by the registered addition with one, since a sum is a literal only
where both sides are, by the checked equations. Without it, `X * N` unfolded into `Plus[ℕ_rec[..., N - 1], X]` was reduced
N deep before the variable sum `X` was seen, which a certificate of `LinearArithmetic` with a coefficient that grows with
the constant met. The script also checks that every term read as stuck has no literal value by peeling: all 36660 of
the None values are read as stuck.

Then the ordering, approved 2026-11-07, which the machine layer's bound needed: a natural number below 2^63 is in the
range of the machine integers. Its check took `literalValue` of the first component of the pair of `m + 2^63`. Weak head
reduction projected out `Plus[m, 2^63]` and went on: the literal operation failed, as `m` is a variable, and the
definition unfolded into its recursor, whose iota on the literal exposed one successor, so the offset was no longer
readable and 2^63 successors were peeled one by one. Lazy delta unfolded the addition in definitional equality the same
way, before the rule could read through it.

- **The registered addition reduces by its two checked equations, its recursion folded,** never into its recursor:
  with the second argument reduced, `t + zero` is `t`, `t + n` for a literal `n > 0` is `successor[t + (n - 1)]`,
  `t + successor[s]` is `successor[t + s]`, and `t + s` stays as it is where `s` is stuck. Each result is the same sum by
  one equation; the recursor reaches a constructor exactly where the second argument does, and the same one. So every
  later reading, `literalValue`, the offset rule and lazy delta, still sees the offset. Lazy delta still unfolds a stuck
  addition as any definition, so a sum written as its recursor is equal to it. `$foldedAddition` turns it off for the
  agreement test.
- **The offset rule is a loop,** at one depth: both offsets positive, the smaller is stripped; one offset 0 over a base
  that is not zero, against a positive one, that base is reduced and read again; two numerals are decided by their
  numbers; and what is left once neither side has an offset to strip is compared once by general definitional equality.
  A rule that recursed once per round overflowed the stack of W15 (w15-bugs §69): `Twice[2900] + 1` against 5801, 1450
  rounds, crashed the process.

Measured: the three bridge lemmas on the literal 2^63 in 0.41 s together (aborted at 300 s and 2.3 GB before);
`Twice[2900] + 1` against 5801 and 5802 in 0.94 s, `Twice[20000] + 1` in 6.5 s. The agreement script adds 150 additions
written as their recursor, applied to a successor, inside a sum and under a successor, which are equal, and with a step of
two successors, which are not, but where the recursion takes no step: with the rule and the folded addition on and with
both off, all of them agree with each other and with what is expected, and so does everything else in the script.

## Registrations and the trusted base

Approved by Stephen, 2026-11-07, after a registration proved `False` with an empty axiom closure: a projection
registered as the greatest common divisor computes `FirstNumber[2, 3]` as 1 on literals, and unfolds to 2, so
`1 == 2`. The rule since:

- **Checked:** an operation with defining equations is checked against them by computation, for variables, when it is
  registered, and refused where one fails. The equations are those the prelude's definitions satisfy:
  - addition: `t + zero == t`, `t + successor[s] == successor[t + s]`;
  - multiplication: `t * zero == zero`, `t * successor[s] == t * s + t`, with an addition registered;
  - power: `t ^ zero == successor[zero]`, `t ^ successor[s] == t ^ s * t`, with a multiplication registered;
  - subtraction: `t - zero == t`, `t - successor[s] == predecessor[t - s]`, the predecessor by the recursor;
  - equality and order: `equal` and `lessEqual` on `zero` and successors, in four and three equations;
  - remainder and quotient, by recursion on the dividend with the divisor `s` fixed, with an equality registered, the
    quotient with a remainder too, and the choice by the recursor of the Booleans the equality gives:

        remainder[zero, s] == zero
        remainder[successor[t], s] == if equal[successor[remainder[t, s]], s] then zero else successor[remainder[t, s]]
        quotient[zero, s] == zero
        quotient[successor[t], s] == if equal[successor[remainder[t, s]], s] then successor[quotient[t, s]] else quotient[t, s]

    With `s` zero the remainder plus one is never `s`, which gives Lean's `t % 0 = t` and `t / 0 = 0`.

  An operation equal to the prelude's only by a proof, as `isZero[(m - n) + (n - m)]` for equality, fails its
  equations: the kernel computes the role on literals, which must agree with what the definition computes.
- **Refused or trusted:** where the equations fail, an operation of a role the kernel reads terms through, addition for
  the offset rule, and multiplication, power, subtraction, equality and order, is refused. A quotient or a remainder is
  accepted and trusted: Lean's `Nat.div` and `Nat.mod` are defined by well-founded recursion, which does not compute on
  a variable, so the bridge from Lean is honest only by reporting them. Approved by Stephen, 2026-11-07.
- **Trusted:** an operation without equations, the greatest common divisor, the logarithm, the bitwise operations and
  the shifts, is accepted and trusted, as Lean's kernel trusts GMP. A trusted registration stays a trusted assumption:
  `TypeTheoryAxiomClosure` names it, as `"Registration"`, wherever a proof rests on it, so every role is either checked
  or in the closure. Whether a quotient or a remainder is trusted is decided where the closure asks, by its equations
  in the environment, so the natural numbers an environment stores keep their form. The prelude registers none of
  these. The greatest common divisor can follow by Euclid's equations, `gcd[zero, s] == s` and a step through the
  remainder.
- **The closure** names every trusted assumption a proof rests on: axioms, rewrite rules and unchecked registrations.
  An empty closure means the proof rests on the kernel alone.

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
  - the registered `Plus[t, s]` with `offset[s] = {b, k}`, k > 0, is `{Plus[t, b], k}`, and `{t, k}` where b is `zero`;
    `Plus[t, s]` with `offset[s] = {zero, 0}` is `offset[t]`;
  - anything else is `{t, 0}`.

  Reading offsets through `Plus` is what makes the rule finish on the case measured: `(0 + (m + c)) + 0` is
  `{0 + m, c}` and `m + c` is `{m, c}`, so one step strips c and compares `0 + m` with `m`, which the normal path refuses
  at once. Without it, each round exposes one successor of the left side, and the rule takes c rounds.
- **What justifies reading through `Plus`:** the two defining equations of addition, `Plus[t, zero] ≡ t` and
  `Plus[t, successor[s]] ≡ successor[Plus[t, s]]`. Registration today trusts the addition only to compute on literals
  as integer addition does, which does not imply them on open terms; an addition by recursion on its first argument
  satisfies the literal condition and not the equations. So `registerNaturalNumbers` (trusted) checks both equations by
  definitional equality, for fresh variables t and s, when an addition is registered, and refuses the registration
  where they fail. The offset rule then shortcuts k uses of equations the kernel has checked itself.
- **The rule**, for `a` and `b` with offsets `{x, k}` and `{y, k'}`:
  - both offsets positive: strip m = min(k, k') from both, and compare `x` with offset k − m against `y` with offset k' − m, written back in offset form, by general definitional equality. This is progress: it is m successor steps on each side, removed by constructor injectivity.
  - both bases `zero`, both sides literals or successors of them: decide k == k' directly.
  - one offset 0 over a base that is not `zero`: the rule does not apply. The normal path reduces that side to weak head normal form. If it becomes a successor or a literal, the rule applies on the next round with a positive offset; if it is stuck, the comparison goes on as today.
  The literal arithmetic is on k and k' only, Wolfram Language integers, as the registered operations already compute on literals.
- **Agreement with unfolding:** each step of the rule is a step the kernel takes itself:
  - `Plus[t, n + 1]` unfolds by the definition of `Plus`, recursion on its second argument, to `successor[Plus[t, n]]`;
  - `successor[s] ≡ successor[s']` iff `s ≡ s'`, by constructor injectivity in defeq: same constructor, compare arguments;
  - a literal `n + 1` is `successor[n]` (`NaturalNumbers.wl`).

  So the rule decides what k ↑ k' steps of unfolding would decide, and doesn't decide anything else.
- **The test of agreement**, as you asked:
  - Small range: every pair of terms from bases {zero, x, y, successor[x], x + y} with offsets 0..12, built in each of the three offset forms, compared with the rule on and off. The off path is today's unfolding, which terminates in this range. The results must be equal.
  - Random large: offsets up to 2^64, checked by an independent route. Two terms with a common base and offsets k and k' must be equal iff k == k'; with different variable bases, never.
  - Forged-proof tests: an equation that holds only after a nonzero offset difference, `x + 5 == x + 6`, must stay rejected. So must `Typed["equalityReflexivity"[x + 5], x + 5 == y + 5]` for distinct variables x and y.
  - Registration: an addition by recursion on its first argument, which computes the literals right, is refused, with
    the equation that fails named; the prelude's and the integers' registrations pass.
  - Termination, for the third case: `t` against `x + 3`, where `t` is a term whose weak head normal form is a successor, a definition unfolding to `successor[successor[successor[x]]]`, which must be found equal; and where `t` is stuck, an application of a variable, which must be found unequal, with no loop. Both run under a time limit.

## Acceptance

- `2^16` under a second, and `2^63` finishing: (1).
- The `c = 9223372036854775808` lemma under a set memory cap, `MemoryConstrained` inside plus the outside footprint watchdog: (2).
- The whole TypeTheory suite unchanged, today 456 of 456.

Order: (1) first, since it touches no trusted code; then (2), after this note is reviewed.
