# The universality of Wolfram's (2,3) Turing machine (design)

The user asked on 2026-11-20 to move the proof that Wolfram's (2,3) Turing machine is universal into TypeTheory. The
proof now lives in ~/src/wolfram/TuringMachineSearch/Proofs (Lean, built by the session "Turing"). The port has:
- a new environment, `TypeTheoryEnvironment["Wolfram23"]`, with fewer definitions than the Lean proof;
- a tutorial that proves each rung of Smith's chain of emulations;
- every proof checked by TypeTheory's kernel, and no Lean.

Turing reviewed this design against the Lean proof's plan (Proofs/docs/PLAN.md) and its source; its corrections are in.

## What is proved

The existential finite form, `Smith.wolfram23_universal`, by the route before the closed-form initial condition (M9).
Commit f5fbb03 of TuringMachineSearch is the last before M9, and its two key files are:
- `Proofs/Smith/Conjecture0.lean`: `conjecture0_finite`, `system4_emulation`, `repS4_terminal`, and `conjecture5_finite_exact`;
- `Proofs/Smith/Universality.lean`: the composition, 119 lines.

In today's tree the existential theorem is a corollary of the closed form, so f5fbb03 is the source to port.

**Hypotheses:**
- `WF tm`, a well-formed binary machine. It also constrains the never-executed row of state 0, because the tag productions
  run on after the halt.
- `ValidCfg c` and `c.state < numStates`.
- The machine actually runs `n` steps: `nSteps tm c n = some c'`.

**Conclusions,** for some start configuration of wolfram23, a width `w`, a base `b`, times `times` and a final time `T`:
- the start is a valid wolfram23 configuration, in state A;
- `decodeTM numStates (2^w) b` of the configuration at `times i` is `some (canon c_i)`, where `canon` drops trailing
  blanks;
- `times` is strictly increasing on `i < n`, and `times i <= T`;
- for every `tau <= T` the run is defined and the tape keeps its size. In the standard semantics, where the tape grows
  only when the head moves past its end, this is the clause "the run never leaves the tape";
- at `T + 1` the configuration is `<A, L, 0, []>`, with `L` as long as the starting tape.

The infinite form (T6, one tape for all `n`) comes after, and reuses the System 4 half.

## Why relations

Each rung is one statement of the same shape. `ForwardSim R` says that when `R s t` holds and `s` takes a step, `t` takes
at least one step to a `t'` with `R s' t'`. Relations are used for two separate reasons (PLAN.md, section 1):
- wolfram23 has no periodic orbits, so no time-independent encoding can follow a cyclic tag system with cycles step for
  step;
- the encoded System 5 run always ends, so budgets live inside `R`.

## The ladder

Line counts are of the Lean files on the route to T8, after dropping the closed form and loop-freeness.

| Rung | Steps of the target per source step | Lean lines |
|---|---|---:|
| Framework: systems, `ForwardSim`, schedules (Simulation.lean) | | 468 |
| 1. Turing machine to 2-tag system (Cocke and Minsky): TagRounds, CockeMinsky | 3 tag rounds per move right, 5 per move left; a round has a variable number of tag steps | 817 |
| 2. 2-tag system to cyclic tag system (Cook): TagToCTS | one full cycle of the 2(1 + 84S) appendants per tag step | about 800 |
| The glue of rungs 1 and 2: TMToCTS (alphabet, `enc` and `dec`, `decodeCTS`, `canon`) | | 702 |
| 3. Cyclic tag system to System 5, the doubling inside the encoder | x + 1 or x + 2, two doubled steps per step | 6,204 |
| 4. System 5 to System 4 | existential, f large enough | 3,111 |
| 5. System 4 to System 3, parity blocks of width 2^w | at least 1 | 2,407 |
| 6. System 3 to wolfram23: Systems123, and the non-loop-freeness half of Wolfram23Bridge | 1 or 3 | about 310 |
| 7. Composition: Conjecture0 and Universality at f5fbb03 | | about 1,000 |
| Shared: wolfram23's valid configurations (Wolfram23Valid), finite sets (XorMerge), tapes and machines (BiTM/Basic, TM/Defs) | | about 900 |

The Lean proof's notes name rung 5 as the deepest and rung 3 as the longest. In rung 5, a scan is a prefix-XOR
transducer, and a one-element set's string is a row of the rule-60 automaton, of period 2^w by the identity
stepR^[2^w] x = shiftR^[2^w] x xor x.

## Fewer definitions, and what each merge costs

- **One notion of a system**: a step function `S -> Option S`, its iteration, `ForwardSim`, composition, and the schedule
  lemma. It replaces six hand-made iterations.
- **One lookahead machine type for Systems 3 to 0**, with wolfram23 as System 0's table. A lookahead step is `none` when
  the head would leave the tape, while T8's confinement and exit clauses are about the standard semantics, which extends
  the tape with a blank. So the port keeps the small bridge to the standard machine: the run and exit lemmas, about 100
  lines, the half of Wolfram23Bridge that loop-freeness doesn't need.
- **The relabelings `phi3` and `phi2`** are proved by cases on the whole zipper, not on the state and the cells to the
  right alone. `phi3` swaps every cell left of the head, so a move left brings a swapped cell to the head. Decoding is
  unaffected: it reads the head and the cells to its right up to the first 0, in state B, where neither map changes
  anything.
- **Finite sets**: the bag, the rules and the System 4 sets are lists of integers in the Lean proof, compared up to
  permutation. Whether the port uses strictly increasing lists of naturals is decided at rung 3, weighing two things:
  - Naturals agree with the integers only under invariants. System 5 subtracts 1 from every element of the bag and then
    erases 0, so the bag needs every element at least 1 before a step. System 4's decrement erases 0 before subtracting,
    so it is safe as written; that order must be kept. Every truncated subtraction needs its inequality as a hypothesis,
    for example `rulePos f t k = 2k + f + 3 - t`, the band `2f - 2j - 2`, and loop counts like `f + t - 3`.
  - Sorted lists make equality of bags structural, but sortedness becomes a new obligation of every encoder and every
    step, which the Lean proof never had.
- **The doubling inside the System 5 encoder.** Its step lemma then covers two doubled steps (`represents_step_double`).
  The decoder still undoes the doubling, inside the bag's decoder.
- **Decoders.** `decodeTM` is a composition of decoders: decodeBlocks, decodeBag, undbl, tagWordDecode, dec and
  decodeWord. Its correctness needs a decoding lemma per rung, which the `ForwardSim` relations don't give: decodeBag
  (System 5), `RepS4_decode` (System 4), `rep3_decode` (System 3), `decodeCTS_word` and `undbl_dbl`.
- **Left out**:
  - the halting and evaluation machinery (about 70% of the Lean `System5.lean` and `System4.lean`);
  - loop-freeness (T5);
  - the closed form (M9);
  - Systems 1 and 2 as machines of their own; their tables stay, as the stages of the relabeling.

## Exits and confinement

T8's last two conclusions need, besides the simulations:
- **System 5's terminal event**: the rules are exhausted with 1 in the bag, and the step is `none` on empty rules
  (`conjecture5_finite_exact`).
- **System 4's exit** to the right in state C (`repS4_terminal`, `repS4_exit`).
- **System 3's exit** (`rep3_exit`): the run goes off the focus, then C1 reads the implicit 0 and moves right as A00,
  which the relabeling turns into wolfram23's B2 -> A0>.
- **Left confinement**: the left end of System 3's tape is `0^m 2 2 1^t` with `h <= m`. A turn at the left end lowers `m`
  by one (`turnRun`), which keeps the run off the cells to the left of the tape. For T6 later, Rep3's left and right
  context are parametric from the start, as the Lean proof had to refactor them in M8.
- **The parameters, existential at f5fbb03**: `f` from the System 5 run's length (`conjecture4_cts_exists_f`), a width
  with `2^w` above every set element and `h + 3 <= 2^w`, and `h` the System 4 exit time.
- **The glue of rungs 1 and 2**: `tm_tag_forwardSim`, `cts_of_tag`, `tagToCTS_appendants_length`, `length_word` (the last
  word is not empty, a hypothesis of `conjecture0_finite`), and `WordOK` and `prod_OK` under `WF`.

## Proving in TypeTheory

- **Tables by computation.** Where the Lean proof splits a rule table with `fin_cases` and `simp`, the port splits the
  zipper with `"Cases"`, and the kernel computes every leaf. The case trees are generated by a script, since they are
  data. The milestone 1 prototype, in job scratch `w23/m1.wls`, proves all three theorems of rung 6's tables, over every
  configuration, each in about 1 s:
  - `phi3` turns a step of System 3 into one of System 2;
  - `phi2` turns a step of System 2 into one of System 1;
  - System 0 makes a step of System 1 in `system0Steps[c]` steps, 3 on B21 and B22 and 1 otherwise.

  It states "System 0 reaches whatever System 1 reaches" as `steps0 == orElse[step1, steps0]`, so that where System 1 is
  stuck, both sides are the same term. Every leaf is then `"Reflexivity"`.
- **Tapes and lists by induction**, with `"Cases"`, `"Induction"` and `"RewriteRepeated"`. Arithmetic goes to
  `"LinearArithmetic"` (the Lean proof's 1,029 `omega`), and algebra to `"Ring"`.
- **A list library** for the environment: appending, lengths, taking and dropping, repetition, rotation, and the
  symmetric difference of the finite sets. Also iteration's law `steps (m + n) = steps m ∘ steps n`, and the rule-60
  identity, by induction on `w`.

## Progress

On main by 2026-11-21:
- the framework (steps, forwardSimulation, the lifting and composition lemmas);
- rung 6 as one theorem, `system0Simulates3`, and the bridge to the standard machine, `wolfram23Simulates3`;
- rung 2 complete, `cookSimulation`: a cyclic tag configuration carries its appendants rotated, so there is no phase
  index, and a block lemma (`cyclicTagBlock`) selects the appendants under the 1s of a block. One tag step is k + k
  cyclic tag steps.
- rung 1 complete, `minskySimulation`: the 2-tag system follows any binary Turing machine, one step of the machine being
  three rounds of the tag system for a move to the right and five for a move to the left (`minskyStep`).

How rung 1 is built:
- **Symbols as a type.** `"MinskySymbol"` has the pad and one constructor for each of the 21 kinds, with the state and
  the bits the kind carries. Its productions are a recursor over it, so each computes with a symbolic state and
  machine, and the tag system takes words over any type of symbols (`tagStep` with an implicit type).
- **Rounds.** `passOutFrom` is what a round appends: the productions of every other symbol, with a flag for whether the
  next symbol is read, a structural recursion that computes. Pairs read from their first or second symbols give
  repeated productions (`passOutAlignedPairs`, `passOutShiftedPairs`). A round over an even word is `tagRoundEven`; over
  an odd word `a :: l`, whose first production is `c :: d`, the last symbol takes `c` as its partner
  (`tagRoundOddHead`). No parity function and no last-symbol split are needed.
- **Numbers as the machine reads them.** The right number is written `2 n + h` and the left `2 i + b`, the low bit last,
  since addition recurses on its second argument: `2 n + 0` and `2 n + 1` compute, and each round's case on a bit
  reduces without parity lemmas.
- **The transition** is read through its fields, `t[["next"]]`, `t[["write"]]`, `t[["direction"]]`, behind a named
  `byDirection`, so the productions of a move follow from the direction's equation alone (`productionERight`, ...).

Rungs 1 and 2 are joined (`machineToCyclicTag`): for a machine whose transitions keep the states below S, Cook's
cyclic tag system follows it.
- **Symbols as numbers.** A symbol is 84 q + 4 kind + 2 h + b + 1, the pad 0. The prelude has no division, so
  `divideBy` is a structural recursion that carries one at a time; dividing 84 q + c is c carries after `(q, 0)`
  (`divideAdd`, `divideMultiple`), which computes for every literal c, and the inverse (`minskyDecodeEncode`) is 42
  generated cases, each by two rewrites and reflexivity.
- **The relabeling.** The tag system on numbers decodes, produces and encodes, so it commutes with the encoding
  (`minskyNumbersCommute`) and follows the tag system on symbols step for step (`relabelingSimulation`).
- **Bounds.** Rung 2 asks that the productions of every number below k stay below k. Division's specification
  (`divideSpecification`) needs both sides of a decision: a case split on the decidability instance gives `Decide` its
  value in each branch.

Next: rungs 3 to 5 (cyclic tag to System 5, System 5 to 4, System 4 to 3), then rung 7 and the tutorial.

## Files

- `TypeTheory/Kernel/Library/Wolfram23/*.wl`, one file per rung after a common `Systems.wl`, together building
  `TypeTheoryEnvironment["Wolfram23"]` on the prelude. It is saved, as the machine environments are.
- `TypeTheory/Tests/Library/Wolfram23.wlt`: each rung's statement, and runs on the traces of Smith's paper (the p.47
  System 3 trace, the 36-line System 5 trace).
- `docs/paclet/en/Tutorials/Wolfram23Universality.md`, a section per rung with three parts:
  - the two systems, with one run of each computed by the kernel;
  - the relation and the theorem;
  - the proof, its key lemmas shown with their proofs.

  It ends with T8 and the decoded run of a small machine.

## Order of work

Each milestone ends with its tests and its tutorial section, checked, and is released.

1. The framework, rung 6 with the bridge to the standard machine, and one tape-heavy lemma as a sample of what replacing
   `simp` costs. Rung 6's tables are computation and would under-measure it; the sample is System 3's walk to the left,
   or a System 4 focus lemma at `L ++ e :: R`.
2. Rung 2, then rung 1, and their glue.
3. Rung 3, and the choice of the finite-set type.
4. Rung 4.
5. Rung 5, with the exit and the left confinement.
6. Rung 7: the composition, the decoders' lemmas, and T8.
7. Later: the infinite form, with an infinite tape and the generalized Rep3.

Gemini, through agy, may draft library lemmas and proof scripts in parallel. The kernel checks whatever it writes, as it
checks everything else.

## Risks

- **Size.** The Lean proof leans on `simp` (1,366 calls) and `omega`. TypeTheory has no `simp`, so tape and list lemmas
  need more explicit steps. Milestone 1's sample measures this.
- **Build time.** An environment of this size loads from a saved file, and its full check belongs in the suite and in
  releases, on the pod.
- **Faithfulness.** The Lean relations fix Smith's tape layouts exactly. Turing reviews each rung's statement before its
  proof starts.
