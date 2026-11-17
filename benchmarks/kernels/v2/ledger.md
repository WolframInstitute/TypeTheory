# TypeTheory on v2: the ledger

The runs of TypeTheory's test suite on the v2 kernel and the causes of their failures, each with the kernel area it
went to and its state. [README.md](README.md) gives the method.

## Runs

| Run | TypeTheory | v2 kernel | Files: pass, fail, time out, past memory, of all | Tests failing on v2 that pass on Wolfram 15 | Tests never run (file killed) |
| --- | --- | --- | --- | --- | --- |
| 1 (2026-11-17) | 32ae661 | main bb251a622, built in the lane, no Wolfram 15 fallback | 33, 4, 4, 0 of 41 | 13 | 69 |

The Wolfram 15 column, licensed Wolfram 15.0.1 on Linux, passes 671 of 673 tests. Its two failures were TypeTheory's
own: `Library/Machine.wlt` and `Library/MachineReals.wlt` count the environments' constants, and the matrices added
49 to each without the counts following (127 and 281 now).

On v2, 589 of the 604 tests in the 37 files with a result pass: the 13 below fail on v2 alone, and the 2 counts on
both kernels.

The two columns differ in one input: v2's package has its own KernelCompiler, built from the kernel repository's main
(it reports 0.1.6), and TypeTheory takes the highest version, so v2 ran typed code through main's compiler and
Wolfram 15 through 0.1.1. No v2 failure was traced to the compiler.

## Hangs and slow files

The 4 files that ran past 600 s on v2, four files at a time. Each was rerun alone with a line as each test ends, and
traced to its test and the call that takes the time.

| Cause | Area | Files (tests never run) | State |
| --- | --- | --- | --- |
| `CodeParse` of a 217 KB file takes 349 s, against 2.4 s on Wolfram 15 (about 146 times slower); `Terms/Scoping.wlt` parses every kernel file before its first test | KernelPaclet | Scoping (3) | known: PureMath's ledger sent it as a speed item; TypeTheory's case sent |
| TypeTheory's own work, normal forms and environments, about 1.7 to 5 times slower: a real vector's normal form 36 s against 21 s, an environment of three definitions 3.9 s against 0.8 s | WolframKernel | CompiledDefinitions (29) | sent, a speed item with TypeTheory as its repro |
| Slow but done when run alone: 423 s and 471 s | WolframKernel | CompiledKernel (32), NormalForms (5) | rerun alone: 31 of 32 and 4 of 5, the failures below; with the speed item |

## Failures by cause

The 13 tests that fail on v2 and pass on Wolfram 15, and the failures of the timed-out files when rerun alone. Each
cause was found by a probe on both kernels and reduced to a repro free of TypeTheory. A repro's results are the pod
builds': v2 main bb251a622 and Wolfram 15.0.1, on Linux.

"Alone" counts the tests in which the item is the only cause found, so fixing it alone recovers them; "total" adds
the tests that also need another item. Ranking is by alone, then total.

| # | Item | Owner | Alone | Total | State |
| --- | --- | --- | --- | --- | --- |
| 1 | Operators print as calls: `Subtract`, `Divide`, `Cross`, `CenterDot`, `CircleTimes`, `NotExists` | FrontEnd | 5 | 7 | sent |
| 2 | `FindEquationalProof` is not implemented | Math | 2 | 2 | sent |
| 3 | TraditionalForm rewrites a sum inside a held argument before a `MakeBoxes` rule sees it | FrontEnd | 1 | 4 | sent |
| 4 | A sum inside a sum loses its parentheses | FrontEnd | 1 | 3 | sent |
| 5 | TraditionalForm's `Mod` leaves its argument's sum without parentheses | FrontEnd | 0 | 1 | sent |

### 1. Operators print as calls (FrontEnd)

```wl
ToBoxes[HoldForm[Subtract[k, 1]]]
(* Wolfram 15: TagBox[RowBox[{"k", "-", "1"}], HoldForm]
   v2:         TagBox[RowBox[{"Subtract", "[", RowBox[{"k", ",", "1"}], "]"}], HoldForm] *)
ToBoxes[Cross[a, b]]                    (* Wolfram 15: RowBox[{"a", "\[Cross]", "b"}];  v2: Cross[a, b] *)
ToBoxes[CenterDot[2, a]]                (* Wolfram 15: RowBox[{"2", "\[CenterDot]", "a"}] *)
ToBoxes[CircleTimes[a, b]]              (* Wolfram 15: RowBox[{"a", "\[CircleTimes]", "b"}] *)
ToBoxes[HoldForm[NotExists[x, p]]]      (* Wolfram 15: RowBox[{SubscriptBox["\[NotExists]", "x"], "p"}] *)
ToBoxes[HoldForm[Divide[a, b]]]         (* Wolfram 15: FractionBox["a", "b"] *)
```

v2 gives the call form, `Head[args]`, for each. TypeTheory shows a product of types through `Cross`, a dependent sum
through `NotExists`, and a difference through `Subtract`, so on v2 they read `Cross[ℕ, 𝔹]` and `NotExists[n : ℕ, ...]`.
Alone: A-dependent-sum-shows-as-sigma-over-its-binder, A-notation-of-the-user-shows-a-constant-and-a-projection-of-a-variable-has-no-parentheses,
Operators-numbers-and-symbols-show-their-types-on-mouseover, The-types-on-mouseover-change-nothing-a-term-shows,
A-term-read-back-from-a-core-term-shows-its-types-without-elaborating-it-again (the last two by their boxes; to
confirm on the rerun). With 3 or 4: Products-and-sums-of-types-show-as-times-and-alternatives,
TraditionalForm-shows-a-notation-given-for-it.

### 2. `FindEquationalProof` is not implemented (Math)

```wl
FindEquationalProof[op[c, e] == c, {ForAll[{x, y, z}, op[op[x, y], z] == op[x, op[y, z]]], ForAll[x, op[e, x] == x], ForAll[x, op[inv[x], x] == e]}]
(* Wolfram 15: ProofObject[...] in 0.4 s, its "ProofDataset" a Dataset of 10 steps
   v2:         returned unevaluated *)
```

TypeTheory's tactic `"Equational"` replays the proof `FindEquationalProof` finds, by its `"ProofDataset"`. Alone:
FindEquationalProof-proves-group-laws-from-the-axioms, FindEquationalProof-works-in-any-type.

### 3. TraditionalForm rewrites a held argument before a rule sees it (FrontEnd)

```wl
SetAttributes[seen, HoldAllComplete];
seen /: MakeBoxes[seen[x_], form_] := ToBoxes[ToString[Unevaluated[FullForm[x]], InputForm], form];
ToBoxes[seen[a + 1], TraditionalForm]
(* Wolfram 15: the string "FullForm[a + 1]"
   v2:         the string "FullForm[SystemLibrary`PackageScope`traditionalSum[a, 1]]" *)
```

v2's TraditionalForm replaces `Plus` by an internal `SystemLibrary`PackageScope`traditionalSum` throughout the
expression it formats, held arguments included, before a user's `MakeBoxes` rule runs, and the internal head then
shows in the boxes. StandardForm gives the argument as written. TypeTheory's terms hold their expressions, so their
TraditionalForm shows `traditionalSum(a, 1)` and loses its notations and its tables of cases. Alone:
A-notation-that-gives-an-InterpretationBox-holds-boxes-alone. With 1, 4 or 5: TraditionalForm-shows-a-recursor-as-its-cases,
TraditionalForm-shows-a-constant-by-its-traditional-notation, TraditionalForm-shows-a-notation-given-for-it.

### 4. A sum inside a sum loses its parentheses (FrontEnd)

```wl
ToBoxes[HoldForm[(a + b) + c]]
(* Wolfram 15: TagBox[RowBox[{RowBox[{"(", RowBox[{"a", "+", "b"}], ")"}], "+", "c"}], HoldForm]
   v2:         TagBox[RowBox[{RowBox[{"a", "+", "b"}], "+", "c"}], HoldForm] *)
ToBoxes[HoldForm[a + (b + c)]]          (* the same, on the right *)
ToBoxes[HoldForm[(r + 2) + k], TraditionalForm]   (* the same in TraditionalForm *)
```

A product of a sum keeps its parentheses on v2; only a sum in a sum loses them, so `(k + 1) + 1` and `k + (1 + 1)`
both read `k + 1 + 1`. Alone: A-sum-in-a-sum-shows-its-parentheses. With 1 or 3: Products-and-sums-of-types-show-as-times-and-alternatives,
TraditionalForm-shows-a-recursor-as-its-cases.

### 5. TraditionalForm's `Mod` leaves its argument unparenthesized (FrontEnd)

```wl
ToBoxes[HoldForm[Mod[1 + a, 4]], TraditionalForm]
(* Wolfram 15: TemplateBox[{RowBox[{"(", RowBox[{"1", "+", "a"}], ")"}], "4"}, "Mod"]
   v2:         TemplateBox[{RowBox[{"1", "+", "a"}], "4"}, "Mod"] *)
```

The `"Mod"` template shows its first argument before "mod", so a sum there needs its parentheses. With 3:
TraditionalForm-shows-a-constant-by-its-traditional-notation.

## Totals

- 13 v2-only failures, in `Terms/SurfaceSyntax.wlt` (11) and `Proofs/Equational.wlt` (2). 9 are recovered by a single
  fix; the other 4 need two of the items above.
- `Checking/NormalForms.wlt`'s test No-normal-form-the-suite-computes-holds-a-redex runs 19 test files under a check
  of every normal form: on v2 it finds no redex, and fails on SurfaceSyntax's 11 failures counted again. It is not a
  cause of its own.
- 69 tests never ran in run 1, in the 4 files past 600 s: see "Hangs and slow files".

## TypeTheory's own

- `Library/Machine.wlt` and `Library/MachineReals.wlt`: the counts of the environments' constants, behind the
  matrices. Fixed (0aeaf7c), 17/17 on Wolfram 15.
- `Checking/CompiledKernel.wlt`, A-forged-proof-about-a-made-up-large-constant-is-refused-alike-on-both-paths (seen
  when the file runs alone): it compares `ToString[failure["Message"]]` from the two kernels of TypeTheory. Wolfram
  15 writes each parameter of the message as boxes cut by `Short`, so the environments' handles do not show and the
  strings agree; v2 writes the whole term, its environment's handle included, and they differ. The test relies on
  unspecified rendering, and is not routed: TypeTheory's failure messages are to be plain text (its task 92), which
  makes the strings agree on both kernels.
