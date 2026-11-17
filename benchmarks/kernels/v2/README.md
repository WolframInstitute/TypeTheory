# TypeTheory on the v2 Wolfram kernel

TypeTheory's test suite runs on the v2 kernel (WolframKernel) file by file, against Wolfram 15.0. The run finds the
v2 gaps that TypeTheory hits, so their count can be watched as it falls from one v2 release to the next.
[ledger.md](ledger.md) holds the runs and the causes, each with the kernel area it went to and where it stands. The
method is PureMath's (PureMath's `benchmarks/kernels/v2`).

## A run

```sh
sh benchmarks/kernels/v2/lane.sh [<kernel commit>]
```

It sends this checkout's HEAD to a lanes pod and to the Wolfram 15 pod. The tree also carries what a release paclet
adds:

- the environments saved at HEAD (`wolframscript -f scripts/save_environments.wls` first);
- the Linux library;
- KernelCompiler 0.1.1.

Then it runs both columns.

1. **The v2 column.** The kernel commit (main by default) is built in a lane, pod dir `TypeTheory-v2`. Each test file
   then runs in a kernel of its own, 600 s and 6 GB per kernel, four at a time, under the kernel tree's
   `memcap.py` (`scripts/run_tests_by_file.sh`). `.test-runs/` holds a log for each file. A `TIMEOUT` or `MEMORY` line
   names a file that was stopped.
2. **The Wolfram 15 column.** The whole suite in one licensed Wolfram 15.0 kernel on the w15 pod.

Both run `with_kernelcompiler.wls`, which loads the same KernelCompiler before `scripts/run_tests.wls`.

3. **The analysis.** `python3 benchmarks/kernels/v2/analyze.py <test-runs> <w15 log>` groups the v2 failures of tests
   that pass on Wolfram 15 by a first cause and writes them as JSON beside the log. A test that fails on both kernels
   is TypeTheory's own and is fixed here.

## From causes to the ledger

The first cut is mechanical: one bug can show under several causes, and a wrong result says nothing about its cause.
A cause becomes a ledger row once it has a repro: the smallest input, free of TypeTheory where it can be, with the
result on both kernels. Causes that are one bug merge, and the wrong results are read test by test. A hang, a file
past its time on v2 whose tests take seconds on Wolfram 15, is traced to its test and to the primitive that does not
return.

Rows go to the kernel area that owns the function, in the order of the tests a fix recovers, hangs first:

| Area | Functions |
| --- | --- |
| Math | calculus, ODEs, series, limits, `Solve`, `Integrate`, `Minimize`, `FindInstance`, polynomial algebra |
| Simplify | `Simplify`, `FullSimplify` and `Expand` result forms |
| FrontEnd | formatting, boxes, `ToString`, typesetting |
| Tensors | arrays, linear algebra, graphs |
| WolframDev | patterns and definition order |
| WolframKernel | evaluation, messages, attributes, scoping |
| KernelPaclet | `Import`, `Export`, packages, paclets, LibraryLink |

## Reruns

Each v2 release gets a run made the same way. The ledger adds the run's counts beside the earlier ones. A row whose
tests pass moves to fixed, with the release that fixed it.
