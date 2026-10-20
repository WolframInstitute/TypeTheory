# Kernel conformance

TypeTheory is pure Wolfram Language, so any kernel that evaluates the language as Wolfram 15 does can
run it. This directory holds what such a kernel must get right: the calls of `System` functions that
TypeTheory makes, each with Wolfram 15's result.

| File | What it holds |
|---|---|
| `Corpus.wlt` | One `VerificationTest` per case, for `TestReport` |
| `Corpus.wl` | The same cases as `{id, HoldComplete[call], HoldComplete[result]}` |
| `Calls.tsv` | Every `System` function TypeTheory calls, with how often, while it builds the prelude and runs its tests |
| `run.wl` | Runs `Corpus.wl` on a kernel and prints each case whose result differs; plain WL, for kernels without MUnit |

`scripts/kernel_conformance.wls` writes the corpus. It traces TypeTheory on Wolfram 15 and keeps, for each
function, the smallest call of each shape of arguments that can be replayed on its own. A fresh kernel
then replays each kept call, and the corpus keeps those that give the same result there.

```sh
wolframscript -f scripts/kernel_conformance.wls    # rewrite the corpus, about 20 minutes
wolfram-kernel KernelConformance/run.wl            # check a kernel against it
```
