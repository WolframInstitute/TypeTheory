# The kernel's code on Wolfram 15's evaluator

Core terms share their subterms: a reduct reuses the terms it was made from, so a term is a graph
whose distinct subterms can be far fewer than the leaves of the tree it writes out to. An integer
is a pair of naturals, and adding two reads the previous pair twice, `Pair[p.1 + q.1, p.2 + q.2]`:
a sum of k integers writes out to a tree that doubles with each term, while its distinct subterms
grow linearly. Wolfram 15's evaluator walks a term as that tree in two places. The kernel's code is
written so that neither happens. Times are Wolfram 15.1 on an Apple M3 Max.

## 1. Evaluating a term after an assignment

Wolfram 15 marks an expression it has evaluated and skips it the next time, but an assignment
between two evaluations, such as a cache's `store[key] = value`, takes the marks away. The next
evaluation of a term then walks it per occurrence. Passing a shared term of 2^20 leaves to a
function, with one assignment before each call:

| The term's heads | One call |
|---|---:|
| no attributes | 868 µs |
| `HoldAll` | 1,041 µs |
| `HoldAllComplete` | 0.8 µs |
| any, with no assignment between the calls | 0.3 µs |

So the composite heads, `application`, `lambdaAbstraction`, `dependentFunctionType`,
`localDefinition`, `projection` and `cubicalSystem`, are `HoldAllComplete`, and evaluating a term
stops at its head (`Kernel.md`, "Representation"). The leaves, `boundVariable`, `freeVariable`,
`universeSort` and the rest, evaluate as usual.

A held head keeps whatever it is given, so each construction computes its parts first: with
`Construct`, with `With`, or, in a replacement rule that computes a part, as the rule matches,
`With[{value = …}, value /; True]`. `withTermConstructionCheck` puts a rule on each composite head
that catches a construction leaving a part uncomputed, repairs it and records where it came from;
`Tests/Terms/TermConstruction.wlt` runs the forged tests, the random substitutions and a slice of
the suite under it.

## 2. Substitution walks the values in its target

`With`, `Module`, a `:>` rule and a named `Function` substitute their variables by walking their
body, and the body holds whatever an enclosing definition put there: a term reached from the
definition's arguments is walked as its tree. Wolfram 15 skips the walk when its summary of the
term's symbols rules the variable out, which a term naming many user symbols defeats, so whether a
site pays depends on the names in the terms. A definition's own substitution of its pattern
variables walks only its stored right side.

A nested construction over a shared term of depth 10 and then 13, one user symbol at each leaf:

| Construction | Depth 10 | Depth 13 |
|---|---:|---:|
| `With` or `Module` at the top of a definition, and anything under them, the multi-list `With[{a = …}, {b = …}, body]` included | ~60 µs | ~500 µs |
| a rule inside a rule | 93 µs | 720 µs |
| `Block`, `Block` over `With` or over a rule, a single rule, a rule over `With`, a named or slot `Function` over `With`, plain calls, `If` | ~1 µs | ~1 µs |

So the steps of reduction, inference and definitional equality dispatch on the patterns of their
definitions and keep sequential locals in `Block`, never in a `With`, `Module`, `:>` or named
`Function` over a term:
- **Each `Block` local belongs to one function.** A `Block` is dynamic, so a local that named a
  function would hide it from everything called inside, as a local `propositionQ` would have hidden
  `propositionQ`. `Tests/Terms/Scoping.wlt` checks that each local belongs to one function and names
  no definition.
- **Constructions under a `Block` compute their parts,** as in §1: a held head would keep the
  local's symbol, not its value.
- **The recursion limit.** The kernel recurses as deep as terms nest, so `catchKernelFailure` raises
  `$RecursionLimit` to at least 20,000.

## 3. What it gives

`Decide` on a sum of k integer literals:

| k | Both walks | §1 only | Neither |
|---:|---:|---:|---:|
| 8 | 0.08 s | | 0.026 s |
| 12 | 1.02 s | 1.09 s | |
| 16 | 15.6 s | 16.4 s | 0.047 s |
| 20 | | 261 s | 0.062 s |
| 32 | | | 0.103 s |
| 64 | | | 0.246 s |
| 128 | | | 0.674 s |
| 256 | | | 2.08 s |

The Euler characteristics of the sphere and the torus take 0.041 s and 0.108 s, against 0.06 s and
0.23 s, and Jacobi's two squares at n = 12 takes 9.7 s, against 13.8 s.

Checking the Mathlib cones of `DefinitionalEquality.md` §7.3, median of two warm runs; translating
is unchanged at 1.2, 1.5 and 3.3 s:

| Cone | Both walks | §1 only | and `reduceHead` | Neither |
|---|---:|---:|---:|---:|
| `binaryRec` | 7.58 s | 7.35 s | 6.08 s | 5.41 s (−29%) |
| `omega` | 10.75 s | 10.28 s | 8.09 s | 7.23 s (−33%) |
| `balanceL` | 21.14 s | 20.76 s | 18.10 s | 15.87 s (−25%) |

§1 alone moves little: its walks come after assignments, and §2's come at every step. Both together
remove the doubling, and what remains of the cones is the evaluator's cost for each call
(`DefinitionalEquality.md` §7.5).

## 4. Caches where the walks were

With the walks gone, work that a cache saves shows. `Decide` reduces its decision under the kernel's
caches: the instance search and the check stay outside, so no cache outlives a metavariable's
assignment. A check remembers the universe instantiations it makes (`$universeInstantiationCache`,
keyed by the term, its parameters and the levels, the terms being the records' own objects, so a
lookup costs a pointer's comparison). With both:
- `Decide` on a sum of k integers takes 0.033 s at k = 16, 0.115 s at 64 and 0.461 s at 256, at
  the default recursion limit;
- the Euler characteristics take 0.020 s and 0.043 s;
- Jacobi's two squares, `r2[n] == 4 DivisorSum[n, χ4]`, takes 0.344 s at n = 12 and 0.879 s at
  n = 20; without the universe cache, 0.38 s and 0.97 s;
- the cones check in 4.92 s, 6.54 s and 14.20 s, 35%, 39% and 33% under the first column above.

A map of the universe instantiation over the distinct subterms alone, in place of the cache,
measured from neutral to 2% faster on the cones, whose types are small.
