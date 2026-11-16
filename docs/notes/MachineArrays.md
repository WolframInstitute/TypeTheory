# Vectors of typed code

The packed arrays of rank 1 that the compiler's typed entries take, make and return, in the type theory: the model,
what it leaves out, the theorems it rests on, and what is not done yet. The library is
`TypeTheory/Kernel/Library/MachineArrays.wl`; the reading of typed code is in
`TypeTheory/Kernel/Elaboration/CompiledDefinitions.wl`. The design was approved on 2026-11-16 and is in 0.51.0.

## The type

`"PackedArray"[A, 1]` is the compiler's `"PackedArray"::[A, 1]`: the lists `{A}` whose length is below 2^63, a subtype
of the prelude's lists. `a["list"]` is the list of an array, as `n["integer"]` is the integer of a machine integer,
and `a["proof"]` the proof that its length is in range. So `Length` of an array is a machine integer made from the
length and the proof, and never leaves, as in typed code. The elements are `"Integer64"` in
`TypeTheoryEnvironment["Machine"]`, and `"Real64"` too in `TypeTheoryEnvironment["MachineReals"]`, which takes the
same declarations.

`"PackedArray"[A, rank]` is defined by recursion on the rank, with A at rank 0. The recursion carries the element type,
so that rank 1 computes to `Subtype["arrayLengthRange"[A]]` of A itself. A first form, the arrays of the rank below at
each rank, left the lists at rank 1 as lists of a recursion yet to compute at rank 0. They were the same type by
computation, but not the same term: a hypothesis on `a["list"]` did not rewrite a goal written with `{A}`.

The other choice was plain lists, with `Length` giving `"Integer64" | Failure`. The library would be simpler, but the
model would have a leave that typed code does not, and every theorem about code that calls `Length` would carry the
hypothesis that the length fits.

## The operations

Each is first on lists, a place counted from 0 by an integer and walked down the list, so a place below 0 or past the
end is never met and gives `Failure["PartRange", <||>]`. Then on arrays, a place from 1 or, below 0, from the end, by
the leaves of typed code (WolframKernel main 322291757, read from the C backend and the runtime, then run against the
evaluator):

| Typed code | Model | Leaves |
|---|---|---|
| `Length[a]` | `"arrayLength"[a]`, an `"Integer64"` | none |
| `a[[i]]` | `"arrayPart"[a, i]` | `"PartRange"` outside 1 <= i <= n and -n <= i <= -1 |
| `a[[i]] = v` | `"arraySetPart"[a, i, v]`, the local set to it | `"PartRange"`, by the same rule |
| `Take[a, n]` | `"arrayTake"[a, n]`: the first n, or below 0 the last -n | `"PartRange"` past the length |
| `ConstantArray[c, n]` | `"arrayConstant"[c, n]` | `"Range"` for n < 0 |
| `Total[a]` of machine integers | `"arrayTotal"[a]`: `"machinePlus"` from 0, left to right | `"IntegerOverflow"` at the first partial sum out of range |

Typed code has no `Total` of reals: the compiler gives a function that calls it no typed entry.

## What the model leaves out

An allocation that fails leaves typed code with `Failure["Memory", <||>]`. Whether it does depends on the machine
and not on the values, as the checks of the recursion level do, which the model already leaves out: the meaning of
typed code is its value where it does not leave for want of memory. `"arrayOfList"` makes an array of a list and has a
branch for a list too long to hold, whose value is that leave, since the type needs the proof of the range. The library
proves that no operation reaches it: setting a part keeps the length (`"arraySetPartLength"`), Take gives the length
asked for and never more than the array has (`"arrayTakeLength"`, `"arrayTakeLengthBound"`), each leaves by a part that
is not there alone (`"arraySetPartLeave"`, `"arrayTakeLeave"`), and a constant array of a length a machine integer
counts is there (`"arrayConstantOfNatural"`).

`Native`UncheckedBlock` and `Native`UncheckedArray`, which skip the checks, are not modeled, nor matrices, arrays of
expressions or strings.

## The translation

The compiler's kinds are `"Array:Int64"` and `"Array:Real64"`, beside `"Integer64"`, `"Real64"` and `"Boolean"`. `Length`
is a step that never leaves; `Part`, `Take`, `Total` and `ConstantArray` are steps that may. The compiler's `SetPart`
of a local array is read as two statements the model has already: the step `"arraySetPart"`, and the local set to its
value. So an array that a loop or an If sets is one of the locals it sets, its state, by the rule for locals, and no
rule of its own was needed.

An argument `x_List` says no type, so a function of a vector takes its types with it,
`TypeTheoryFormalize[Typed[f, {types} -> result], "Machine"]`, the Wolfram Language's form for a function with its
types, as `FunctionCompile` takes it. The types are passed to the compiler's `TypedSignatures` as strings, a vector's
in InputForm, and the result given is checked against the compiler's. `Typed[f, type]` is the option `"Type"` in every
meaning.

## The theorems

The gate of the slice, in `Tests/Elaboration/CompiledDefinitions.wlt`, each with `quotientSoundness` alone in its
closure:

- `vectorSum`, a `While` over `Part`, computes `"arrayTotal"`, with its leaves, for all fuel above the length, wherever
  the length and one more are machine integers: the counter that passes the last part is one more than the length.
  The design stated the theorem without that hypothesis; the model needs it, since `i + 1` leaves at a length of
  2^63 - 1. Where every partial sum is a machine integer, `"partialSumsInRange"`, the value is the sum of the
  integers of the list, `"integerListSum"`.
- `vectorSquares`, a `ConstantArray` whose parts a `While` sets, gives the squares of 1 to n wherever n n is a machine
  integer, for all fuel above n.

The proofs follow the triangular loop's: one round of the loop and the round that stops, each by unfolding the loop
once; an invariant by induction on the elements left, with the array split at the place the loop is at, `pre` and the
rest (`"arrayPartOfJoin"`, `"arraySetPartOfJoin"`); and a continuation bound twice as once, `"confirmBindThen"`, which
takes a round to the hypothesis of the induction.

One proof step in the library was first a `"LinearArithmetic"` with the bound 2^63 among its literals, and the kernel
could not finish checking it within its recursion limit. A term from the prelude's order, `"lessEqualSuccessor"` and
`"lessEqualTransitivity"`, states the same without the literal arithmetic.
