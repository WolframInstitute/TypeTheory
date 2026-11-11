# Machine reals

The 64-bit reals of the compiler's typed code in the type theory: what the model is, what it assumes, what was
checked against the machine, and the plan for the second slice. The library is
`TypeTheory/Kernel/Library/MachineReals.wl`; the reading of typed code is in
`TypeTheory/Kernel/Elaboration/CompiledDefinitions.wl`.

## The model (0.40.0)

A machine real is a rational that binary64 represents, m 2^e with |m| < 2^53 and -1074 <= e <= 971. `"Real64"` is that
subtype of the rationals, so a machine real has an exact value, `x["rational"]`, and its order and equality are those
of its value. NaN and the infinities are no values: a typed entry leaves before it holds one, and the model's
operations give `A | Failure` with the leave as the failure. The sign of zero is not kept.

`TypeTheoryEnvironment["MachineReals"]` is the rationals with the declarations of `"Machine"` and the reals:
`"Machine"` stays on the integers, and `TypeTheoryFormalize[f, "Machine"]` takes the reals' environment where the
typed code of `f` has a real.

Each operation is the rounding of an exact rational result:

| Operation | Value | Leaves |
|---|---|---|
| `"real64Plus"`, `"real64Subtract"` | the result of the exact sum or difference | `"NotFinite"` past the largest real |
| `"real64Times"` | the result of the exact product | `"NotFinite"`; `"Underflow"` where the product is not 0 and its result is below 2^-1022 |
| `"real64Reciprocal"` | the result of 1/y; x / y is x times it, two roundings | those of a product; `"NotFinite"` by 0 |
| `"real64OfInteger"` | the result of an integer, taken before an operation with a real | none in the range of 64 bits |
| `"real64Floor"`, `"real64Ceiling"`, `"real64Round"`, `"real64IntegerPart"` | the machine integer of the whole number, `Round` half to even | `"IntegerOverflow"` from 9*10^18 on |
| `"real64Sqrt"` | the correctly rounded square root | `"Domain"` below 0 |
| an order of an integer and a real | the order of the two values | `"Range"` for an integer past 2^53 |
| `"real64EqualQ"` | the same, or apart by no more than 2^-46 of the larger | none |

## What is assumed

Three constants are axioms with an `"Implementation"`, which the Wolfram Language computes and the kernel never does:
`"real64Result"`, the rounding to the nearest real with ties to even; `"rationalFloor"`; and `"real64SqrtResult"`.
Everything else is a definition over a Boolean order of the rationals. A theorem about real code names the axioms
it uses in its closure: `"real64Plus"[x, y] == "real64Result"[x + y]` has
`<|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature"|>`.

`NormalForm[term, "Implementations" -> True]` is a calculator. It replaces an implemented axiom applied to values by
the value the Wolfram Language computes, and what it gives is no proof: the kernel does not find the two sides equal
by computation, and refuses reflexivity as the proof of their equation (the test
"A-value-an-implementation-computed-is-no-proof").

## What was checked against the machine

`scripts/machine_real_checks.wl` runs 47 rows of real arithmetic as compiled code against the evaluator and compares
the results as text. On arm64 (macOS) and on x86-64 (Linux, a release build of the WolframKernel project with its
JIT on) the 47 rows give the same text. The rows cover each operation, each leave and the mixed integer and real
cases. They test that the model reads the code as the machine runs it; they are no proof of the arithmetic, which
rests on the three axioms.

## The second slice: what is proposed, before any code

### Theorems with content

`"real64Plus"[x, y] == "real64Plus"[y, x]` and the same for `"real64Times"`, each by the commutativity of the
rationals under the rounding. They use the rounding only as a function, so their closure is that of the theorem
above, and they are the first statements about real code that are not true by unfolding.

### The properties of the rounding

Three properties are wanted, each a statement over the rationals:

- **Identity on the representable.** If q is representable, the rounding of q is q.
- **Monotone.** If q <= q' and both roundings are values, the rounding of q is at most that of q'.
- **The half-ulp bound.** The rounding of q is within half a unit in the last place of q: |r - q| <= 2^(e - 1) for
  the exponent e of r, and at most 2^-1075 in the subnormal range.

The proposal is one further axiom, not three: the specification of the rounding, that `"real64Result"[q]` is a
representable r with no representable strictly nearer to q, and with an even m where two are equally near, or the
leave where the nearest is past the largest. The three properties are then theorems, by arithmetic of the
rationals and the uniqueness of such an r. The same specification gives certified values: the nearness of a given r
to a given q is a Boolean check on two literals that the kernel computes, and a lemma turns that check into
`"real64Result"[q] == r`. A value the Wolfram Language computed then enters a proof once the kernel has checked its
certificate, where today it cannot enter one at all.

The alternative, defining the rounding by its algorithm and proving the specification, removes the axiom and is the
later stage: it needs the floor defined from the integers' quotient, which needs laws of `Quotient` the integers'
library does not have yet, and a search for the exponent. The specification axiom states exactly what that stage
would prove, so the theorems above it do not change when the axiom becomes a theorem.

`"rationalFloor"` and `"real64SqrtResult"` stay axioms in this slice. The square root gets the same kind of
specification when a theorem needs it: r >= 0 representable with no representable nearer to the root, stated by
squares.

### Power and the functions of the mathematical library

The model fixes a value only where every conforming machine computes the same value:

| Functions | What the model states | On what evidence |
|---|---|---|
| sum, difference, product, reciprocal, square root, the conversions and the whole-number functions | the value | IEEE 754 requires correct rounding; the 47 rows on two platforms |
| `Power` with an integer exponent | the value, if typed code multiplies; otherwise as the next row | to be read from the typed code of `x^n`, and run on both platforms |
| `Exp`, `Log`, `Sin`, `Cos`, `Tan`, `ArcTan`, `Power` with a real exponent, and the rest of the library | no value: a constant per function with its domain and its leaves, and nothing about its last bit | these are not correctly rounded, and two libraries may differ in the last place; one witness per function, a point where arm64 and x86-64 differ, is to be found by a grid run on both |

A function of the last row is an axiom whose `"Implementation"` is this machine's library. `NormalForm` with
implementations computes with it and the result holds for this machine; a theorem that mentions the function says
so in its closure, by the function's name, and can use nothing about it but that it is a function. A bound in units
of the last place against the exact function is not stated: the library has no real analysis to state the exact
function in.
