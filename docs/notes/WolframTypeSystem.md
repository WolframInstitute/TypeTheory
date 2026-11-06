# The Wolfram Language's types in TypeTheory: plan

Status: proposal, 2026-11-06. Coordinated with Stephen (kernel v2); WolframDev owns v2's compiler side.

## The idea: a type is written as the pattern of its values

TypeTheory's Wolfram Language environment already names its types by the Wolfram Language's own heads, one head for
a type and its values, by position. Its newest types follow the patterns that match their values:

| Values | Pattern | Type | Status |
|---|---|---|---|
| a list of `A` | `{__A}` | `{A}` | prelude |
| a sequence of any length of `A` | `x___A` | `A...` | 0.27, `Unevaluated[a, b]` shows `[a, b]` |
| a sequence of an `A` and a `B` | `PatternSequence[_A, _B]` | `Sequence[A, B]` | 0.26 (HList) |
| an `A` or a `B` | `_A \| _B` | `A \| B` | proposed: `DisjointUnionType` written as `Alternatives` |
| a value or a failure | `_A \| _Failure` | `A \| Failure` | proposed: errors |
| a value or a missing one | `_A \| _Missing` | `A \| Missing` | proposed: `Option`, `Missing[]` for `"none"` |
| an expression | `_` | `Expressions` | 0.26 |

Writing types this way keeps one notation for the patterns a definition is written with and the types
`TypeTheoryFormalize` gives it: a definition `f[x_Integer] := ...` and its type `Integers -> ...` read the same.

## Errors: `A | Failure`

- `Failure` an inductive type of the environment: a tag, a string, and a message, an association of strings to
  expressions; `Failure[tag, <|...|>]` a value of it, as written.
- `A | Failure` the type of a value or a failure (Lean's `Except`), with `Confirm : A | Failure -> A` read as bind
  inside `Enclose : (A | Failure) -> A | Failure`, as Wolfram Language code writes them; `ConfirmBy`, `ConfirmMatch`
  as bind after a test.
- v2's Core reads every call as `Either` (spec section 4.1, the table of exits, kernel 3066b82d): a call gives a value,
  `Right v`, or an exit, `Left e`; the check after each call is the bind, and the regions `Core`Catch` (which `Catch`
  and `Enclose` lower to), `Core`Cleanup` and `Core`Quiet` are the handlers. The exits TypeTheory reads:
  - a confirmation's failure, raised by `Confirm`, `ConfirmBy`, `ConfirmMatch`, `ConfirmQuiet`, `ConfirmAssert`,
    tagged `{Kernel`Private`encloseTag, tag}` and taken by the `Enclose` of that tag: `A | Failure`, `Enclose` its
    catch, with a handler `handler[failure]`;
  - a throw, a value and a tag, taken by the `Catch` whose form matches the tag: `A | Thrown[E]`, read per tag;
  - a return of a compiled function, taken by the function itself: no type of its own, the function's value.
  Aborts and quits pass every compiled region and stay outside the types. `WithCleanup` runs its cleanup on both
  sides and `Quiet` passes every exit through, so both read as the identity on the monad.

## State: Module, Set, Do, While

- v2's Core is in A-normal form: `Core`StatementBlock[{statements}, atom]` with `SetLocal`, `Copy`, `Core`If` and
  `Core`While`; Do, For and Table lower to While. Read a StatementBlock as a State computation over its locals, and a
  While with a bound as recursion on its fuel, as ReplaceRepeated's MaxIterations already is.
- First target: loops of the shape `Module[{s = 0}, Do[s += f[i], {i, n}]; s]`, read as recursion on `n`, so the
  compiled loop of the Programs and Proofs tutorial gets a theorem of its own.

## IO

- v2 tracks no effects; its pure stamps are a property of values. IO is by name: `Print`, `Echo`, `Import`,
  `RandomInteger`, ... are axioms of type `... -> IO[A]`, with `CompoundExpression` as sequencing. The name of the
  type is to be decided.

## Data structures

- `Association[K, V]`: finite maps, a type and its values `<|k -> v|>` by position, with `Lookup` giving
  `V | Missing`, `KeyExistsQ`, `Keys`, `Values`, `Append`; keys compared by a decidable equality.
- Packed arrays as `Vector[A, n]` with machine element types (v2 has packed machine integer, real and complex
  arrays of any rank natively).
- `DataStructure` kinds after v2's note 69.

## Machine types

- v2's typed entries (spec section 6, Types.wl) give each compiled function a signature: int64, Real64, arrays. A
  shared table maps them to TypeTheory types; `"MachineInteger"` is the integers in `[-2^63, 2^63)`, whose
  arithmetic is exact while it stays in range (W15's compiled code stops with IntegerOverflow and falls back), so
  a theorem says where a compiled program is exact: for the closed form of the triangular numbers, n <= 3037000499.
  That needs a nonlinear arithmetic tactic (products of hypotheses, as Lean's nlinarith).

## Kernel v2 work (WolframDev)

1. A public KernelCompiler entry returning a function's Core and its Types.wl signature in one call.
2. A typed entry for literal base cases plus one typed general definition, the shape `TypeTheoryFormalize` reads as
   recursion on the natural numbers.
3. A spec section on Core's exits (Throw, Confirm/Enclose, Catch).
