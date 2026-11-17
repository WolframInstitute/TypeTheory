# Matrices of typed code

The packed arrays of rank 2 that typed code makes inside a function, in the type theory: the model, what typed code has
and has not, the theorems, and what is not done yet. The library is `TypeTheory/Kernel/Library/MachineArrays.wl`, with
the vectors ([MachineArrays.md](MachineArrays.md)). The design was approved by Stephen on 2026-11-17.

## What typed code has

Read from KernelCompiler's source (0.1.6 and later, `Compiler/Types.wl`, `Compiler/CBackend.wl`) and probed through
`TypedSignatures` with that source loaded:

- A matrix is `"Matrix:Int64"` or `"Matrix:Real64"`, FunctionCompile's `"PackedArray"::[t, 2]`. The runtime holds it
  as `{data, rows, columns}` (`wl_integer_matrix_t` in `runtime/rt-abi/include/wl_abi.h`): a flat array of rows times
  columns elements, and the two counts.
- It exists only inside typed code: no typed entry takes or returns one.
- It is made by `Partition[a, k]` of a vector: k columns, `Floor[Length[a]/k]` rows, a shorter tail dropped.
  `Failure["Range", <||>]` for k below 1, and `Memory` where the allocation fails.
- Three operations: `Length[m]`, the rows, which never leaves; `m[[i]]`, a row as a vector; `m[[i, j]]`, an element.
  Each index is counted as `Part` counts. One that is not there leaves with `Failure["PartRange", <||>]`.
- Nothing else: no `Dimensions`, `Transpose` or `Dot` of matrices, no `m[[i, j]] = v`, and no ranks above 2.

## The type

`"PackedArray"[A, 2]` computes to `"Matrix"[A]`, a structure with one constructor,
`"matrix"[columns, rows, proof]`:

- `m["columns"]` is the column count;
- `m["rows"]` is the list of the rows, lists of A;
- `m["proof"]` is `"matrixRange"[columns, rows]`, which says four things: the columns, the rows and their product are
  below 2^63, and every row is as long as the columns (`"rowsOfLength"`).

The columns are kept because typed code keeps them. A matrix with no rows still has columns: `Partition[{1, 2}, 3]`
has 0 rows and 3 columns. Transpose twice is then the identity on every matrix. With a list of lists, the transpose of
the transpose of a 0 by 3 matrix would be 0 by 0. The model maps one to one onto the runtime's layout: the rows joined
are `data`, their number is `rows`, and `columns` is `columns`.

The bound on the product is the allocation typed code makes. The bounds on the columns and the rows make `Length` a
machine integer, and a row a vector, without a leave. A row as a list rather than as a vector keeps the structure free
of the vectors' own proofs; `"matrixRow"` makes the vector, and `"matrixRowLeave"` shows it is never the leave of an
allocation that fails.

`"PackedArray"[A, rank]` keeps its recursion on the rank. Rank 1 is still `Subtype["arrayLengthRange"[A]]` of A itself,
so the vectors' theorems do not change. Rank 2 is the matrices. A rank above is the lists a machine holds of the arrays
of the rank below, not the empty type: a theorem about a function on an empty type would hold vacuously and read as a
guarantee (Stephen, 2026-11-17). `TypeTheoryFormalize` refuses a type of a rank above 2, naming it.

## The operations

| Typed code | Model | Leaves |
|---|---|---|
| `Partition[a, k]` | `"matrixOfPartition"[a, k]` | `"Range"` for k below 1 |
| `Length[m]` | `"matrixLength"[m]`, an `"Integer64"` | none |
| `m[[i]]` | `"matrixRow"[m, i]`, a vector | `"PartRange"` |
| `m[[i, j]]` | `"matrixPart"[m, i, j]` | `"PartRange"` for either index |

The mathematics, which typed code does not have, stated on the model's matrices:

- `"matrixDimensions"[m]` is the pair of the counts of the rows and the columns.
- `"matrixTranspose"[m]` is the matrix whose rows are m's columns, built from the rows by `"transposeRows"`.
- `"matrixVectorProduct"[m, v]` is the list of the exact sums of the integers' products, row by row, for matrices
  and vectors of machine integers (`"integerListDot"`).

`Partition` is `"partitionRows"`, a recursion on fuel: the first n elements, then the rows of the rest, while n are
left. A row takes at least one element where n is above 0, so as many rounds as the list is long are enough. A count
no machine holds, which typed code's machine integers never give, leaves as an allocation that fails
(`"partitionMatrix"`). `Memory` stays out of the meaning, as for vectors.

## The theorems

- `"matrixTransposeTwice"`: `"matrixTranspose"["matrixTranspose"[m]] == m` for every matrix, with no axiom.
- `"matrixDimensionsOfTranspose"`: the dimensions of a transpose are the pair swapped, with no axiom.
- `"matrixOfPartitionOfNatural"`: Partition by a count a machine integer holds, 1 or more, is the matrix of the rows
  `"listPartition"` gives.
- `"matrixOfPartitionRange"`: by a count below 1 it leaves with `"Range"`.
- `"matrixRowLeave"`, `"matrixPartLeave"`: a row and an element leave by a part that is not there alone.

The proof of the first rests on one lemma, `"transposeOfPrependColumns"`. A row put before columns as long as it is
transposes to the row before the transpose of the columns. It needs no rectangularity, only that lengths match, and
each of its steps is computation. With it and the column count, `"transposeRowsTwice"` goes by induction on the rows.
Two matrices with the same columns and rows are one, `"matrixEquality"`, since any two proofs of the range are one.

## Not done yet

- The translation: the kinds `"Matrix:Int64"` and `"Matrix:Real64"`, and steps for `Partition`, `Length` of a matrix
  and `Part` at one and two levels. A matrix is a local only, so the input form and the typed entries do not change.
  It needs KernelCompiler with matrices installed (0.1.7, from the WolframKernel project's main), which TypeTheory
  loads; the installed 0.1.1 has none.
- The theorem that a matrix-vector product by loops, `Partition` and then `m[[i, j]] v[[j]]`, computes
  `"matrixVectorProduct"` where no step leaves.
- The reals' matrices, `"Matrix:Real64"`, with the translation.
