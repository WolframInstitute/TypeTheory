# Packed arrays of every rank (design, for review)

The machine library (`Library/MachineArrays.wl`) has `"PackedArray"[A, r]` by recursion on the rank: rank 0 is `A`,
rank 1 a list a machine holds, rank 2 a `"Matrix"[A]` that carries the proof that its rows are as long as its columns,
and a rank above a list a machine holds of the arrays of the rank below. Only ranks 1 and 2 are rectangular: an array of
rank 3 may hold matrices of different shapes, so `Dimensions` is defined at rank 2 alone, and `Transpose` with it. The
Wolfram Language's packed arrays are rectangular at every rank, and `Dimensions` and `Transpose` take every rank. The
user asked for `Dimensions` over every rank (2026-11-19).

## What changes

- **Ranks 0, 1 and 2 stay as they are.** They are rectangular already, with the shapes `{}`, `{length}` and
  `{rows, columns}`; typed code has these ranks alone, and the translation, the vectors' and matrices' theorems and
  the two loop theorems are about them.
- **A rank of 3 or more is rectangular: a matrix of the levels below.** `"Nested"[A, shape]`, by recursion on the
  list `shape`, is the rectangular nesting of the levels below the first two: `"Nested"[A, {}]` is `A`, and
  `"Nested"[A, Prepend[ds, d]]` the lists of `d` values of `"Nested"[A, ds]`. An array of rank `k + 3` is a structure
  `"tensor"[inner, values, proof]`: `values` a `"Matrix"["Nested"[A, inner]]`, its rows and columns the first two
  levels, and the proof that `inner` has `k + 1` dimensions and that all the elements, the product of every dimension,
  are below 2^63.
- **The operations take every rank**, by cases on the rank, each case of ranks 1 and 2 computing to the operation
  the library has now:
  - `"arrayDimensions"`: `PackedArray[A, n] -> {ℕ}`; `{}`, `{length}`, `{rows, columns}` and the shape;
  - `"arrayTranspose"`, `Transpose`: `PackedArray[A, n + 2] -> PackedArray[A, n + 2]`, the first two levels swapped,
    as the Wolfram Language's Transpose of an array of rank 3 or more does; at rank 2 the matrix transpose. A rank
    below 2 has no transpose by its type, as Transpose of a vector fails in the Wolfram Language.
  - `Transpose` names `"arrayTranspose"` in `TypeTheoryEnvironment["Machine"]`, in place of the matrix one, and
    `Dimensions` of a packed array is `"arrayDimensions"` by the instance below.

## The theorems, for every rank

- `Length[Dimensions[a]] == n` for `a` of `PackedArray[A, n]`;
- `Dimensions[Transpose[a]]` is `Dimensions[a]` with its first two entries swapped, which at rank 2 is
  `Reverse[Dimensions[a]]`;
- `Transpose[Transpose[a]] == a`.

Each is proved by cases on the rank: ranks 0 to 2 by the matrix theorems there are, a rank of 3 or more by the same
theorems of the outer matrix, whose element type is `"Nested"[A, inner]`: Transpose of the first two levels is the
matrix transpose of `values`, so Transpose twice is `"matrixTransposeTwice"` and its dimensions
`"matrixDimensionsOfTranspose"`, joined to `inner`.

## Why nested and not flat, and the path to typed code of rank 3

The kernel's packed arrays of every rank are one flat row-major buffer with a shape (Stephen, 2026-11-19), and a flat
representation would be the kernel's own. It is not taken here because Transpose of a flat buffer is a permutation of
blocks, `new[[(j2 d1 + j1) R + r]] == old[[(j1 d2 + j2) R + r]]` for blocks of `R` elements, and Transpose twice and the
dimensions of a transpose then need lemmas of index arithmetic and of Partition and Join undoing each other; with the
first two levels a matrix they are the matrix theorems the library has already proved, applied to another element type.

Typed code has no array of rank 3 now. When it has, its translation reads the compiler's flat buffer, and the path is a
view in each direction, `"arrayOfFlat"[shape, data]` (Partition level by level, from the innermost) and
`"flatOfArray"[a]` (Catenate, from the outermost), with the theorems that they undo each other where the data has
the product of the shape as its length. A theorem about the nested array is then one about the flat buffer through
the views, and only the views need the arithmetic of positions.

## Dimensions, a class (0.57.0)

The Wolfram Language's `Dimensions` takes every expression, not packed arrays alone, so the prelude has it as the
method of a class, `"Dimensional"[T]`, and a packed array is one instance (the user, 2026-11-19). Each instance gives
two functions of a value: its dimensions and the head at each of its levels. A level counts while every subexpression
at it has the head of the whole and the same length, which is why the heads are kept: `f[g[1, 2], g[3, 4]]` has `{2}`
in the Wolfram Language, not `{2, 2}`. The prelude's instances are the expressions, the lists of a type with an
instance (their elements' levels, as far as all share them, under a level of `List`), the associations (their length
alone, as the Wolfram Language gives it), and the natural numbers, strings and Booleans (none). The machine library's
`"packedArrayDimensional"` gives `"arrayDimensions"` and a `List` at each level.

The dimensions are a method of their own, beside the heads, rather than read off a list of levels: then `Dimensions[a]`
of a packed array is `"arrayDimensions"[a]` by computation, even for an `a` that is a variable, and the theorems above,
stated with `Dimensions`, are proved by the library's theorems about `"arrayDimensions"` as they were.

## What does not change

Typed code still has ranks 1 and 2: `TypeTheoryFormalize` refuses a packed array of a rank above 2 by name, since the
compiler's typed entries have no other. The arrays of higher rank are mathematics, as `Dimensions` and `Transpose` are
for matrices now. No trust-boundary file changes: the library is checked by the kernel when it is built, and the names
are elaboration's table of meanings.

## Left for later

`Part` and `Length` over every rank (`Part` drops a level; `Length` is the first dimension), `Flatten`, and a uniform
representation of every rank by `"Nested"`, which would let ranks 1 and 2 be its cases too at the cost of restating the
vectors' and matrices' theorems and the translation.
