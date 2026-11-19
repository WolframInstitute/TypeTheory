(* ::Package:: *)

(*
The vectors and matrices of typed code: the packed arrays of rank 1 that the compiler's typed entries take, make and
return, and those of rank 2 that typed code makes inside a function, with their operations as typed code computes them,
in TypeTheoryEnvironment["Machine"] and, with the reals' arrays, TypeTheoryEnvironment["MachineReals"].

An array is a list that a machine can hold, a subtype of the prelude's lists: its length is below 2^63, so Length of
an array is a machine integer and never leaves, as in typed code. a["list"] is the list of an array a, as n["integer"]
is the integer of a machine integer, and a["proof"] the proof that the length is in range. Parts are counted from 1, or
below 0 from the end, and a part that is not there is the compiler's leave Failure["PartRange", <||>].

A matrix keeps its columns, as typed code's own matrix, {data, rows, columns}, does: m["columns"], the list of its rows
m["rows"], each as long as the columns, and m["proof"], that the columns, the rows and their product, the elements typed
code allocates, are below 2^63. A matrix with no rows still has its columns, Partition[{1, 2}, 3] 3, so that Transpose
twice is the identity on every matrix. Typed code makes a matrix by Partition of a vector alone, and reads its Length,
a row and an element; Dimensions, Transpose and the product by a vector are not typed code, and are here as the
mathematics typed code's loops are stated against.

	"PackedArray"[A, rank]           the compiler's "PackedArray"::[A, rank]: A at rank 0, the vectors at rank 1, the
	                                 matrices at rank 2, and at a rank above, the lists a machine holds of the arrays of
	                                 the rank below; the model has ranks 1 and 2, of "Integer64" or "Real64"
	"arrayLength"[a]                 Length[a], an "Integer64"
	"arrayPart"[a, i]                a[[i]], A | Failure
	"arraySetPart"[a, i, v]          the array of a[[i]] = v, by the same rule on i
	"arrayTake"[a, n]                Take[a, n]: the first n, or below 0 the last -n
	"arrayConstant"[c, n]            ConstantArray[c, n], leaving with Failure["Range", <||>] for a length below 0
	"arrayTotal"[a]                  Total of machine integers: the machine's sums from 0, left to right, leaving with
	                                 Failure["IntegerOverflow", <||>] where one does; typed code has no Total of reals
	"listPart", "listSetPart", "listTake", "listDrop", "listConstant"
	                                 the same on lists, a place counted from 0 by an integer
	"arrayOfList"[l]                 the array of a list, and the leave of an allocation that fails, Failure["Memory",
	                                 <||>], for a list too long to hold: no operation here reaches it
	"integerListSum", "partialSumsInRange"
	                                 the sum of the integers of a list, and that every sum on the way to it is a machine
	                                 integer: what a total is stated against
	"matrixOfPartition"[a, k]        Partition[a, k]: k columns, as many rows of k as the vector has, a shorter tail
	                                 dropped, leaving with Failure["Range", <||>] for k below 1
	"matrixLength"[m]                Length[m], the rows, an "Integer64"
	"matrixRow"[m, i]                m[[i]], a vector
	"matrixPart"[m, i, j]            m[[i, j]], each index by Part's rule
	"matrixDimensions"[m]            Dimensions[m], the list {rows, columns}, as the Wolfram Language gives it
	"matrixTranspose"[m]             Transpose[m]
	"matrixVectorProduct"[m, v]      the product of a matrix and a vector of machine integers, the exact sums of the
	                                 integers' products, row by row

Whether an allocation fails depends on the machine and not on the values, as the checks of the recursion level do,
which the model leaves out: the meaning of typed code is its value where it does not leave for want of memory. The
theorems say so of each operation: a part set keeps the length, "arraySetPartLength"; Take gives the length asked for,
"arrayTakeLength", and never more than the array has, "arrayTakeLengthBound"; each leaves by a part that is not there
alone, "arraySetPartLeave" and "arrayTakeLeave"; a constant array of a length a machine integer counts is there,
"arrayConstantOfNatural". A proof about a loop over an array takes its rounds with "arrayPartOfJoin" and
"arraySetPartOfJoin", the array split at the place the loop is at, and its invariant with "confirmBindThen".

Of matrices: Partition by a count a machine integer holds, 1 or more, is the matrix of its rows,
"matrixOfPartitionOfNatural", and by a count below 1 it leaves, "matrixOfPartitionRange"; a row and an element leave by
a part that is not there alone, "matrixRowLeave" and "matrixPartLeave"; Transpose twice is the identity,
"matrixTransposeTwice", and the dimensions of a transpose are the dimensions reversed, "matrixDimensionsOfTranspose". A proof
about a loop over a matrix and a vector takes the machine's dot product, "integerListDotTotal", which is the exact one
where every product and sum is in range, "integerListDotTotalOfSums"; the rows' dot products in turn, "rowsDotTotals"
and "rowsDotTotalsOfSums"; and an element of a matrix split at a place, "matrixPartOfJoin".
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[$machineArrayDeclarations]


(* ::Section:: *)
(*Usage Messages*)


$machineArrayDeclarations::usage = "$machineArrayDeclarations is the list of the declarations of the vectors and matrices of typed code, in order, which need the declarations of the machine integers before them."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations in order, each theorem proved by its tactics in the environment so far; the bound written as a
   literal *)
$machineArrayDeclarations = With[{upper = 9223372036854775808}, {
	(* the two cases of a sum are apart, and each is one to one: what a proof needs of a result that is known to be a
	   value, or known to be a leave *)
	TypeTheoryTheorem["rightNotLeft",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B]}, Implies[Typed["right"[f], A | B] == Typed["left"[x], A | B], False]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B], Typed[e, Typed["right"[f], A | B] == Typed["left"[x], A | B]]},
			"equalitySubstitution"[e, "trueIntroduction",
				P -> Function[{Typed[s, A | B]}, InductiveRecursor[DisjointUnionType][Function[{Typed[t, A | B]}, TypeUniverse[0]], Function[{Typed[a, A]}, False], Function[{Typed[b, B]}, True], s]]]]
	],
	TypeTheoryTheorem["leftNotRight",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B]}, Implies[Typed["left"[x], A | B] == Typed["right"[f], A | B], False]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B], Typed[e, Typed["left"[x], A | B] == Typed["right"[f], A | B]]},
			"rightNotLeft"[A, B, x, f, "equalitySymmetry"[e]]]
	],
	TypeTheoryTheorem["leftInjective",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[y, A]}, Implies[Typed["left"[x], A | B] == Typed["left"[y], A | B], x == y]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[e, Typed["left"[x], A | B] == Typed["left"[y], A | B]]},
			"equalityCongruence"[Function[{Typed[s, A | B]}, InductiveRecursor[DisjointUnionType][Function[{Typed[t, A | B]}, A], Function[{Typed[a, A]}, a], Function[{Typed[b, B]}, x], s]], e]]
	],
	TypeTheoryTheorem["rightInjective",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[f, B], Typed[g, B]}, Implies[Typed["right"[f], A | B] == Typed["right"[g], A | B], f == g]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[f, B], Typed[g, B], Typed[e, Typed["right"[f], A | B] == Typed["right"[g], A | B]]},
			"equalityCongruence"[Function[{Typed[s, A | B]}, InductiveRecursor[DisjointUnionType][Function[{Typed[t, A | B]}, B], Function[{Typed[a, A]}, f], Function[{Typed[b, B]}, b], s]], e]]
	],
	(* a failure passes through two continuations as through one: where each value's continuation, bound again, is g's.
	   The invariant of a loop is stated of the loop bound to what the function does with its state, and this takes a
	   round of the loop, a result bound to the rest of the loop, to the hypothesis of the induction *)
	machineTheorem["confirmBindThen",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[C, TypeUniverse[1]], Typed[m, A | Failure], Typed[f, A -> B | Failure], Typed[k, B -> C | Failure], Typed[g, A -> C | Failure]},
			Implies[ForAll[{Typed[t, A]}, "confirmBind"[f[t], k] == g[t]], "confirmBind"["confirmBind"[m, f], k] == "confirmBind"[m, g]]],
		{"Introduce"[A, B, C, m, f, k, g, h], "Cases"[m], "Introduce"[a], "Exact"[h[a]], "Introduce"[e], "Reflexivity"}
	],

	(* the lists a machine holds: the variable of the range names the list of an array, a["list"] *)
	TypeTheoryDefinition["arrayLengthRange", Typed[
		Function[{Typed[A, TypeUniverse[1]]}, Typed[list, {A}] |-> Length[list] < upper],
		ForAll[{Typed[A, TypeUniverse[1]]}, {A} -> TypeUniverse[0]]
	]],
	(* the matrices: every row as long as the columns, and the columns, the rows and the elements counts a machine
	   holds. The binders of "matrix" name the parts of a matrix, m["columns"], m["rows"] and m["proof"] *)
	TypeTheoryDefinition["rowsOfLength", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[rows, {{A}}], Typed[columns, NonNegativeIntegers]}, InductiveRecursor[List][
			Function[{Typed[t, {{A}}]}, TypeUniverse[0]],
			True,
			Function[{Typed[row, {A}], Typed[rest, {{A}}], Typed[r, TypeUniverse[0]]}, Length[row] == columns && r],
			rows
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {{A}} -> NonNegativeIntegers -> TypeUniverse[0]]
	]],
	TypeTheoryDefinition["matrixRange", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[columns, NonNegativeIntegers], Typed[rows, {{A}}]},
			columns < upper && Length[rows] < upper && Length[rows] columns < upper && "rowsOfLength"[rows, columns]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, NonNegativeIntegers -> {{A}} -> TypeUniverse[0]]
	]],
	TypeTheoryInductiveType[
		"Matrix",
		ForAll[{Typed[A, TypeUniverse[1]]}, TypeUniverse[1]],
		{"matrix" -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[columns, NonNegativeIntegers], Typed[rows, {{A}}], Typed[proof, "matrixRange"[columns, rows]]}, "Matrix"[A]]}
	],
	(* the levels of an array below its first two, rectangular, by recursion on their dimensions: none leaves an element,
	   and a dimension d before the rest the lists of d values of the levels below *)
	TypeTheoryDefinition["Nested", Typed[
		Function[{Typed[A, TypeUniverse[1]], Typed[shape, {NonNegativeIntegers}]}, InductiveRecursor[List][
			Function[{Typed[t, {NonNegativeIntegers}]}, TypeUniverse[1]],
			A,
			Function[{Typed[d, NonNegativeIntegers], Typed[ds, {NonNegativeIntegers}], Typed[r, TypeUniverse[1]]}, Subtype[Function[{Typed[l, {r}]}, Length[l] == d]]],
			shape
		]],
		TypeUniverse[1] -> {NonNegativeIntegers} -> TypeUniverse[1]
	]],
	(* the elements of an array of a shape, the product of its dimensions *)
	TypeTheoryDefinition["shapeElements", Typed[
		Function[{Typed[shape, {NonNegativeIntegers}]}, InductiveRecursor[List][
			Function[{Typed[t, {NonNegativeIntegers}]}, NonNegativeIntegers],
			1,
			Function[{Typed[d, NonNegativeIntegers], Typed[ds, {NonNegativeIntegers}], Typed[r, NonNegativeIntegers]}, d r],
			shape
		]],
		{NonNegativeIntegers} -> NonNegativeIntegers
	]],
	(* the arrays of rank k + 3: the first two levels a matrix of the levels below, of the k + 1 dimensions inner, and
	   all the elements, the product of every dimension, below 2^63. The binders of "tensor" name its parts,
	   t["inner"], t["values"] and t["proof"] *)
	TypeTheoryInductiveType[
		"Tensor",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[k, NonNegativeIntegers]}, TypeUniverse[1]],
		{"tensor" -> ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[k, NonNegativeIntegers], Typed[inner, {NonNegativeIntegers}],
			Typed[values, "Matrix"["Nested"[A, inner]]],
			Typed[proof, Length[inner] == k + 1 && "shapeElements"[inner] (Length[values[["rows"]]] values[["columns"]]) < upper]}, "Tensor"[A, k]]}
	],
	(* by its rank, as the compiler's type "PackedArray"::[t, rank]: an array of rank 0 is an element, of rank 1 a list
	   of elements a machine holds, of rank 2 a matrix, and of a rank k + 3 a "Tensor", the matrix of its first two
	   levels over the levels below, rectangular at every rank; typed code has ranks 1 and 2 alone. The arrays of ranks 1 and 2 compute to the lists and matrices of A
	   itself, and not of a recursion that is yet to compute: a hypothesis on a["list"] and a term written with {A} are
	   then the same term, which a rewrite needs *)
	TypeTheoryDefinition["PackedArray", Typed[
		Function[{Typed[A, TypeUniverse[1]], Typed[rank, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, TypeUniverse[1] -> TypeUniverse[1]],
			Function[{Typed[T, TypeUniverse[1]]}, T],
			Function[{Typed[k, NonNegativeIntegers], Typed[r, TypeUniverse[1] -> TypeUniverse[1]]}, Function[{Typed[T, TypeUniverse[1]]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[j, NonNegativeIntegers]}, TypeUniverse[1]],
					Subtype["arrayLengthRange"[T]],
					Function[{Typed[j, NonNegativeIntegers], Typed[s, TypeUniverse[1]]}, InductiveRecursor[NonNegativeIntegers][
						Function[{Typed[i, NonNegativeIntegers]}, TypeUniverse[1]],
						"Matrix"[T],
						Function[{Typed[i, NonNegativeIntegers], Typed[q, TypeUniverse[1]]}, "Tensor"[T, i]],
						j
					]],
					k
				]
			]],
			rank
		][A]],
		TypeUniverse[1] -> NonNegativeIntegers -> TypeUniverse[1]
	]],
	(* the element of a list at a place counted from 0 by an integer: the list is walked with the place counted
	   down, so a place below 0 or past the end is never met, and is not there *)
	TypeTheoryDefinition["listPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> (A | Failure)],
			Function[{Typed[j, Integers]}, Typed["right"[Failure["PartRange", <||>]], A | Failure]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> (A | Failure)]}, Function[{Typed[j, Integers]},
				"machineIf"["integerEqual"[j, 0], Typed["left"[x], A | Failure], r[j - 1]]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> Integers -> (A | Failure)]
	]],
	(* the list with the element at such a place set *)
	TypeTheoryDefinition["listSetPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}], Typed[v, A]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> ({A} | Failure)],
			Function[{Typed[j, Integers]}, Typed["right"[Failure["PartRange", <||>]], {A} | Failure]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> ({A} | Failure)]}, Function[{Typed[j, Integers]},
				"machineIf"["integerEqual"[j, 0],
					Typed["left"[Prepend[v][rest]], {A} | Failure],
					"confirmBind"[r[j - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]
				]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> A -> Integers -> ({A} | Failure)]
	]],
	(* the first elements of a list, as many as an integer counts, and the list without them; more than it has are
	   not there *)
	TypeTheoryDefinition["listTake", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> ({A} | Failure)],
			Function[{Typed[c, Integers]}, "machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> ({A} | Failure)]}, Function[{Typed[c, Integers]},
				"machineIf"["integerEqual"[c, 0],
					Typed["left"[Typed[{}, {A}]], {A} | Failure],
					"confirmBind"[r[c - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]
				]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> Integers -> ({A} | Failure)]
	]],
	TypeTheoryDefinition["listDrop", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> ({A} | Failure)],
			Function[{Typed[c, Integers]}, "machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> ({A} | Failure)]}, Function[{Typed[c, Integers]},
				"machineIf"["integerEqual"[c, 0], Typed["left"[Prepend[x][rest]], {A} | Failure], r[c - 1]]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> Integers -> ({A} | Failure)]
	]],
	(* the list of a number of copies of an element *)
	TypeTheoryDefinition["listConstant", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[c, A], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, {A}],
			Typed[{}, {A}],
			Function[{Typed[k, NonNegativeIntegers], Typed[r, {A}]}, Prepend[c][r]],
			n
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, A -> NonNegativeIntegers -> {A}]
	]],
	(* the array of a list a machine can hold, and for a longer one the leave of an allocation that fails. Setting a
	   part and Take never give such a list, "arraySetPartLeave" and "arrayTakeLeave", nor does a constant array of a
	   length a machine integer counts, "arrayConstantOfNatural": the leave is not part of the meaning of typed code *)
	TypeTheoryDefinition["arrayOfList", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[Decidable][
			Typed[d, Decidable["arrayLengthRange"[A][l]]] |-> "PackedArray"[A, 1] | Failure,
			Typed[h, Not["arrayLengthRange"[A][l]]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 1] | Failure],
			Typed[h, "arrayLengthRange"[A][l]] |-> Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure],
			"machineDecision"["arrayLengthRange"[A][l]]
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* Length never leaves: the length of an array's list is a machine integer by the array's own proof *)
	TypeTheoryDefinition["arrayLength", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]]},
			Typed["subtype"["integerOfNatural"[Length[a[["list"]]]], "naturalInteger64Range"[Length[a[["list"]]], a[["proof"]]]], "Integer64"]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> "Integer64"]
	]],
	(* a[[i]]: from 1, or below 0 from the end *)
	TypeTheoryDefinition["arrayPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers]},
			"machineIf"["integerLessEqualQ"[1, i],
				"listPart"[a[["list"]]][i - 1],
				"listPart"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + i]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> Integers -> (A | Failure)]
	]],
	(* a[[i]] = v: the array with the part set, by the same rule *)
	TypeTheoryDefinition["arraySetPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A]},
			"confirmBind"[
				"machineIf"["integerLessEqualQ"[1, i],
					"listSetPart"[a[["list"]], v][i - 1],
					"listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i]
				],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> Integers -> A -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* Take[a, n]: the first n, or below 0 the last -n *)
	TypeTheoryDefinition["arrayTake", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers]},
			"confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n],
					"listTake"[a[["list"]]][n],
					"listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]
				],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> Integers -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* ConstantArray[c, n]: the natural number of an integer that is not below 0 is the first of its normal pair; a
	   length below 0 is the compiler's leave Failure["Range", <||>] *)
	TypeTheoryDefinition["arrayConstant", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[c, A], Typed[n, Integers]},
			"machineIf"["integerLessEqualQ"[0, n],
				"arrayOfList"["listConstant"[c, "integerNormalPair"[n][[1]]]],
				Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 1] | Failure]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, A -> Integers -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* Total of machine integers: the machine's sums from 0, left to right, leaving where one does *)
	TypeTheoryDefinition["integerListTotal", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, "Integer64" -> ("Integer64" | Failure)],
			Function[{Typed[s, "Integer64"]}, Typed["left"[s], "Integer64" | Failure]],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, "Integer64" -> ("Integer64" | Failure)]}, Function[{Typed[s, "Integer64"]},
				"confirmBind"["machinePlus"[s[["integer"]], x[["integer"]]], r]
			]],
			l
		]],
		{"Integer64"} -> "Integer64" -> ("Integer64" | Failure)
	]],
	TypeTheoryDefinition["arrayTotal", Typed[
		Function[{Typed[a, "PackedArray"["Integer64", 1]]}, "confirmBind"["machineResult"[0], Function[{Typed[zero, "Integer64"]}, "integerListTotal"[a[["list"]]][zero]]]],
		"PackedArray"["Integer64", 1] -> ("Integer64" | Failure)
	]],
	(* the mathematics the total is stated against: the sum of the integers of a list of machine integers, and that
	   every sum on the way to it from s, left to right, is one a machine holds *)
	TypeTheoryDefinition["integerListSum", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, Integers],
			Typed[0, Integers],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, Integers]}, x[["integer"]] + r],
			l
		]],
		{"Integer64"} -> Integers
	]],
	TypeTheoryDefinition["partialSumsInRange", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, Integers -> TypeUniverse[0]],
			Function[{Typed[s, Integers]}, True],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, Integers -> TypeUniverse[0]]}, Function[{Typed[s, Integers]},
				"integer64Range"[s + x[["integer"]]] && r[s + x[["integer"]]]
			]],
			l
		]],
		{"Integer64"} -> Integers -> TypeUniverse[0]
	]],
	(* the element of a list at an index counted as Part counts it, from 1, or below 0 from the end *)
	TypeTheoryDefinition["listPartOfIndex", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}], Typed[i, Integers]},
			"machineIf"["integerLessEqualQ"[1, i], "listPart"[l][i - 1], "listPart"[l]["integerOfNatural"[Length[l]] + i]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> Integers -> (A | Failure)]
	]],
	(* the first n elements of a list, all of them where it has fewer *)
	TypeTheoryDefinition["listFirst", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}], Typed[n, NonNegativeIntegers]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, NonNegativeIntegers -> {A}],
				Function[{Typed[k, NonNegativeIntegers]}, Typed[{}, {A}]],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, NonNegativeIntegers -> {A}]},
					Function[{Typed[k, NonNegativeIntegers]},
						InductiveRecursor[NonNegativeIntegers][Typed[j, NonNegativeIntegers] |-> {A}, Typed[{}, {A}], {Typed[j, NonNegativeIntegers], Typed[s, {A}]} |-> Prepend[x][r[j]], k]
					]
				],
				l
			][n]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> NonNegativeIntegers -> {A}]
	]],
	(* the rows of Partition[l, n]: the first n elements, then the rows of the rest, while n elements are left; a
	   shorter tail is dropped. A row takes at least one element where n is above 0, so as many rounds as the list is
	   long are enough; Partition by 0 leaves before it is reached *)
	TypeTheoryDefinition["partitionRows", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[k, NonNegativeIntegers]}, {A} -> {{A}}],
				Function[{Typed[l, {A}]}, Typed[{}, {{A}}]],
				Function[{Typed[k, NonNegativeIntegers], Typed[r, {A} -> {{A}}]}, Function[{Typed[l, {A}]},
					"machineIf"["lessEqual"[n, Length[l]], Prepend["listFirst"[l, n]][r[Drop[l, n]]], Typed[{}, {{A}}]]
				]],
				fuel
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, NonNegativeIntegers -> NonNegativeIntegers -> {A} -> {{A}}]
	]],
	TypeTheoryDefinition["listPartition", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}], Typed[n, NonNegativeIntegers]}, "partitionRows"[n, Length[l]][l]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> NonNegativeIntegers -> {{A}}]
	]],
	(* each element of a row put before its column, the row and the columns as long as each other *)
	TypeTheoryDefinition["prependColumns", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[row, {A}]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, {{A}} -> {{A}}],
			Function[{Typed[columns, {{A}}]}, columns],
			Function[{Typed[x, A], Typed[xs, {A}], Typed[r, {{A}} -> {{A}}]}, Function[{Typed[columns, {{A}}]},
				InductiveRecursor[List][
					Function[{Typed[t, {{A}}]}, {{A}}],
					Typed[{}, {{A}}],
					Function[{Typed[column, {A}], Typed[rest, {{A}}], Typed[s, {{A}}]}, Prepend[Prepend[x][column]][r[rest]]],
					columns
				]
			]],
			row
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> {{A}} -> {{A}}]
	]],
	(* the columns of rows of a length, as lists: no rows give that many empty columns *)
	TypeTheoryDefinition["transposeRows", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[columns, NonNegativeIntegers], Typed[rows, {{A}}]}, InductiveRecursor[List][
			Function[{Typed[t, {{A}}]}, {{A}}],
			"listConstant"[Typed[{}, {A}], columns],
			Function[{Typed[row, {A}], Typed[rest, {{A}}], Typed[r, {{A}}]}, "prependColumns"[row][r]],
			rows
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, NonNegativeIntegers -> {{A}} -> {{A}}]
	]],
	(* typed code's operations on a matrix: Length, the rows, which never leaves; a row, m[[i]], a vector; and an
	   element, m[[i, j]], each index counted as Part counts it *)
	TypeTheoryDefinition["matrixLength", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]},
			Typed["subtype"["integerOfNatural"[Length[m[["rows"]]]], "naturalInteger64Range"[Length[m[["rows"]]], m[["proof"]][["right"]][["left"]]]], "Integer64"]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 2] -> "Integer64"]
	]],
	TypeTheoryDefinition["matrixRow", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]], Typed[i, Integers]},
			"confirmBind"["listPartOfIndex"[m[["rows"]], i], Function[{Typed[row, {A}]}, "arrayOfList"[row]]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 2] -> Integers -> ("PackedArray"[A, 1] | Failure)]
	]],
	TypeTheoryDefinition["matrixPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]], Typed[i, Integers], Typed[j, Integers]},
			"confirmBind"["listPartOfIndex"[m[["rows"]], i], Function[{Typed[row, {A}]}, "listPartOfIndex"[row, j]]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 2] -> Integers -> Integers -> (A | Failure)]
	]],
	(* the mathematics: Dimensions, the list of the counts of the rows and the columns, as the Wolfram Language gives it;
	   and the product of a matrix and a
	   vector of machine integers, the exact sum of the integers' products for each row, as far as the shorter goes *)
	TypeTheoryDefinition["matrixDimensions", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]},
			Typed[{Length[m[["rows"]]], m[["columns"]]}, {NonNegativeIntegers}]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 2] -> {NonNegativeIntegers}]
	]],
	TypeTheoryDefinition["integerListDot", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, {"Integer64"} -> Integers],
			Function[{Typed[w, {"Integer64"}]}, Typed[0, Integers]],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, {"Integer64"} -> Integers]}, Function[{Typed[w, {"Integer64"}]},
				InductiveRecursor[List][
					Function[{Typed[t, {"Integer64"}]}, Integers],
					Typed[0, Integers],
					Function[{Typed[y, "Integer64"], Typed[ys, {"Integer64"}], Typed[s, Integers]}, x[["integer"]] y[["integer"]] + r[ys]],
					w
				]
			]],
			l
		]],
		{"Integer64"} -> {"Integer64"} -> Integers
	]],
	TypeTheoryDefinition["matrixVectorProduct", Typed[
		Function[{Typed[m, "PackedArray"["Integer64", 2]], Typed[v, "PackedArray"["Integer64", 1]]},
			Map[Function[{Typed[row, {"Integer64"}]}, "integerListDot"[row][v[["list"]]]], m[["rows"]]]
		],
		"PackedArray"["Integer64", 2] -> "PackedArray"["Integer64", 1] -> {Integers}
	]],

	(* a list a machine can hold is its array, with no leave: the decision of the range, whatever the instance, takes its
	   true case, and any two proofs of the range are one. And the array of a list, where there is one, has that list *)
	TypeTheoryTheorem["arrayOfListInRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[h, "arrayLengthRange"[A][l]]}, "arrayOfList"[l] == Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure]],
		Function[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[h, "arrayLengthRange"[A][l]]}, InductiveRecursor[Decidable][
			Typed[d, Decidable["arrayLengthRange"[A][l]]] |-> InductiveRecursor[Decidable][
				Typed[e, Decidable["arrayLengthRange"[A][l]]] |-> "PackedArray"[A, 1] | Failure,
				Typed[k, Not["arrayLengthRange"[A][l]]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 1] | Failure],
				Typed[k, "arrayLengthRange"[A][l]] |-> Typed["left"["subtype"[l, k]], "PackedArray"[A, 1] | Failure],
				d
			] == Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure],
			Typed[k, Not["arrayLengthRange"[A][l]]] |-> "falseElimination"[k[h]],
			Typed[k, "arrayLengthRange"[A][l]] |-> "equalityReflexivity"[Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure]],
			"machineDecision"["arrayLengthRange"[A][l]]
		]]
	],
	machineTheorem["arrayOfListValue",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, {A}], Typed[b, "PackedArray"[A, 1]]}, Implies["arrayOfList"[m] == Typed["left"[b], "PackedArray"[A, 1] | Failure], b[["list"]] == m]],
		{"Introduce"[A, m, b],
			"Change"[Implies[InductiveRecursor[Decidable][
				Typed[d, Decidable["arrayLengthRange"[A][m]]] |-> "PackedArray"[A, 1] | Failure,
				Typed[k, Not["arrayLengthRange"[A][m]]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 1] | Failure],
				Typed[k, "arrayLengthRange"[A][m]] |-> Typed["left"["subtype"[m, k]], "PackedArray"[A, 1] | Failure],
				"machineDecision"["arrayLengthRange"[A][m]]
			] == Typed["left"[b], "PackedArray"[A, 1] | Failure], b[["list"]] == m]],
			"Cases"["machineDecision"["arrayLengthRange"[A][m]]],
			"Introduce"[k, h], "Exact"["falseElimination"["rightNotLeft"["PackedArray"[A, 1], Failure, b, Failure["Memory", <||>], h]]],
			"Introduce"[k, h], "Rewrite"["leftInjective"["PackedArray"[A, 1], Failure, "subtype"[m, k], b, h], "RightToLeft"], "Reflexivity"}
	],
	(* the integer of an array's length is the integer of its list's *)
	machineTheorem["arrayLengthInteger",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, "PackedArray"[A, 1]]}, "arrayLength"[v][["integer"]] == "integerOfNatural"[Length[v[["list"]]]]],
		{"Introduce"[A, v], "Reflexivity"}
	],
	(* a constant list has the length given *)
	machineTheorem["listConstantLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, A], Typed[n, NonNegativeIntegers]}, Length["listConstant"[c, n]] == n],
		{"Introduce"[A, c, n], "Induction"[n], "Reflexivity", "Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]}
	],
	(* the part of a list at the length of what comes before it, and the list with that part set *)
	machineTheorem["listPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[x, A], Typed[rest, {A}], Typed[pre, {A}]},
			"listPart"[Join[pre, Prepend[x][rest]]]["integerOfNatural"[Length[pre]]] == Typed["left"[x], A | Failure]],
		{"Introduce"[A, x, rest, pre], "Induction"[pre],
			"Reflexivity",
			"Introduce"[y, tail, ih],
			"Change"["machineIf"["integerEqual"["integerOfNatural"[Length[tail] + 1], 0], Typed["left"[y], A | Failure],
				"listPart"[Join[tail, Prepend[x][rest]]]["integerOfNatural"[Length[tail] + 1] - 1]] == Typed["left"[x], A | Failure]],
			"Rewrite"["integerOfSuccessorNotZero"[Length[tail]]], "Rewrite"["integerOfNaturalPredecessor"[Length[tail]]], "Exact"[ih]}
	],
	machineTheorem["listSetPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, A], Typed[y, A], Typed[rest, {A}], Typed[pre, {A}]},
			"listSetPart"[Join[pre, Prepend[y][rest]], v]["integerOfNatural"[Length[pre]]] == Typed["left"[Join[pre, Prepend[v][rest]]], {A} | Failure]],
		{"Introduce"[A, v, y, rest, pre], "Induction"[pre],
			"Reflexivity",
			"Introduce"[z, tail, ih],
			"Change"["machineIf"["integerEqual"["integerOfNatural"[Length[tail] + 1], 0],
				Typed["left"[Prepend[v][Join[tail, Prepend[y][rest]]]], {A} | Failure],
				"confirmBind"["listSetPart"[Join[tail, Prepend[y][rest]], v]["integerOfNatural"[Length[tail] + 1] - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[z][t]], {A} | Failure]]]
			] == Typed["left"[Join[Prepend[z][tail], Prepend[v][rest]]], {A} | Failure]],
			"Rewrite"["integerOfSuccessorNotZero"[Length[tail]]], "Rewrite"["integerOfNaturalPredecessor"[Length[tail]]], "Rewrite"[ih], "Reflexivity"}
	],
	(* a list with a part set is as long as it was, and the setting leaves by a part that is not there alone *)
	machineTheorem["listSetPartLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, A], Typed[l, {A}], Typed[j, Integers], Typed[m, {A}]},
			Implies["listSetPart"[l, v][j] == Typed["left"[m], {A} | Failure], Length[m] == Length[l]]],
		{"Introduce"[A, v, l], "Induction"[l],
			"Introduce"[j, m, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, Failure["PartRange", <||>], h]]],
			"Introduce"[x, rest, ih, j, m],
			"Change"[Implies["machineIf"["integerEqual"[j, 0], Typed["left"[Prepend[v][rest]], {A} | Failure],
				"confirmBind"["listSetPart"[rest, v][j - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["left"[m], {A} | Failure], Length[m] == Length[rest] + 1]],
			"Cases"["integerEqual"[j, 0]],
			"Have"[ih2, ForAll[{Typed[t, {A}]}, Implies["listSetPart"[rest, v][j - 1] == Typed["left"[t], {A} | Failure], Length[t] == Length[rest]]]], "Exact"[ih[j - 1]],
			"Generalize"[ih2], "Cases"["listSetPart"[rest, v][j - 1]],
			"Introduce"[t, ih2, h],
			"Have"[hl, Length[t] == Length[rest]], "Exact"[ih2[t, "equalityReflexivity"[Typed["left"[t], {A} | Failure]]]],
			"Rewrite"["leftInjective"[{A}, Failure, Prepend[x][t], m, h], "RightToLeft"], "Exact"["equalityCongruence"["successor", hl]],
			"Introduce"[f, ih2, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, f, h]]],
			"Introduce"[h], "Rewrite"["leftInjective"[{A}, Failure, Prepend[v][rest], m, h], "RightToLeft"], "Reflexivity"}
	],
	machineTheorem["listSetPartLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, A], Typed[l, {A}], Typed[j, Integers], Typed[f, Failure]},
			Implies["listSetPart"[l, v][j] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, v, l], "Induction"[l],
			"Introduce"[j, f, h], "Exact"["equalitySymmetry"["rightInjective"[{A}, Failure, Failure["PartRange", <||>], f, h]]],
			"Introduce"[x, rest, ih, j, f],
			"Change"[Implies["machineIf"["integerEqual"[j, 0], Typed["left"[Prepend[v][rest]], {A} | Failure],
				"confirmBind"["listSetPart"[rest, v][j - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[j, 0]],
			"Have"[ih2, ForAll[{Typed[g, Failure]}, Implies["listSetPart"[rest, v][j - 1] == Typed["right"[g], {A} | Failure], g == Failure["PartRange", <||>]]]], "Exact"[ih[j - 1]],
			"Generalize"[ih2], "Cases"["listSetPart"[rest, v][j - 1]],
			"Introduce"[t, ih2, h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[x][t], f, h]]],
			"Introduce"[g, ih2, h], "Rewrite"["rightInjective"[{A}, Failure, g, f, h], "RightToLeft"], "Exact"[ih2[g, "equalityReflexivity"[Typed["right"[g], {A} | Failure]]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[v][rest], f, h]]]}
	],
	(* Take gives the length asked for, of a list no longer than the one it takes from, and leaves by a part that is
	   not there alone *)
	machineTheorem["listTakeLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[m, {A}]},
			Implies["listTake"[l][c] == Typed["left"[m], {A} | Failure], "integerOfNatural"[Length[m]] == c && Length[m] <= Length[l]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["left"[m], {A} | Failure],
				"integerOfNatural"[Length[m]] == c && Length[m] <= 0]],
			"Have"[hc, Implies["integerEqual"[c, 0] == "true", c == 0]], "Exact"["integerEqualTrue"[c, 0]],
			"Generalize"[hc], "Cases"["integerEqual"[c, 0]],
			"Introduce"[hc, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, Failure["PartRange", <||>], h]]],
			"Introduce"[hc, h], "Rewrite"["leftInjective"[{A}, Failure, Typed[{}, {A}], m, h], "RightToLeft"],
			"Exact"["andIntroduction"["equalitySymmetry"[hc["equalityReflexivity"["true"]]], "lessEqualZero"[0]]],
			"Introduce"[x, rest, ih, c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure],
				"confirmBind"["listTake"[rest][c - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["left"[m], {A} | Failure],
				"integerOfNatural"[Length[m]] == c && Length[m] <= Length[rest] + 1]],
			"Have"[hc, Implies["integerEqual"[c, 0] == "true", c == 0]], "Exact"["integerEqualTrue"[c, 0]],
			"Generalize"[hc], "Cases"["integerEqual"[c, 0]],
			"Introduce"[hc],
			"Have"[ih2, ForAll[{Typed[t, {A}]}, Implies["listTake"[rest][c - 1] == Typed["left"[t], {A} | Failure], "integerOfNatural"[Length[t]] == c - 1 && Length[t] <= Length[rest]]]], "Exact"[ih[c - 1]],
			"Generalize"[ih2], "Cases"["listTake"[rest][c - 1]],
			"Introduce"[t, ih2, h],
			"Have"[hl, "integerOfNatural"[Length[t]] == c - 1 && Length[t] <= Length[rest]], "Exact"[ih2[t, "equalityReflexivity"[Typed["left"[t], {A} | Failure]]]],
			"Rewrite"["leftInjective"[{A}, Failure, Prepend[x][t], m, h], "RightToLeft"],
			"Change"["integerOfNatural"[Length[t] + 1] == c && Length[t] + 1 <= Length[rest] + 1],
			"Apply"["andIntroduction"],
			"Rewrite"["integerOfNaturalAddition"[Length[t], 1]], "Rewrite"[hl[["left"]]], "Ring",
			"Exact"["lessEqualSuccessor"[hl[["right"]]]],
			"Introduce"[f, ih2, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, f, h]]],
			"Introduce"[hc, h], "Rewrite"["leftInjective"[{A}, Failure, Typed[{}, {A}], m, h], "RightToLeft"],
			"Exact"["andIntroduction"["equalitySymmetry"[hc["equalityReflexivity"["true"]]], "lessEqualZero"[Length[rest] + 1]]]}
	],
	machineTheorem["listTakeLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[f, Failure]},
			Implies["listTake"[l][c] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["right"[f], {A} | Failure],
				f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["equalitySymmetry"["rightInjective"[{A}, Failure, Failure["PartRange", <||>], f, h]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Typed[{}, {A}], f, h]]],
			"Introduce"[x, rest, ih, c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure],
				"confirmBind"["listTake"[rest][c - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Have"[ih2, ForAll[{Typed[g, Failure]}, Implies["listTake"[rest][c - 1] == Typed["right"[g], {A} | Failure], g == Failure["PartRange", <||>]]]], "Exact"[ih[c - 1]],
			"Generalize"[ih2], "Cases"["listTake"[rest][c - 1]],
			"Introduce"[t, ih2, h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[x][t], f, h]]],
			"Introduce"[g, ih2, h], "Rewrite"["rightInjective"[{A}, Failure, g, f, h], "RightToLeft"], "Exact"[ih2[g, "equalityReflexivity"[Typed["right"[g], {A} | Failure]]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Typed[{}, {A}], f, h]]]}
	],
	(* a list without its first elements is no longer than it, and it too leaves by a part that is not there alone *)
	machineTheorem["listDropLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[m, {A}]},
			Implies["listDrop"[l][c] == Typed["left"[m], {A} | Failure], Length[m] <= Length[l]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["left"[m], {A} | Failure],
				Length[m] <= 0]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, Failure["PartRange", <||>], h]]],
			"Introduce"[h], "Rewrite"["leftInjective"[{A}, Failure, Typed[{}, {A}], m, h], "RightToLeft"], "Exact"["lessEqualZero"[0]],
			"Introduce"[x, rest, ih, c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Prepend[x][rest]], {A} | Failure], "listDrop"[rest][c - 1]] == Typed["left"[m], {A} | Failure], Length[m] <= Length[rest] + 1]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["lessEqualStep"[ih[c - 1, m, h]]],
			"Introduce"[h], "Rewrite"["leftInjective"[{A}, Failure, Prepend[x][rest], m, h], "RightToLeft"], "Change"[Length[rest] + 1 <= Length[rest] + 1], "Exact"["lessEqualReflexivity"]}
	],
	machineTheorem["listDropLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[f, Failure]},
			Implies["listDrop"[l][c] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["right"[f], {A} | Failure],
				f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["equalitySymmetry"["rightInjective"[{A}, Failure, Failure["PartRange", <||>], f, h]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Typed[{}, {A}], f, h]]],
			"Introduce"[x, rest, ih, c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Prepend[x][rest]], {A} | Failure], "listDrop"[rest][c - 1]] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"[ih[c - 1, f, h]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[x][rest], f, h]]]}
	],
	(* an operation on the list of an array, made an array again: where the array is there, the operation gave its list;
	   and where the operation gives lists no longer than the array's, the leave is the operation's own, the same
	   failure in the sum of the lists and in the sum of the arrays *)
	machineTheorem["arrayOfResultValue",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[r, {A} | Failure], Typed[b, "PackedArray"[A, 1]]},
			Implies["confirmBind"[r, Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], r == Typed["left"[b[["list"]]], {A} | Failure]]],
		{"Introduce"[A, r], "Cases"[r],
			"Introduce"[m, b, h], "Rewrite"["arrayOfListValue"[A, m, b, h]],
			"Introduce"[f, b, h], "Exact"["falseElimination"["rightNotLeft"["PackedArray"[A, 1], Failure, b, f, h]]]}
	],
	machineTheorem["arrayOfResultLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[r, {A} | Failure], Typed[e, Failure]},
			Implies[ForAll[{Typed[m, {A}]}, Implies[r == Typed["left"[m], {A} | Failure], Length[m] <= Length[a[["list"]]]]],
				Implies["confirmBind"[r, Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["right"[e], "PackedArray"[A, 1] | Failure], r == Typed["right"[e], {A} | Failure]]]],
		{"Introduce"[A, a, r], "Cases"[r],
			"Introduce"[m, e, hb, h],
			"Have"[shorter, Length[m] <= Length[a[["list"]]]], "Exact"[hb[m, "equalityReflexivity"[Typed["left"[m], {A} | Failure]]]],
			"Have"[held, Length[a[["list"]]] < upper], "Exact"[a[["proof"]]],
			"Have"[hr, "arrayLengthRange"[A][m]], "Exact"["lessEqualTransitivity"["lessEqualSuccessor"[shorter], held]],
			"Have"[h2, "arrayOfList"[m] == Typed["right"[e], "PackedArray"[A, 1] | Failure]], "Exact"[h],
			"Rewrite"["arrayOfListInRange"[A, m, hr], "At" -> h2],
			"Exact"["falseElimination"["leftNotRight"["PackedArray"[A, 1], Failure, "subtype"[m, hr], e, h2]]],
			"Introduce"[f, e, hb, h],
			"Have"[h3, Typed["right"[f], "PackedArray"[A, 1] | Failure] == Typed["right"[e], "PackedArray"[A, 1] | Failure]], "Exact"[h],
			"Rewrite"["rightInjective"["PackedArray"[A, 1], Failure, f, e, h3]]}
	],
	(* the part of an array at the place after what comes before it *)
	machineTheorem["arrayPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[x, A], Typed[rest, {A}]},
			Implies[v[["list"]] == Join[pre, Prepend[x][rest]], "arrayPart"[v, "integerOfNatural"[Length[pre] + 1]] == Typed["left"[x], A | Failure]]],
		{"Introduce"[A, v, pre, x, rest, e],
			"Have"[positive, 1 <= Length[pre] + 1], "LinearArithmetic",
			"Change"["machineIf"["integerLessEqualQ"[1, "integerOfNatural"[Length[pre] + 1]],
				"listPart"[v[["list"]]]["integerOfNatural"[Length[pre] + 1] - 1],
				"listPart"[v[["list"]]]["integerOfNatural"[Length[v[["list"]]]] + "integerOfNatural"[Length[pre] + 1]]] == Typed["left"[x], A | Failure]],
			"Rewrite"["integerLessEqualQOfNatural"[1, Length[pre] + 1, positive]],
			"Rewrite"["integerOfNaturalPredecessor"[Length[pre]]],
			"Rewrite"[e],
			"Exact"["listPartOfJoin"[A, x, rest, pre]]}
	],
	(* an array with a part set is an array, the list as long as it was; the part of an array set at the place after
	   what comes before it, with the proof of the range named, and then as an array there is, whose list is known *)
	machineTheorem["arraySetPartRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[y, A], Typed[v, A], Typed[rest, {A}]},
			Implies[a[["list"]] == Join[pre, Prepend[y][rest]], "arrayLengthRange"[A][Join[pre, Prepend[v][rest]]]]],
		{"Introduce"[A, a, pre, y, v, rest, e],
			"Change"[Length[Join[pre, Prepend[v][rest]]] < upper], "Rewrite"["lengthJoin"[pre, Prepend[v][rest]]],
			"Change"[Length[pre] + Length[Prepend[y][rest]] < upper], "Rewrite"["lengthJoin"[pre, Prepend[y][rest]], "RightToLeft"],
			"Rewrite"[e, "RightToLeft"], "Exact"[a[["proof"]]]}
	],
	machineTheorem["arraySetPartOfJoinInRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[y, A], Typed[v, A], Typed[rest, {A}], Typed[h, "arrayLengthRange"[A][Join[pre, Prepend[v][rest]]]]},
			Implies[a[["list"]] == Join[pre, Prepend[y][rest]],
				"arraySetPart"[a, "integerOfNatural"[Length[pre] + 1], v] == Typed["left"["subtype"[Join[pre, Prepend[v][rest]], h]], "PackedArray"[A, 1] | Failure]]],
		{"Introduce"[A, a, pre, y, v, rest, h, e],
			"Have"[positive, 1 <= Length[pre] + 1], "LinearArithmetic",
			"Change"["confirmBind"[
				"machineIf"["integerLessEqualQ"[1, "integerOfNatural"[Length[pre] + 1]],
					"listSetPart"[a[["list"]], v]["integerOfNatural"[Length[pre] + 1] - 1],
					"listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + "integerOfNatural"[Length[pre] + 1]]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"["subtype"[Join[pre, Prepend[v][rest]], h]], "PackedArray"[A, 1] | Failure]],
			"Rewrite"["integerLessEqualQOfNatural"[1, Length[pre] + 1, positive]],
			"Rewrite"["integerOfNaturalPredecessor"[Length[pre]]],
			"Rewrite"[e],
			"Rewrite"["listSetPartOfJoin"[A, v, y, rest, pre]],
			"Exact"["arrayOfListInRange"[A, Join[pre, Prepend[v][rest]], h]]}
	],
	machineTheorem["arraySetPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[y, A], Typed[v, A], Typed[rest, {A}]},
			Implies[a[["list"]] == Join[pre, Prepend[y][rest]],
				Exists[{Typed[b, "PackedArray"[A, 1]]}, "arraySetPart"[a, "integerOfNatural"[Length[pre] + 1], v] == Typed["left"[b], "PackedArray"[A, 1] | Failure] && b[["list"]] == Join[pre, Prepend[v][rest]]]]],
		{"Introduce"[A, a, pre, y, v, rest, e],
			"Have"[h, "arrayLengthRange"[A][Join[pre, Prepend[v][rest]]]], "Exact"["arraySetPartRange"[A, a, pre, y, v, rest, e]],
			"Exact"["existsIntroduction"["subtype"[Join[pre, Prepend[v][rest]], h],
				"andIntroduction"["arraySetPartOfJoinInRange"[A, a, pre, y, v, rest, h, e], "equalityReflexivity"[Join[pre, Prepend[v][rest]]]]]]}
	],
	(* a[[i]] = v keeps the length, and leaves by a part that is not there alone *)
	machineTheorem["arraySetPartLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A], Typed[b, "PackedArray"[A, 1]]},
			Implies["arraySetPart"[a, i, v] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] == Length[a[["list"]]]]],
		{"Introduce"[A, a, i, v, b],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[1, i], "listSetPart"[a[["list"]], v][i - 1], "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] == Length[a[["list"]]]]],
			"Cases"["integerLessEqualQ"[1, i]],
			"Introduce"[h], "Exact"["listSetPartLength"[A, v, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + i, b[["list"]],
				"arrayOfResultValue"[A, "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i], b, h]]],
			"Introduce"[h], "Exact"["listSetPartLength"[A, v, a[["list"]], i - 1, b[["list"]], "arrayOfResultValue"[A, "listSetPart"[a[["list"]], v][i - 1], b, h]]]}
	],
	machineTheorem["arraySetPartLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A], Typed[e, Failure]},
			Implies["arraySetPart"[a, i, v] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
		{"Introduce"[A, a, i, v, e],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[1, i], "listSetPart"[a[["list"]], v][i - 1], "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
			"Cases"["integerLessEqualQ"[1, i]],
			"Introduce"[h], "Exact"["listSetPartLeave"[A, v, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + i, e,
				"arrayOfResultLeave"[A, a, "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i], e,
					Function[{Typed[m, {A}], Typed[hm, "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i] == Typed["left"[m], {A} | Failure]]},
						"equalitySubstitution"["equalitySymmetry"["listSetPartLength"[A, v, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + i, m, hm]], "lessEqualReflexivity",
							P -> Function[{Typed[k, NonNegativeIntegers]}, k <= Length[a[["list"]]]]]],
					h]]],
			"Introduce"[h], "Exact"["listSetPartLeave"[A, v, a[["list"]], i - 1, e,
				"arrayOfResultLeave"[A, a, "listSetPart"[a[["list"]], v][i - 1], e,
					Function[{Typed[m, {A}], Typed[hm, "listSetPart"[a[["list"]], v][i - 1] == Typed["left"[m], {A} | Failure]]},
						"equalitySubstitution"["equalitySymmetry"["listSetPartLength"[A, v, a[["list"]], i - 1, m, hm]], "lessEqualReflexivity",
							P -> Function[{Typed[k, NonNegativeIntegers]}, k <= Length[a[["list"]]]]]],
					h]]]}
	],
	(* Take[a, n] of a count that is not below 0 has the length n; of any count, a length no more than the array's; and it
	   leaves by a part that is not there alone *)
	machineTheorem["arrayTakeLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[b, "PackedArray"[A, 1]]},
			Implies["integerLessEqualQ"[0, n] == "true", Implies["arrayTake"[a, n] == Typed["left"[b], "PackedArray"[A, 1] | Failure], "integerOfNatural"[Length[b[["list"]]]] == n]]],
		{"Introduce"[A, a, n, b, hn],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n], "listTake"[a[["list"]]][n], "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], "integerOfNatural"[Length[b[["list"]]]] == n]],
			"Rewrite"[hn], "Introduce"[h],
			"Exact"["andEliminationLeft"["listTakeLength"[A, a[["list"]], n, b[["list"]], "arrayOfResultValue"[A, "listTake"[a[["list"]]][n], b, h]]]]}
	],
	machineTheorem["arrayTakeLengthBound",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[b, "PackedArray"[A, 1]]},
			Implies["arrayTake"[a, n] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] <= Length[a[["list"]]]]],
		{"Introduce"[A, a, n, b],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n], "listTake"[a[["list"]]][n], "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] <= Length[a[["list"]]]]],
			"Cases"["integerLessEqualQ"[0, n]],
			"Introduce"[h], "Exact"["listDropLength"[A, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + n, b[["list"]],
				"arrayOfResultValue"[A, "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n], b, h]]],
			"Introduce"[h], "Exact"["andEliminationRight"["listTakeLength"[A, a[["list"]], n, b[["list"]], "arrayOfResultValue"[A, "listTake"[a[["list"]]][n], b, h]]]]}
	],
	machineTheorem["arrayTakeLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[e, Failure]},
			Implies["arrayTake"[a, n] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
		{"Introduce"[A, a, n, e],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n], "listTake"[a[["list"]]][n], "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
			"Cases"["integerLessEqualQ"[0, n]],
			"Introduce"[h], "Exact"["listDropLeave"[A, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + n, e,
				"arrayOfResultLeave"[A, a, "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n], e,
					Function[{Typed[m, {A}], Typed[hm, "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n] == Typed["left"[m], {A} | Failure]]},
						"listDropLength"[A, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + n, m, hm]],
					h]]],
			"Introduce"[h], "Exact"["listTakeLeave"[A, a[["list"]], n, e,
				"arrayOfResultLeave"[A, a, "listTake"[a[["list"]]][n], e,
					Function[{Typed[m, {A}], Typed[hm, "listTake"[a[["list"]]][n] == Typed["left"[m], {A} | Failure]]},
						"andEliminationRight"["listTakeLength"[A, a[["list"]], n, m, hm]]],
					h]]]}
	],
	(* a constant array of a length a machine integer counts: there is the array, and its list is known *)
	machineTheorem["arrayConstantOfNatural",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, A], Typed[k, NonNegativeIntegers]}, Implies[k < upper,
			Exists[{Typed[a, "PackedArray"[A, 1]]}, "arrayConstant"[c, "integerOfNatural"[k]] == Typed["left"[a], "PackedArray"[A, 1] | Failure] && a[["list"]] == "listConstant"[c, k]]]],
		{"Introduce"[A, c, k, hk],
			"Have"[h, "arrayLengthRange"[A]["listConstant"[c, k]]],
			"Change"[Length["listConstant"[c, k]] < upper], "Rewrite"["listConstantLength"[A, c, k]], "Exact"[hk],
			"Have"[hc, "arrayConstant"[c, "integerOfNatural"[k]] == Typed["left"["subtype"["listConstant"[c, k], h]], "PackedArray"[A, 1] | Failure]],
			"Change"["machineIf"["integerLessEqualQ"[0, "integerOfNatural"[k]],
				"arrayOfList"["listConstant"[c, "integerNormalPair"["integerOfNatural"[k]][[1]]]],
				Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 1] | Failure]] == Typed["left"["subtype"["listConstant"[c, k], h]], "PackedArray"[A, 1] | Failure]],
			"Rewrite"["integerLessEqualQOfNatural"[0, k, "lessEqualZero"[k]]], "Rewrite"["integerNormalPairOfNatural"[k]],
			"Exact"["arrayOfListInRange"[A, "listConstant"[c, k], h]],
			"Exact"["existsIntroduction"["subtype"["listConstant"[c, k], h], "andIntroduction"[hc, "equalityReflexivity"["listConstant"[c, k]]]]]}
	],
	(* where the sums on the way are in range the total does not leave, and is the sum *)
	machineTheorem["integerListTotalOfSums",
		ForAll[{Typed[l, {"Integer64"}], Typed[s, "Integer64"]}, Implies["partialSumsInRange"[l][s[["integer"]]],
			Exists[{Typed[r, "Integer64"]}, "integerListTotal"[l][s] == Typed["left"[r], "Integer64" | Failure] && r[["integer"]] == s[["integer"]] + "integerListSum"[l]]]],
		{"Introduce"[l], "Induction"[l],
			"Introduce"[s, h],
			"Exact"["existsIntroduction"[s, "andIntroduction"["equalityReflexivity"[Typed["left"[s], "Integer64" | Failure]], "equalitySymmetry"["integerAdditionZero"[s[["integer"]]]]]]],
			"Introduce"[x, tail, ih, s],
			"Change"[Implies["integer64Range"[s[["integer"]] + x[["integer"]]] && "partialSumsInRange"[tail][s[["integer"]] + x[["integer"]]],
				Exists[{Typed[r, "Integer64"]}, "confirmBind"["machineResult"[s[["integer"]] + x[["integer"]]], "integerListTotal"[tail]] == Typed["left"[r], "Integer64" | Failure] &&
					r[["integer"]] == s[["integer"]] + (x[["integer"]] + "integerListSum"[tail])]]],
			"Introduce"[h],
			"Rewrite"["machineResultInRange"[s[["integer"]] + x[["integer"]], h[["left"]]]],
			"Cases"[ih["subtype"[s[["integer"]] + x[["integer"]], h[["left"]]], h[["right"]]]],
			"Introduce"[r, hr],
			"Exact"["existsIntroduction"[r, "andIntroduction"[hr[["left"]],
				"equalityTransitivity"[hr[["right"]], "integerAdditionAssociativity"[s[["integer"]], x[["integer"]], "integerListSum"[tail]]]]]]}
	],

	(* the transpose of rows: as long as the columns, each column as long as the rows are many, and twice the rows. A row
	   put before columns as long as it is transposes to the row before the transpose of the columns *)
	machineTheorem["prependColumnsLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[row, {A}], Typed[columns, {{A}}]}, Length["prependColumns"[row][columns]] == Length[columns]],
		{"Introduce"[A, row], "Induction"[row],
			"Introduce"[columns], "Reflexivity",
			"Introduce"[x, xs, ih, columns], "Cases"[columns],
			"Reflexivity",
			"Introduce"[column, rest], "Exact"["equalityCongruence"["successor", ih[rest]]]}
	],
	machineTheorem["transposeRowsLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[columns, NonNegativeIntegers], Typed[rows, {{A}}]}, Length["transposeRows"[columns, rows]] == columns],
		{"Introduce"[A, columns, rows], "Induction"[rows],
			"Exact"["listConstantLength"[{A}, Typed[{}, {A}], columns]],
			"Introduce"[row, rest, ih], "Exact"["equalityTransitivity"["prependColumnsLength"[A, row, "transposeRows"[columns, rest]], ih]]}
	],
	machineTheorem["prependColumnsOfLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers], Typed[row, {A}], Typed[columns, {{A}}]},
			Implies[Length[row] == Length[columns], Implies["rowsOfLength"[columns, n], "rowsOfLength"["prependColumns"[row][columns], n + 1]]]],
		{"Introduce"[A, n, row], "Induction"[row],
			"Introduce"[columns], "Cases"[columns],
			"Introduce"[hl, hc], "Exact"["trueIntroduction"],
			"Introduce"[column, rest, hl, hc], "Exact"["falseElimination"["successorNotZero"[Length[rest]]["equalitySymmetry"[hl]]]],
			"Introduce"[x, xs, ih, columns], "Cases"[columns],
			"Introduce"[hl, hc], "Exact"["falseElimination"["successorNotZero"[Length[xs]][hl]]],
			"Introduce"[column, rest, hl, hc],
			"Exact"["andIntroduction"["equalityCongruence"["successor", hc[["left"]]], ih[rest, "successorInjectivity"[hl], hc[["right"]]]]]}
	],
	machineTheorem["constantRowsOfLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, NonNegativeIntegers]}, "rowsOfLength"["listConstant"[Typed[{}, {A}], c], 0]],
		{"Introduce"[A, c], "Induction"[c],
			"Exact"["trueIntroduction"],
			"Introduce"[k, ih], "Exact"["andIntroduction"["equalityReflexivity"[0], ih]]}
	],
	machineTheorem["transposeRowsOfLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[columns, NonNegativeIntegers], Typed[rows, {{A}}]},
			Implies["rowsOfLength"[rows, columns], "rowsOfLength"["transposeRows"[columns, rows], Length[rows]]]],
		{"Introduce"[A, columns, rows], "Induction"[rows],
			"Introduce"[h], "Exact"["constantRowsOfLength"[A, columns]],
			"Introduce"[row, rest, ih, h],
			"Exact"["prependColumnsOfLength"[A, Length[rest], row, "transposeRows"[columns, rest],
				"equalityTransitivity"[h[["left"]], "equalitySymmetry"["transposeRowsLength"[A, columns, rest]]], ih[h[["right"]]]]]}
	],
	machineTheorem["transposeOfPrependColumns",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers], Typed[row, {A}], Typed[columns, {{A}}]},
			Implies[Length[row] == Length[columns], "transposeRows"[n + 1, "prependColumns"[row][columns]] == Prepend[row]["transposeRows"[n, columns]]]],
		{"Introduce"[A, n, row], "Induction"[row],
			"Introduce"[columns], "Cases"[columns],
			"Introduce"[hl], "Reflexivity",
			"Introduce"[column, rest, hl], "Exact"["falseElimination"["successorNotZero"[Length[rest]]["equalitySymmetry"[hl]]]],
			"Introduce"[x, xs, ih, columns], "Cases"[columns],
			"Introduce"[hl], "Exact"["falseElimination"["successorNotZero"[Length[xs]][hl]]],
			"Introduce"[column, rest, hl],
			"Exact"["equalityCongruence"[Function[{Typed[t, {{A}}]}, "prependColumns"[Prepend[x][column]][t]], ih[rest, "successorInjectivity"[hl]]]]}
	],
	machineTheorem["transposeOfConstantRows",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, NonNegativeIntegers]}, "transposeRows"[0, "listConstant"[Typed[{}, {A}], c]] == Typed[{}, {{A}}]],
		{"Introduce"[A, c], "Induction"[c], "Reflexivity", "Introduce"[k, ih], "Exact"[ih]}
	],
	machineTheorem["transposeRowsTwice",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[columns, NonNegativeIntegers], Typed[rows, {{A}}]},
			Implies["rowsOfLength"[rows, columns], "transposeRows"[Length[rows], "transposeRows"[columns, rows]] == rows]],
		{"Introduce"[A, columns, rows], "Induction"[rows],
			"Introduce"[h], "Exact"["transposeOfConstantRows"[A, columns]],
			"Introduce"[row, rest, ih, h],
			"Exact"["equalityTransitivity"[
				"transposeOfPrependColumns"[A, Length[rest], row, "transposeRows"[columns, rest], "equalityTransitivity"[h[["left"]], "equalitySymmetry"["transposeRowsLength"[A, columns, rest]]]],
				"equalityCongruence"[Function[{Typed[t, {{A}}]}, Prepend[row][t]], ih[h[["right"]]]]]]}
	],
	(* two matrices are one where their columns and rows are: any two proofs of the range are one *)
	machineTheorem["matrixEquality",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[r, {{A}}], Typed[s, {{A}}], Typed[p, "matrixRange"[c, r]], Typed[q, "matrixRange"[d, s]]},
			Implies[c == d, Implies[r == s, "matrix"[c, r, p] == "matrix"[d, s, q]]]],
		{"Introduce"[A, c, d, r, s, p, q, e, f], "Generalize"[q], "Rewrite"[e, "RightToLeft"], "Rewrite"[f, "RightToLeft"], "Introduce"[q], "Reflexivity"}
	],
	(* the transpose of a matrix is one: its rows are the columns, as long as the rows were many *)
	machineTheorem["matrixTransposeRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]}, "matrixRange"[Length[m[["rows"]]], "transposeRows"[m[["columns"]], m[["rows"]]]]],
		{"Introduce"[A, m],
			"Have"[h, "matrixRange"[m[["columns"]], m[["rows"]]]], "Exact"[m[["proof"]]],
			"Change"[Length[m[["rows"]]] < upper && Length["transposeRows"[m[["columns"]], m[["rows"]]]] < upper &&
				Length["transposeRows"[m[["columns"]], m[["rows"]]]] Length[m[["rows"]]] < upper && "rowsOfLength"["transposeRows"[m[["columns"]], m[["rows"]]], Length[m[["rows"]]]]],
			"Rewrite"["transposeRowsLength"[A, m[["columns"]], m[["rows"]]]],
			"Exact"["andIntroduction"[h[["right"]][["left"]], "andIntroduction"[h[["left"]], "andIntroduction"[
				"equalitySubstitution"["multiplicationCommutativity"[Length[m[["rows"]]], m[["columns"]]], h[["right"]][["right"]][["left"]], P -> Function[{Typed[k, NonNegativeIntegers]}, k < upper]],
				"transposeRowsOfLength"[A, m[["columns"]], m[["rows"]], h[["right"]][["right"]][["right"]]]]]]]}
	],
	TypeTheoryDefinition["matrixTranspose", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]},
			"matrix"[Length[m[["rows"]]], "transposeRows"[m[["columns"]], m[["rows"]]], "matrixTransposeRange"[A, m]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 2] -> "PackedArray"[A, 2]]
	]],
	(* Transpose twice is the identity on every matrix, and the dimensions of a transpose are the dimensions reversed *)
	machineTheorem["matrixTransposeTwice",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]}, "matrixTranspose"["matrixTranspose"[m]] == m],
		{"Introduce"[A, m], "Cases"[m], "Introduce"[c, rows, p],
			"Exact"["matrixEquality"[A, Length["transposeRows"[c, rows]], c, "transposeRows"[Length[rows], "transposeRows"[c, rows]], rows,
				"matrixTransposeRange"[A, "matrixTranspose"["matrix"[c, rows, p]]], p,
				"transposeRowsLength"[A, c, rows], "transposeRowsTwice"[A, c, rows, p[["right"]][["right"]][["right"]]]]]}
	],
	machineTheorem["matrixDimensionsOfTranspose",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]}, "matrixDimensions"["matrixTranspose"[m]] == Reverse["matrixDimensions"[m]]],
		{"Introduce"[A, m],
			"Exact"["equalityCongruence"[Function[{Typed[k, NonNegativeIntegers]}, Typed[{k, Length[m[["rows"]]]}, {NonNegativeIntegers}]],
				"transposeRowsLength"[A, m[["columns"]], m[["rows"]]]]]}
	],
	(* every rank: Dimensions, the list of the dimensions, {} for an element, {length} for a vector, {rows, columns} for
	   a matrix, and the rows, the columns and the levels below for a rank above; a rank of n + 2 has a Transpose, the
	   first two levels swapped, the matrix transpose at rank 2 and of the outer matrix above *)
	TypeTheoryDefinition["arrayDimensions", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, "PackedArray"[A, k] -> {NonNegativeIntegers}],
			Function[{Typed[x, A]}, Typed[{}, {NonNegativeIntegers}]],
			Function[{Typed[k, NonNegativeIntegers], Typed[r, "PackedArray"[A, k] -> {NonNegativeIntegers}]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[j, NonNegativeIntegers]}, "PackedArray"[A, j + 1] -> {NonNegativeIntegers}],
				Function[{Typed[a, "PackedArray"[A, 1]]}, Typed[{Length[a[["list"]]]}, {NonNegativeIntegers}]],
				Function[{Typed[j, NonNegativeIntegers], Typed[s, "PackedArray"[A, j + 1] -> {NonNegativeIntegers}]}, InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[i, NonNegativeIntegers]}, "PackedArray"[A, i + 2] -> {NonNegativeIntegers}],
					Function[{Typed[m, "PackedArray"[A, 2]]}, "matrixDimensions"[m]],
					Function[{Typed[i, NonNegativeIntegers], Typed[q, "PackedArray"[A, i + 2] -> {NonNegativeIntegers}]},
						Function[{Typed[t, "Tensor"[A, i]]}, Join["matrixDimensions"[t[["values"]]], t[["inner"]]]]],
					j
				]],
				k
			]],
			n
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[n, NonNegativeIntegers]}, "PackedArray"[A, n] -> {NonNegativeIntegers}]
	]],
	(* the transpose of an array of rank k + 3 is one: the outer matrix transposed has as many elements *)
	machineTheorem["tensorTransposeRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[k, NonNegativeIntegers], Typed[t, "Tensor"[A, k]]},
			Length[t[["inner"]]] == k + 1 && "shapeElements"[t[["inner"]]] (Length["matrixTranspose"[t[["values"]]][["rows"]]] "matrixTranspose"[t[["values"]]][["columns"]]) < upper],
		{"Introduce"[A, k, t], "Cases"[t], "Introduce"[inner, values, p], "Cases"[values], "Introduce"[c, rows, q, p],
			"Change"[Length[inner] == k + 1 && "shapeElements"[inner] (Length["transposeRows"[c, rows]] Length[rows]) < upper],
			"Rewrite"["transposeRowsLength"["Nested"[A, inner], c, rows]],
			"Exact"["andIntroduction"[p[["left"]],
				"equalitySubstitution"["multiplicationCommutativity"[Length[rows], c], p[["right"]], P -> Function[{Typed[z, NonNegativeIntegers]}, "shapeElements"[inner] z < upper]]]]}
	],
	TypeTheoryDefinition["arrayTranspose", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, "PackedArray"[A, k + 2] -> "PackedArray"[A, k + 2]],
			Function[{Typed[m, "PackedArray"[A, 2]]}, "matrixTranspose"[m]],
			Function[{Typed[k, NonNegativeIntegers], Typed[r, "PackedArray"[A, k + 2] -> "PackedArray"[A, k + 2]]},
				Function[{Typed[t, "Tensor"[A, k]]}, Typed["tensor"[t[["inner"]], "matrixTranspose"[t[["values"]]], "tensorTransposeRange"[A, k, t]], "Tensor"[A, k]]]],
			n
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[n, NonNegativeIntegers]}, "PackedArray"[A, n + 2] -> "PackedArray"[A, n + 2]]
	]],
	(* the dimensions with the first two swapped, as Transpose swaps the first two levels *)
	TypeTheoryDefinition["dimensionsTransposed", Typed[
		Function[{Typed[d, {NonNegativeIntegers}]}, InductiveRecursor[List][
			Function[{Typed[t, {NonNegativeIntegers}]}, {NonNegativeIntegers}],
			Typed[{}, {NonNegativeIntegers}],
			Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[r, {NonNegativeIntegers}]}, InductiveRecursor[List][
				Function[{Typed[t, {NonNegativeIntegers}]}, {NonNegativeIntegers}],
				Prepend[x][Typed[{}, {NonNegativeIntegers}]],
				Function[{Typed[y, NonNegativeIntegers], Typed[others, {NonNegativeIntegers}], Typed[s, {NonNegativeIntegers}]}, Prepend[y][Prepend[x][others]]],
				rest
			]],
			d
		]],
		{NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	(* two arrays of rank k + 3 are one where their dimensions below and their outer matrices are *)
	machineTheorem["tensorEquality",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[k, NonNegativeIntegers], Typed[inner, {NonNegativeIntegers}], Typed[v, "Matrix"["Nested"[A, inner]]], Typed[w, "Matrix"["Nested"[A, inner]]],
				Typed[p, Length[inner] == k + 1 && "shapeElements"[inner] (Length[v[["rows"]]] v[["columns"]]) < upper],
				Typed[q, Length[inner] == k + 1 && "shapeElements"[inner] (Length[w[["rows"]]] w[["columns"]]) < upper]},
			Implies[v == w, Typed["tensor"[inner, v, p], "Tensor"[A, k]] == Typed["tensor"[inner, w, q], "Tensor"[A, k]]]],
		{"Introduce"[A, k, inner, v, w, p, q, e], "Generalize"[q], "Rewrite"[e, "RightToLeft"], "Introduce"[q], "Reflexivity"}
	],
	(* the theorems of every rank: as many dimensions as the rank, Transpose twice the identity, and the dimensions of a
	   transpose the first two swapped *)
	machineTheorem["arrayDimensionsLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers]}, ForAll[{Typed[a, "PackedArray"[A, n]]}, Length["arrayDimensions"[a]] == n]],
		{"Introduce"[A, n], "Cases"[n],
			"Introduce"[x], "Reflexivity",
			"Introduce"[k], "Cases"[k],
			"Introduce"[a], "Reflexivity",
			"Introduce"[j], "Cases"[j],
			"Introduce"[m], "Reflexivity",
			"Introduce"[i, t],
			"Change"[Length[Join["matrixDimensions"[t[["values"]]], t[["inner"]]]] == i + 3],
			"Rewrite"["lengthJoin"["matrixDimensions"[t[["values"]]], t[["inner"]]]],
			"Rewrite"[t[["proof"]][["left"]]],
			"Change"[2 + (i + 1) == i + 3],
			"LinearArithmetic"}
	],
	machineTheorem["arrayTransposeTwice",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers]}, ForAll[{Typed[a, "PackedArray"[A, n + 2]]}, "arrayTranspose"["arrayTranspose"[a]] == a]],
		{"Introduce"[A, n], "Cases"[n],
			"Introduce"[m], "Exact"["matrixTransposeTwice"[A, m]],
			"Introduce"[k, t], "Cases"[t], "Introduce"[inner, values, p],
			"Exact"["tensorEquality"[A, k, inner, "matrixTranspose"["matrixTranspose"[values]], values,
				"tensorTransposeRange"[A, k, "tensor"[inner, "matrixTranspose"[values], "tensorTransposeRange"[A, k, "tensor"[inner, values, p]]]], p,
				"matrixTransposeTwice"["Nested"[A, inner], values]]]}
	],
	machineTheorem["arrayDimensionsOfTranspose",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers]}, ForAll[{Typed[a, "PackedArray"[A, n + 2]]},
			"arrayDimensions"["arrayTranspose"[a]] == "dimensionsTransposed"["arrayDimensions"[a]]]],
		{"Introduce"[A, n], "Cases"[n],
			"Introduce"[m], "Exact"["matrixDimensionsOfTranspose"[A, m]],
			"Introduce"[k, t],
			"Exact"["equalityCongruence"[Function[{Typed[z, NonNegativeIntegers]}, Prepend[z][Prepend[Length[t[["values"]][["rows"]]]][t[["inner"]]]]],
				"transposeRowsLength"["Nested"[A, t[["inner"]]], t[["values"]][["columns"]], t[["values"]][["rows"]]]]]}
	],

	(* the first n elements are n where the list has them, and the rest is as long as what is left *)
	machineTheorem["listFirstLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[n, NonNegativeIntegers]}, Implies[n <= Length[l], Length["listFirst"[l, n]] == n]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[n], "Cases"[n],
			"Introduce"[h], "Reflexivity",
			"Introduce"[k, h], "Exact"["falseElimination"["successorNotLessEqualZero"[k][h]]],
			"Introduce"[x, rest, ih, n], "Cases"[n],
			"Introduce"[h], "Reflexivity",
			"Introduce"[k, h], "Exact"["equalityCongruence"["successor", ih[k, "lessEqualPredecessor"[h]]]]}
	],
	machineTheorem["dropLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[n, NonNegativeIntegers]}, Implies[n <= Length[l], Length[Drop[l, n]] + n == Length[l]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[n], "Cases"[n],
			"Introduce"[h], "Reflexivity",
			"Introduce"[k, h], "Exact"["falseElimination"["successorNotLessEqualZero"[k][h]]],
			"Introduce"[x, rest, ih, n], "Cases"[n],
			"Introduce"[h], "Reflexivity",
			"Introduce"[k, h],
			"Exact"["equalityTransitivity"["additionSuccessorRight"[Length[Drop[rest, k]], k], "equalityCongruence"["successor", ih[k, "lessEqualPredecessor"[h]]]]]}
	],
	(* the rows of a partition: no more than its rounds, no more elements than the list has, and each n long *)
	machineTheorem["partitionRowsCount",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[l, {A}]}, Length["partitionRows"[n, fuel][l]] <= fuel],
		{"Introduce"[A, n, fuel], "Induction"[fuel],
			"Introduce"[l], "Exact"["lessEqualZero"[0]],
			"Introduce"[k, ih, l],
			"Change"[Length["machineIf"["lessEqual"[n, Length[l]], Prepend["listFirst"[l, n]]["partitionRows"[n, k][Drop[l, n]]], Typed[{}, {{A}}]]] <= k + 1],
			"Cases"["lessEqual"[n, Length[l]]],
			"Exact"["lessEqualZero"[k + 1]],
			"Exact"["lessEqualSuccessor"[ih[Drop[l, n]]]]}
	],
	machineTheorem["partitionRowsBound",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[l, {A}]}, Length["partitionRows"[n, fuel][l]] n <= Length[l]],
		{"Introduce"[A, n, fuel], "Induction"[fuel],
			"Introduce"[l], "Change"[0 n <= Length[l]], "Rewrite"["multiplicationZeroLeft"[n]], "Exact"["lessEqualZero"[Length[l]]],
			"Introduce"[k, ih, l],
			"Change"[Length["machineIf"["lessEqual"[n, Length[l]], Prepend["listFirst"[l, n]]["partitionRows"[n, k][Drop[l, n]]], Typed[{}, {{A}}]]] n <= Length[l]],
			"Have"[hc, Implies["lessEqual"[n, Length[l]] == "true", n <= Length[l]]], "Exact"["lessEqualTrue"[n, Length[l]]],
			"Generalize"[hc], "Cases"["lessEqual"[n, Length[l]]],
			"Introduce"[hc], "Change"[0 n <= Length[l]], "Rewrite"["multiplicationZeroLeft"[n]], "Exact"["lessEqualZero"[Length[l]]],
			"Introduce"[hc],
			"Have"[hn, n <= Length[l]], "Exact"[hc["equalityReflexivity"["true"]]],
			"Have"[hb, Length["partitionRows"[n, k][Drop[l, n]]] n <= Length[Drop[l, n]]], "Exact"[ih[Drop[l, n]]],
			"Have"[hd, Length[Drop[l, n]] + n == Length[l]], "Exact"["dropLength"[A, l, n, hn]],
			"Change"[(Length["partitionRows"[n, k][Drop[l, n]]] + 1) n <= Length[l]],
			"Rewrite"["multiplicationSuccessorLeft"[Length["partitionRows"[n, k][Drop[l, n]]], n]],
			"Rewrite"[hd, "RightToLeft"],
			"Exact"["additionMonotonicity"[hb, "lessEqualReflexivity"]]}
	],
	machineTheorem["partitionRowsOfLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[l, {A}]}, "rowsOfLength"["partitionRows"[n, fuel][l], n]],
		{"Introduce"[A, n, fuel], "Induction"[fuel],
			"Introduce"[l], "Exact"["trueIntroduction"],
			"Introduce"[k, ih, l],
			"Change"["rowsOfLength"["machineIf"["lessEqual"[n, Length[l]], Prepend["listFirst"[l, n]]["partitionRows"[n, k][Drop[l, n]]], Typed[{}, {{A}}]], n]],
			"Have"[hc, Implies["lessEqual"[n, Length[l]] == "true", n <= Length[l]]], "Exact"["lessEqualTrue"[n, Length[l]]],
			"Generalize"[hc], "Cases"["lessEqual"[n, Length[l]]],
			"Introduce"[hc], "Exact"["trueIntroduction"],
			"Introduce"[hc], "Exact"["andIntroduction"["listFirstLength"[A, l, n, hc["equalityReflexivity"["true"]]], ih[Drop[l, n]]]]}
	],
	(* the partition of a vector into rows of n, a count a machine holds, is a matrix *)
	machineTheorem["partitionRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, NonNegativeIntegers]}, Implies[n < upper, "matrixRange"[n, "listPartition"[a[["list"]], n]]]],
		{"Introduce"[A, a, n, hn],
			"Have"[held, Length[a[["list"]]] < upper], "Exact"[a[["proof"]]],
			"Have"[count, Length["listPartition"[a[["list"]], n]] <= Length[a[["list"]]]], "Exact"["partitionRowsCount"[A, n, Length[a[["list"]]], a[["list"]]]],
			"Have"[bound, Length["listPartition"[a[["list"]], n]] n <= Length[a[["list"]]]], "Exact"["partitionRowsBound"[A, n, Length[a[["list"]]], a[["list"]]]],
			"Exact"["andIntroduction"[hn, "andIntroduction"["lessEqualTransitivity"["lessEqualSuccessor"[count], held],
				"andIntroduction"["lessEqualTransitivity"["lessEqualSuccessor"[bound], held], "partitionRowsOfLength"[A, n, Length[a[["list"]]], a[["list"]]]]]]]}
	],
	(* the matrix of the rows of n of a vector; a count no machine holds is the leave of an allocation that fails, which
	   typed code, whose counts are machine integers, never reaches *)
	TypeTheoryDefinition["partitionMatrix", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, NonNegativeIntegers]}, InductiveRecursor[Decidable][
			Typed[d, Decidable[n < upper]] |-> "PackedArray"[A, 2] | Failure,
			Typed[h, Not[n < upper]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 2] | Failure],
			Typed[h, n < upper] |-> Typed["left"["matrix"[n, "listPartition"[a[["list"]], n], "partitionRange"[A, a, n, h]]], "PackedArray"[A, 2] | Failure],
			"machineDecision"[n < upper]
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> NonNegativeIntegers -> ("PackedArray"[A, 2] | Failure)]
	]],
	(* Partition[a, k]: k columns, as many rows of k as the vector has, a shorter tail dropped; k below 1 is the
	   compiler's leave Failure["Range", <||>] *)
	TypeTheoryDefinition["matrixOfPartition", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[k, Integers]},
			"machineIf"["integerLessEqualQ"[1, k], "partitionMatrix"[a, "integerNormalPair"[k][[1]]], Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 2] | Failure]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> Integers -> ("PackedArray"[A, 2] | Failure)]
	]],
	TypeTheoryTheorem["partitionMatrixInRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, NonNegativeIntegers], Typed[h, n < upper]},
			"partitionMatrix"[a, n] == Typed["left"["matrix"[n, "listPartition"[a[["list"]], n], "partitionRange"[A, a, n, h]]], "PackedArray"[A, 2] | Failure]],
		Function[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, NonNegativeIntegers], Typed[h, n < upper]}, InductiveRecursor[Decidable][
			Typed[d, Decidable[n < upper]] |-> InductiveRecursor[Decidable][
				Typed[e, Decidable[n < upper]] |-> "PackedArray"[A, 2] | Failure,
				Typed[k, Not[n < upper]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 2] | Failure],
				Typed[k, n < upper] |-> Typed["left"["matrix"[n, "listPartition"[a[["list"]], n], "partitionRange"[A, a, n, k]]], "PackedArray"[A, 2] | Failure],
				d
			] == Typed["left"["matrix"[n, "listPartition"[a[["list"]], n], "partitionRange"[A, a, n, h]]], "PackedArray"[A, 2] | Failure],
			Typed[k, Not[n < upper]] |-> "falseElimination"[k[h]],
			Typed[k, n < upper] |-> "equalityReflexivity"[Typed["left"["matrix"[n, "listPartition"[a[["list"]], n], "partitionRange"[A, a, n, h]]], "PackedArray"[A, 2] | Failure]],
			"machineDecision"[n < upper]
		]]
	],
	(* Partition by a count a machine integer holds, 1 or more, is the matrix of its rows; by a count below 1 it leaves *)
	machineTheorem["matrixOfPartitionOfNatural",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, NonNegativeIntegers], Typed[h, n < upper]}, Implies[1 <= n,
			"matrixOfPartition"[a, "integerOfNatural"[n]] == Typed["left"["matrix"[n, "listPartition"[a[["list"]], n], "partitionRange"[A, a, n, h]]], "PackedArray"[A, 2] | Failure]]],
		{"Introduce"[A, a, n, h, positive],
			"Change"["machineIf"["integerLessEqualQ"[1, "integerOfNatural"[n]], "partitionMatrix"[a, "integerNormalPair"["integerOfNatural"[n]][[1]]], Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 2] | Failure]] ==
				Typed["left"["matrix"[n, "listPartition"[a[["list"]], n], "partitionRange"[A, a, n, h]]], "PackedArray"[A, 2] | Failure]],
			"Rewrite"["integerLessEqualQOfNatural"[1, n, positive]], "Rewrite"["integerNormalPairOfNatural"[n]],
			"Exact"["partitionMatrixInRange"[A, a, n, h]]}
	],
	machineTheorem["matrixOfPartitionRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[k, Integers]},
			Implies["integerLessEqualQ"[1, k] == "false", "matrixOfPartition"[a, k] == Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 2] | Failure]]],
		{"Introduce"[A, a, k, h],
			"Change"["machineIf"["integerLessEqualQ"[1, k], "partitionMatrix"[a, "integerNormalPair"[k][[1]]], Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 2] | Failure]] == Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 2] | Failure]],
			"Rewrite"[h], "Reflexivity"}
	],
	(* a part leaves by a place that is not there alone; a part of rows each c long is c long *)
	machineTheorem["listPartLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[j, Integers], Typed[f, Failure]}, Implies["listPart"[l][j] == Typed["right"[f], A | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[j, f, h], "Exact"["equalitySymmetry"["rightInjective"[A, Failure, Failure["PartRange", <||>], f, h]]],
			"Introduce"[x, rest, ih, j, f],
			"Change"[Implies["machineIf"["integerEqual"[j, 0], Typed["left"[x], A | Failure], "listPart"[rest][j - 1]] == Typed["right"[f], A | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[j, 0]],
			"Introduce"[h], "Exact"[ih[j - 1, f, h]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[A, Failure, x, f, h]]]}
	],
	machineTheorem["listPartOfIndexLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[i, Integers], Typed[f, Failure]}, Implies["listPartOfIndex"[l, i] == Typed["right"[f], A | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, l, i, f],
			"Change"[Implies["machineIf"["integerLessEqualQ"[1, i], "listPart"[l][i - 1], "listPart"[l]["integerOfNatural"[Length[l]] + i]] == Typed["right"[f], A | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerLessEqualQ"[1, i]],
			"Introduce"[h], "Exact"["listPartLeave"[A, l, "integerOfNatural"[Length[l]] + i, f, h]],
			"Introduce"[h], "Exact"["listPartLeave"[A, l, i - 1, f, h]]}
	],
	machineTheorem["rowsOfLengthPart",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, NonNegativeIntegers], Typed[rows, {{A}}], Typed[j, Integers], Typed[row, {A}]},
			Implies["rowsOfLength"[rows, c], Implies["listPart"[rows][j] == Typed["left"[row], {A} | Failure], Length[row] == c]]],
		{"Introduce"[A, c, rows], "Induction"[rows],
			"Introduce"[j, row, hr, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, row, Failure["PartRange", <||>], h]]],
			"Introduce"[x, rest, ih, j, row, hr],
			"Change"[Implies["machineIf"["integerEqual"[j, 0], Typed["left"[x], {A} | Failure], "listPart"[rest][j - 1]] == Typed["left"[row], {A} | Failure], Length[row] == c]],
			"Cases"["integerEqual"[j, 0]],
			"Introduce"[h], "Exact"[ih[j - 1, row, hr[["right"]], h]],
			"Introduce"[h], "Rewrite"["leftInjective"[{A}, Failure, x, row, h], "RightToLeft"], "Exact"[hr[["left"]]]}
	],
	machineTheorem["rowsOfLengthPartOfIndex",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, NonNegativeIntegers], Typed[rows, {{A}}], Typed[i, Integers], Typed[row, {A}]},
			Implies["rowsOfLength"[rows, c], Implies["listPartOfIndex"[rows, i] == Typed["left"[row], {A} | Failure], Length[row] == c]]],
		{"Introduce"[A, c, rows, i, row, hr],
			"Change"[Implies["machineIf"["integerLessEqualQ"[1, i], "listPart"[rows][i - 1], "listPart"[rows]["integerOfNatural"[Length[rows]] + i]] == Typed["left"[row], {A} | Failure], Length[row] == c]],
			"Cases"["integerLessEqualQ"[1, i]],
			"Introduce"[h], "Exact"["rowsOfLengthPart"[A, c, rows, "integerOfNatural"[Length[rows]] + i, row, hr, h]],
			"Introduce"[h], "Exact"["rowsOfLengthPart"[A, c, rows, i - 1, row, hr, h]]}
	],
	(* a row and an element of a matrix leave by a part that is not there alone: a row is a vector a machine holds,
	   never the leave of an allocation that fails *)
	machineTheorem["matrixRowLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]], Typed[i, Integers], Typed[f, Failure]},
			Implies["matrixRow"[m, i] == Typed["right"[f], "PackedArray"[A, 1] | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, m, i, f],
			"Have"[hv, ForAll[{Typed[row, {A}]}, Implies["listPartOfIndex"[m[["rows"]], i] == Typed["left"[row], {A} | Failure], Length[row] == m[["columns"]]]]],
			"Exact"[Function[{Typed[row, {A}]}, "rowsOfLengthPartOfIndex"[A, m[["columns"]], m[["rows"]], i, row, m[["proof"]][["right"]][["right"]][["right"]]]]],
			"Have"[hl, ForAll[{Typed[g, Failure]}, Implies["listPartOfIndex"[m[["rows"]], i] == Typed["right"[g], {A} | Failure], g == Failure["PartRange", <||>]]]],
			"Exact"["listPartOfIndexLeave"[{A}, m[["rows"]], i]],
			"Have"[held, m[["columns"]] < upper], "Exact"[m[["proof"]][["left"]]],
			"Change"[Implies["confirmBind"["listPartOfIndex"[m[["rows"]], i], Function[{Typed[row, {A}]}, "arrayOfList"[row]]] == Typed["right"[f], "PackedArray"[A, 1] | Failure], f == Failure["PartRange", <||>]]],
			"Generalize"[hv], "Generalize"[hl], "Cases"["listPartOfIndex"[m[["rows"]], i]],
			"Introduce"[row, hl, hv, h],
			"Have"[hr, "arrayLengthRange"[A][row]], "Change"[Length[row] < upper], "Rewrite"[hv[row, "equalityReflexivity"[Typed["left"[row], {A} | Failure]]]], "Exact"[held],
			"Have"[h2, "arrayOfList"[row] == Typed["right"[f], "PackedArray"[A, 1] | Failure]], "Exact"[h],
			"Rewrite"["arrayOfListInRange"[A, row, hr], "At" -> h2],
			"Exact"["falseElimination"["leftNotRight"["PackedArray"[A, 1], Failure, "subtype"[row, hr], f, h2]]],
			"Introduce"[g, hl, hv, h],
			"Have"[h3, Typed["right"[g], "PackedArray"[A, 1] | Failure] == Typed["right"[f], "PackedArray"[A, 1] | Failure]], "Exact"[h],
			"Rewrite"["rightInjective"["PackedArray"[A, 1], Failure, g, f, h3], "RightToLeft"],
			"Exact"[hl[g, "equalityReflexivity"[Typed["right"[g], {A} | Failure]]]]}
	],
	machineTheorem["matrixPartLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]], Typed[i, Integers], Typed[j, Integers], Typed[f, Failure]},
			Implies["matrixPart"[m, i, j] == Typed["right"[f], A | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, m, i, j, f],
			"Have"[hl, ForAll[{Typed[g, Failure]}, Implies["listPartOfIndex"[m[["rows"]], i] == Typed["right"[g], {A} | Failure], g == Failure["PartRange", <||>]]]],
			"Exact"["listPartOfIndexLeave"[{A}, m[["rows"]], i]],
			"Change"[Implies["confirmBind"["listPartOfIndex"[m[["rows"]], i], Function[{Typed[row, {A}]}, "listPartOfIndex"[row, j]]] == Typed["right"[f], A | Failure], f == Failure["PartRange", <||>]]],
			"Generalize"[hl], "Cases"["listPartOfIndex"[m[["rows"]], i]],
			"Introduce"[row, hl, h], "Exact"["listPartOfIndexLeave"[A, row, j, f, h]],
			"Introduce"[g, hl, h],
			"Have"[h3, Typed["right"[g], A | Failure] == Typed["right"[f], A | Failure]], "Exact"[h],
			"Rewrite"["rightInjective"[A, Failure, g, f, h3], "RightToLeft"],
			"Exact"[hl[g, "equalityReflexivity"[Typed["right"[g], {A} | Failure]]]]}
	],
	(* Length of a matrix is the integer of the count of its rows, and the product has as many integers *)
	machineTheorem["matrixLengthInteger",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]}, "matrixLength"[m][["integer"]] == "integerOfNatural"[Length[m[["rows"]]]]],
		{"Introduce"[A, m], "Reflexivity"}
	],
	machineTheorem["matrixVectorProductLength",
		ForAll[{Typed[m, "PackedArray"["Integer64", 2]], Typed[v, "PackedArray"["Integer64", 1]]}, Length["matrixVectorProduct"[m, v]] == Length[m[["rows"]]]],
		{"Introduce"[m, v], "Exact"["lengthMap"[Function[{Typed[row, {"Integer64"}]}, "integerListDot"[row][v[["list"]]]], m[["rows"]]]]}
	],

	(* what a proof about a loop over a matrix and a vector rests on: the machine's dot product of two lists, each
	   product and sum leaving where it does, as s = s + m[[i, j]] v[[j]] computes it, and the exact one where every
	   one is in range; the rows' dot products in turn; an element of a matrix split at a place; and binds taken apart,
	   a pair's first part through a continuation that reads it alone included *)
	TypeTheoryDefinition["integerListDotTotal", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, {"Integer64"} -> "Integer64" -> ("Integer64" | Failure)],
			Function[{Typed[w, {"Integer64"}], Typed[s, "Integer64"]}, Typed["left"[s], "Integer64" | Failure]],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, {"Integer64"} -> "Integer64" -> ("Integer64" | Failure)]}, Function[{Typed[w, {"Integer64"}], Typed[s, "Integer64"]},
				InductiveRecursor[List][
					Function[{Typed[t, {"Integer64"}]}, "Integer64" | Failure],
					Typed["left"[s], "Integer64" | Failure],
					Function[{Typed[y, "Integer64"], Typed[ys, {"Integer64"}], Typed[q, "Integer64" | Failure]},
						"confirmBind"["machineTimes"[x[["integer"]], y[["integer"]]], Function[{Typed[p, "Integer64"]},
							"confirmBind"["machinePlus"[s[["integer"]], p[["integer"]]], Function[{Typed[u, "Integer64"]}, r[ys, u]]]]]
					],
					w
				]
			]],
			l
		]],
		{"Integer64"} -> {"Integer64"} -> "Integer64" -> ("Integer64" | Failure)
	]],
	TypeTheoryDefinition["dotSumsInRange", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, {"Integer64"} -> Integers -> TypeUniverse[0]],
			Function[{Typed[w, {"Integer64"}], Typed[s, Integers]}, True],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, {"Integer64"} -> Integers -> TypeUniverse[0]]}, Function[{Typed[w, {"Integer64"}], Typed[s, Integers]},
				InductiveRecursor[List][
					Function[{Typed[t, {"Integer64"}]}, TypeUniverse[0]],
					True,
					Function[{Typed[y, "Integer64"], Typed[ys, {"Integer64"}], Typed[q, TypeUniverse[0]]},
						"integer64Range"[x[["integer"]] y[["integer"]]] && "integer64Range"[s + x[["integer"]] y[["integer"]]] && r[ys, s + x[["integer"]] y[["integer"]]]
					],
					w
				]
			]],
			l
		]],
		{"Integer64"} -> {"Integer64"} -> Integers -> TypeUniverse[0]
	]],
	machineTheorem["integerListDotTotalOfSums",
	ForAll[{Typed[l, {"Integer64"}], Typed[w, {"Integer64"}], Typed[s, "Integer64"]}, Implies["dotSumsInRange"[l, w, s[["integer"]]],
		Exists[{Typed[t, "Integer64"]}, "integerListDotTotal"[l, w, s] == Typed["left"[t], "Integer64" | Failure] && t[["integer"]] == s[["integer"]] + "integerListDot"[l][w]]]],
	{"Introduce"[l], "Induction"[l],
		"Introduce"[w, s, h],
		"Exact"["existsIntroduction"[s, "andIntroduction"["equalityReflexivity"[Typed["left"[s], "Integer64" | Failure]], "equalitySymmetry"["integerAdditionZero"[s[["integer"]]]]]]],
		"Introduce"[x, tail, ih, w], "Cases"[w],
		"Introduce"[s, h],
		"Exact"["existsIntroduction"[s, "andIntroduction"["equalityReflexivity"[Typed["left"[s], "Integer64" | Failure]], "equalitySymmetry"["integerAdditionZero"[s[["integer"]]]]]]],
		"Introduce"[y, ys, s, h],
		"Change"[Exists[{Typed[t, "Integer64"]},
			"confirmBind"["machineResult"[x[["integer"]] y[["integer"]]], Function[{Typed[p, "Integer64"]},
				"confirmBind"["machineResult"[s[["integer"]] + p[["integer"]]], Function[{Typed[u, "Integer64"]}, "integerListDotTotal"[tail, ys, u]]]]] == Typed["left"[t], "Integer64" | Failure] &&
			t[["integer"]] == s[["integer"]] + (x[["integer"]] y[["integer"]] + "integerListDot"[tail][ys])]],
		"Rewrite"["machineResultInRange"[x[["integer"]] y[["integer"]], h[["left"]]]],
		"Change"[Exists[{Typed[t, "Integer64"]},
			"confirmBind"["machineResult"[s[["integer"]] + x[["integer"]] y[["integer"]]], Function[{Typed[u, "Integer64"]}, "integerListDotTotal"[tail, ys, u]]] == Typed["left"[t], "Integer64" | Failure] &&
			t[["integer"]] == s[["integer"]] + (x[["integer"]] y[["integer"]] + "integerListDot"[tail][ys])]],
		"Rewrite"["machineResultInRange"[s[["integer"]] + x[["integer"]] y[["integer"]], h[["right"]][["left"]]]],
		"Cases"[ih[ys, "subtype"[s[["integer"]] + x[["integer"]] y[["integer"]], h[["right"]][["left"]]], h[["right"]][["right"]]]],
		"Introduce"[t, ht],
		"Exact"["existsIntroduction"[t, "andIntroduction"[ht[["left"]],
			"equalityTransitivity"[ht[["right"]], "integerAdditionAssociativity"[s[["integer"]], x[["integer"]] y[["integer"]], "integerListDot"[tail][ys]]]]]]}
],
	machineTheorem["listPartOfIndexOfJoin",
	ForAll[{Typed[A, TypeUniverse[1]], Typed[pre, {A}], Typed[x, A], Typed[rest, {A}], Typed[c, NonNegativeIntegers]},
		Implies[c == Length[pre], "listPartOfIndex"[Join[pre, Prepend[x][rest]], "integerOfNatural"[c + 1]] == Typed["left"[x], A | Failure]]],
	{"Introduce"[A, pre, x, rest, c, hc], "Rewrite"[hc],
		"Have"[positive, 1 <= Length[pre] + 1], "LinearArithmetic",
		"Change"["machineIf"["integerLessEqualQ"[1, "integerOfNatural"[Length[pre] + 1]],
			"listPart"[Join[pre, Prepend[x][rest]]]["integerOfNatural"[Length[pre] + 1] - 1],
			"listPart"[Join[pre, Prepend[x][rest]]]["integerOfNatural"[Length[Join[pre, Prepend[x][rest]]]] + "integerOfNatural"[Length[pre] + 1]]] == Typed["left"[x], A | Failure]],
		"Rewrite"["integerLessEqualQOfNatural"[1, Length[pre] + 1, positive]],
		"Rewrite"["integerOfNaturalPredecessor"[Length[pre]]],
		"Exact"["listPartOfJoin"[A, x, rest, pre]]}
],
	machineTheorem["matrixPartOfJoin",
	ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]], Typed[preRows, {{A}}], Typed[row, {A}], Typed[restRows, {{A}}], Typed[pre, {A}], Typed[x, A], Typed[rest, {A}], Typed[c, NonNegativeIntegers]},
		Implies[m[["rows"]] == Join[preRows, Prepend[row][restRows]], Implies[row == Join[pre, Prepend[x][rest]], Implies[c == Length[pre],
			"matrixPart"[m, "integerOfNatural"[Length[preRows] + 1], "integerOfNatural"[c + 1]] == Typed["left"[x], A | Failure]]]]],
	{"Introduce"[A, m, preRows, row, restRows, pre, x, rest, c, e1, e2, hc],
		"Change"["confirmBind"["listPartOfIndex"[m[["rows"]], "integerOfNatural"[Length[preRows] + 1]], Function[{Typed[r, {A}]}, "listPartOfIndex"[r, "integerOfNatural"[c + 1]]]] == Typed["left"[x], A | Failure]],
		"Rewrite"[e1],
		"Rewrite"["listPartOfIndexOfJoin"[{A}, preRows, row, restRows, Length[preRows], "equalityReflexivity"[Length[preRows]]]],
		"Rewrite"[e2],
		"Exact"["listPartOfIndexOfJoin"[A, pre, x, rest, c, hc]]}
],
	TypeTheoryDefinition["rowsDotTotals", Typed[
		Function[{Typed[rows, {{"Integer64"}}], Typed[w, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {{"Integer64"}}]}, {"Integer64"} | Failure],
			Typed["left"[Typed[{}, {"Integer64"}]], {"Integer64"} | Failure],
			Function[{Typed[row, {"Integer64"}], Typed[rest, {{"Integer64"}}], Typed[r, {"Integer64"} | Failure]},
				"confirmBind"["confirmBind"["machineResult"[0], Function[{Typed[z, "Integer64"]}, "integerListDotTotal"[row, w, z]]], Function[{Typed[d, "Integer64"]},
					"confirmBind"[r, Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Prepend[d][ds]], {"Integer64"} | Failure]]]]]
			],
			rows
		]],
		{{"Integer64"}} -> {"Integer64"} -> ({"Integer64"} | Failure)
	]],
	TypeTheoryDefinition["rowsDotSumsInRange", Typed[
		Function[{Typed[rows, {{"Integer64"}}], Typed[w, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {{"Integer64"}}]}, TypeUniverse[0]],
			True,
			Function[{Typed[row, {"Integer64"}], Typed[rest, {{"Integer64"}}], Typed[r, TypeUniverse[0]]}, "dotSumsInRange"[row, w, 0] && r],
			rows
		]],
		{{"Integer64"}} -> {"Integer64"} -> TypeUniverse[0]
	]],
	machineTheorem["machineZeroBound", 0 < upper, {"Decide"}],
	machineTheorem["rowsDotTotalsOfSums",
	ForAll[{Typed[rows, {{"Integer64"}}], Typed[w, {"Integer64"}]}, Implies["rowsDotSumsInRange"[rows, w],
		Exists[{Typed[ds, {"Integer64"}]}, "rowsDotTotals"[rows, w] == Typed["left"[ds], {"Integer64"} | Failure] &&
			Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], ds] == Map[Function[{Typed[row, {"Integer64"}]}, "integerListDot"[row][w]], rows]]]],
	{"Introduce"[rows, w], "Induction"[rows],
		"Introduce"[h], "Exact"["existsIntroduction"[Typed[{}, {"Integer64"}], "andIntroduction"["equalityReflexivity"[Typed["left"[Typed[{}, {"Integer64"}]], {"Integer64"} | Failure]], "equalityReflexivity"[Typed[{}, {Integers}]]]]],
		"Introduce"[row, rest, ih, h],
		"Have"[zb, 0 < upper], "Exact"["machineZeroBound"],
		"Cases"["integerListDotTotalOfSums"[row, w, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, zb]], h[["left"]]]],
		"Introduce"[t, ht],
		"Cases"[ih[h[["right"]]]],
		"Introduce"[ds, hd],
		"Change"[Exists[{Typed[es, {"Integer64"}]},
			"confirmBind"["confirmBind"["machineResult"[0], Function[{Typed[z, "Integer64"]}, "integerListDotTotal"[row, w, z]]], Function[{Typed[d, "Integer64"]},
				"confirmBind"["rowsDotTotals"[rest, w], Function[{Typed[fs, {"Integer64"}]}, Typed["left"[Prepend[d][fs]], {"Integer64"} | Failure]]]]] == Typed["left"[es], {"Integer64"} | Failure] &&
			Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], es] == Prepend["integerListDot"[row][w]][Map[Function[{Typed[r, {"Integer64"}]}, "integerListDot"[r][w]], rest]]]],
		"Rewrite"["machineResultInRange"[0, "naturalInteger64Range"[0, zb]]],
		"Change"[Exists[{Typed[es, {"Integer64"}]},
			"confirmBind"["integerListDotTotal"[row, w, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, zb]]], Function[{Typed[d, "Integer64"]},
				"confirmBind"["rowsDotTotals"[rest, w], Function[{Typed[fs, {"Integer64"}]}, Typed["left"[Prepend[d][fs]], {"Integer64"} | Failure]]]]] == Typed["left"[es], {"Integer64"} | Failure] &&
			Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], es] == Prepend["integerListDot"[row][w]][Map[Function[{Typed[r, {"Integer64"}]}, "integerListDot"[r][w]], rest]]]],
		"Rewrite"[ht[["left"]]],
		"Change"[Exists[{Typed[es, {"Integer64"}]},
			"confirmBind"["rowsDotTotals"[rest, w], Function[{Typed[fs, {"Integer64"}]}, Typed["left"[Prepend[t][fs]], {"Integer64"} | Failure]]] == Typed["left"[es], {"Integer64"} | Failure] &&
			Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], es] == Prepend["integerListDot"[row][w]][Map[Function[{Typed[r, {"Integer64"}]}, "integerListDot"[r][w]], rest]]]],
		"Rewrite"[hd[["left"]]],
		"Exact"["existsIntroduction"[Prepend[t][ds], "andIntroduction"["equalityReflexivity"[Typed["left"[Prepend[t][ds]], {"Integer64"} | Failure]],
			"equalityTransitivity"["equalityCongruence"[Function[{Typed[k, Integers]}, Prepend[k][Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], ds]]],
					"equalityTransitivity"[ht[["right"]], "integerAdditionZeroLeft"["integerListDot"[row][w]]]],
				"equalityCongruence"[Function[{Typed[ks, {Integers}]}, Prepend["integerListDot"[row][w]][ks]], hd[["right"]]]]]]]}
],
	machineTheorem["confirmBindAssociativity",
	ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[C, TypeUniverse[1]], Typed[p, A | Failure], Typed[f, A -> B | Failure], Typed[k, B -> C | Failure]},
		"confirmBind"["confirmBind"[p, f], k] == "confirmBind"[p, Function[{Typed[t, A]}, "confirmBind"[f[t], k]]]],
	{"Introduce"[A, B, C, p], "Cases"[p], "Introduce"[a, f, k], "Reflexivity", "Introduce"[e, f, k], "Reflexivity"}
],
	machineTheorem["confirmBindCongruence",
	ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[p, A | Failure], Typed[f, A -> B | Failure], Typed[g, A -> B | Failure]},
		Implies[ForAll[{Typed[t, A]}, f[t] == g[t]], "confirmBind"[p, f] == "confirmBind"[p, g]]],
	{"Introduce"[A, B, p], "Cases"[p], "Introduce"[a, f, g, h], "Exact"[h[a]], "Introduce"[e, f, g, h], "Reflexivity"}
],
	machineTheorem["confirmBindFirstThen",
	ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[C, TypeUniverse[1]], Typed[D, TypeUniverse[1]], Typed[E, TypeUniverse[1]],
			Typed[p, CartesianProductType[A, B] | Failure], Typed[d, A | Failure], Typed[c, CartesianProductType[A, B] -> C | Failure], Typed[k, C -> D | Failure],
			Typed[h, A -> E | Failure], Typed[g, E -> D | Failure]},
		Implies["confirmBind"[p, Function[{Typed[t, CartesianProductType[A, B]]}, Typed["left"[t[["first"]]], A | Failure]]] == d,
			Implies[ForAll[{Typed[t, CartesianProductType[A, B]]}, "confirmBind"[c[t], k] == "confirmBind"[h[t[["first"]]], g]],
				"confirmBind"["confirmBind"[p, c], k] == "confirmBind"["confirmBind"[d, h], g]]]],
	{"Introduce"[A, B, C, D, E, p], "Cases"[p],
		"Introduce"[t, d, c, k, h, g, e, hc], "Rewrite"[e, "RightToLeft"], "Exact"[hc[t]],
		"Introduce"[f, d, c, k, h, g, e, hc], "Rewrite"[e, "RightToLeft"], "Reflexivity"}
],
	machineTheorem["rowsOfLengthOfJoin",
	ForAll[{Typed[A, TypeUniverse[1]], Typed[c, NonNegativeIntegers], Typed[row, {A}], Typed[rest, {{A}}], Typed[pre, {{A}}]},
		Implies["rowsOfLength"[Join[pre, Prepend[row][rest]], c], Length[row] == c]],
	{"Introduce"[A, c, row, rest, pre], "Induction"[pre],
		"Introduce"[h], "Exact"[h[["left"]]],
		"Introduce"[x, tail, ih, h], "Exact"[ih[h[["right"]]]]}
]
}]
