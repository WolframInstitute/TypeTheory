(* ::Package:: *)

(* Tests for Library/MachineArrays.wl: the vectors of typed code, lists that a machine can hold, and its matrices, which
   keep their columns, with the operations of typed code on them and their leaves, in TypeTheoryEnvironment["Machine"].
   A part is counted from 1, or below 0 from the end; one that is not there is Failure["PartRange", <||>].
   Run with: TestReport["TypeTheory/Tests/Library/MachineArrays.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

machine = TypeTheoryEnvironment["Machine"]

(* {10, 0, 30}: a constant array of three 0s, its first part set to 10 and its last to 30 *)
samples = TypeTheoryEnvironment[machine, {
	TypeTheoryDefinition["sampleArray", Typed[
		"confirmBind"["machineResult"[0], Typed[z, "Integer64"] |-> "confirmBind"["arrayConstant"[z, 3], Typed[a, "PackedArray"["Integer64", 1]] |->
			"confirmBind"["machineResult"[10], Typed[t, "Integer64"] |-> "confirmBind"["arraySetPart"[a, 1, t], Typed[b, "PackedArray"["Integer64", 1]] |->
				"confirmBind"["machineResult"[30], Typed[u, "Integer64"] |-> "arraySetPart"[b, -1, u]]]]]],
		"PackedArray"["Integer64", 1] | Failure
	]]
}]

(* the value of a function of the sample array *)
SetAttributes[onSample, HoldFirst]
onSample[function_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["sampleArray", function], samples]]]

(* the vectors are in the machine's environment, with no axiom of their own; an array is a list with the proof that a
   machine holds it, and the array of rank 0 is the element *)
VerificationTest[
	{
		Complement[Information[machine, "Axioms"], Information[TypeTheoryEnvironment["Integers"], "Axioms"]],
		DefinitionallyEqualQ[TypeTheoryTerm["PackedArray"["Integer64", 1], machine], TypeTheoryTerm[Subtype["arrayLengthRange"["Integer64"]], machine]],
		DefinitionallyEqualQ[TypeTheoryTerm["PackedArray"["Integer64", 0], machine], TypeTheoryTerm["Integer64", machine]],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["arrayLength", machine]], TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> "Integer64"], machine]],
		Map[
			Function[name, TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, machine}]],
			{"arraySetPartLength", "arraySetPartLeave", "arrayTakeLength", "arrayTakeLeave", "arrayConstantOfNatural", "integerListTotalOfSums"}
		]
	},
	{{}, True, True, True, ConstantArray[<|"quotientSoundness" -> "Proposition"|>, 6]},
	TestID -> "The-vectors-are-lists-a-machine-holds-with-no-axiom-of-their-own"
]

(* the operations on {10, 0, 30}, as Wolfram's evaluator gives them, and the leaves of typed code where it gives none *)
VerificationTest[
	{
		onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> Typed["left"[a], "PackedArray"["Integer64", 1] | Failure]],
		onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> Typed["left"["arrayLength"[a]], "Integer64" | Failure]],
		Map[Function[i, onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> "arrayPart"[a, Typed[i, Integers]]]], {1, 2, 3, -1, -3}],
		Map[Function[n, onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> "arrayTake"[a, Typed[n, Integers]]]], {2, -1, 0, 3}],
		onSample["arrayTotal"],
		onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> "confirmBind"["machineResult"[7], Typed[x, "Integer64"] |-> "arraySetPart"[a, -2, x]]]
	},
	{
		{10, 0, 30},
		Length[{10, 0, 30}],
		Map[Function[i, Part[{10, 0, 30}, i]], {1, 2, 3, -1, -3}],
		Map[Function[n, Take[{10, 0, 30}, n]], {2, -1, 0, 3}],
		Total[{10, 0, 30}],
		ReplacePart[{10, 0, 30}, -2 -> 7]
	},
	TestID -> "Parts-Take-Total-and-a-part-set-are-the-evaluators"
]

VerificationTest[
	{
		Map[Function[i, onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> "arrayPart"[a, Typed[i, Integers]]]], {0, 4, -4}],
		Map[Function[n, onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> "arrayTake"[a, Typed[n, Integers]]]], {4, -4}],
		onSample[Typed[a, "PackedArray"["Integer64", 1]] |-> "confirmBind"["machineResult"[7], Typed[x, "Integer64"] |-> "arraySetPart"[a, 0, x]]],
		Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[7], Typed[x, "Integer64"] |-> "arrayConstant"[x, Typed[n, Integers]]], machine]]]], {-1, 0, 2}],
		(* 2^62 + 2^62 is past the machine integers, 2^62 - 1 + 2^62 is not *)
		Map[
			Function[x, TypeTheoryExpression[NormalForm[TypeTheoryTerm[
				"confirmBind"["machineResult"[Typed[x, Integers]], Typed[y, "Integer64"] |-> "confirmBind"["machineResult"[4611686018427387904], Typed[z, "Integer64"] |->
					"confirmBind"["arrayConstant"[y, 2], Typed[a, "PackedArray"["Integer64", 1]] |-> "confirmBind"["arraySetPart"[a, 2, z], "arrayTotal"]]]],
				machine
			]]]],
			{4611686018427387904, 4611686018427387903}
		]
	},
	{
		ConstantArray[Failure["PartRange", <||>], 3],
		ConstantArray[Failure["PartRange", <||>], 2],
		Failure["PartRange", <||>],
		{Failure["Range", <||>], {}, {7, 7}},
		{Failure["IntegerOverflow", <||>], 9223372036854775807}
	},
	TestID -> "A-part-that-is-not-there-a-negative-length-and-a-total-past-the-machine-leave"
]

(* what the operations promise: a part set keeps the length, Take of a count that is not below 0 has that length and
   never more than the array has, both leave by a part that is not there alone, never for want of memory, and a constant
   array of a length a machine integer counts is there *)
VerificationTest[
	Map[
		Function[pair, With[{theorem = TypeTheoryTerm @@ {First[pair], machine}}, DefinitionallyEqualQ[TypeTheoryType[theorem], Last[pair]]]],
		{
			{"arraySetPartLength", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A], Typed[b, "PackedArray"[A, 1]]},
				Implies["arraySetPart"[a, i, v] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] == Length[a[["list"]]]]], machine]},
			{"arraySetPartLeave", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A], Typed[e, Failure]},
				Implies["arraySetPart"[a, i, v] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]], machine]},
			{"arrayTakeLength", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[b, "PackedArray"[A, 1]]},
				Implies["integerLessEqualQ"[0, n] == "true", Implies["arrayTake"[a, n] == Typed["left"[b], "PackedArray"[A, 1] | Failure], "integerOfNatural"[Length[b[["list"]]]] == n]]], machine]},
			{"arrayTakeLengthBound", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[b, "PackedArray"[A, 1]]},
				Implies["arrayTake"[a, n] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] <= Length[a[["list"]]]]], machine]},
			{"arrayTakeLeave", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[e, Failure]},
				Implies["arrayTake"[a, n] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]], machine]},
			{"arrayConstantOfNatural", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[c, A], Typed[k, NonNegativeIntegers]}, Implies[k < 9223372036854775808,
				Exists[{Typed[a, "PackedArray"[A, 1]]}, "arrayConstant"[c, "integerOfNatural"[k]] == Typed["left"[a], "PackedArray"[A, 1] | Failure] && a[["list"]] == "listConstant"[c, k]]]], machine]}
		}
	],
	ConstantArray[True, 6],
	TestID -> "A-part-set-keeps-the-length-Take-gives-the-length-asked-and-neither-runs-out-of-memory"
]

(* an array is not made from a list without the proof that a machine holds it: a value of "PackedArray" whose proof is
   another's is refused *)
VerificationTest[
	TypeTheoryEnvironment[machine, {TypeTheoryDefinition["forgedArray", Typed["subtype"[Typed[{}, {"Integer64"}], "trueIntroduction"], "PackedArray"["Integer64", 1]]]}]["Tag"],
	"TypeMismatch",
	TestID -> "An-array-needs-the-proof-that-its-list-is-held"
]

(* the matrices: Partition[{1, 2, 3, 4, 5}, 2] and Partition[{1, 2}, 3], of natural numbers, as the operations do not
   depend on the elements; and Partition[{3, 2, 2, 2, 2, 2}, 3] and {1, 1, 1} of machine integers, for the product *)
matrixSamples = TypeTheoryEnvironment[machine, {
	TypeTheoryDefinition["sampleMatrix", Typed[
		"confirmBind"["arrayOfList"[Typed[{1, 2, 3, 4, 5}, {NonNegativeIntegers}]], Typed[a, "PackedArray"[NonNegativeIntegers, 1]] |-> "matrixOfPartition"[a, 2]],
		"PackedArray"[NonNegativeIntegers, 2] | Failure
	]],
	TypeTheoryDefinition["emptyMatrix", Typed[
		"confirmBind"["arrayOfList"[Typed[{1, 2}, {NonNegativeIntegers}]], Typed[a, "PackedArray"[NonNegativeIntegers, 1]] |-> "matrixOfPartition"[a, 3]],
		"PackedArray"[NonNegativeIntegers, 2] | Failure
	]],
	TypeTheoryDefinition["sampleProduct", Typed[
		"confirmBind"["machineResult"[2], Typed[z, "Integer64"] |-> "confirmBind"["arrayConstant"[z, 6], Typed[a, "PackedArray"["Integer64", 1]] |->
			"confirmBind"["machineResult"[3], Typed[t, "Integer64"] |-> "confirmBind"["arraySetPart"[a, 1, t], Typed[b, "PackedArray"["Integer64", 1]] |->
				"confirmBind"["matrixOfPartition"[b, 3], Typed[m, "PackedArray"["Integer64", 2]] |->
					"confirmBind"["machineResult"[1], Typed[o, "Integer64"] |-> "confirmBind"["arrayConstant"[o, 3], Typed[v, "PackedArray"["Integer64", 1]] |->
						Typed["left"["matrixVectorProduct"[m, v]], {Integers} | Failure]]]]]]]],
		{Integers} | Failure
	]]
}]

(* the value of a function of a sample matrix; the rows, the dimensions and a transpose's rows as lists of the
   natural numbers *)
onMatrix[sample_String, function_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"[sample, function], matrixSamples]]]
rowsOf = Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> Typed["left"[m[["rows"]]], {{NonNegativeIntegers}} | Failure];
dimensionsOf = Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |->
	Typed["left"["matrixDimensions"[m]], {NonNegativeIntegers} | Failure];

(* a matrix is the array of rank 2, and keeps its columns; the array of a rank above is a "Tensor", the matrix of its
   first two levels over the levels below. Transpose twice is the identity on every matrix with no axiom; the leaves and Partition
   rest on the integers' alone *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm["PackedArray"["Integer64", 2], machine], TypeTheoryTerm["Matrix"["Integer64"], machine]],
		DefinitionallyEqualQ[TypeTheoryTerm["PackedArray"["Integer64", 3], machine], TypeTheoryTerm["Tensor"["Integer64", 0], machine]],
		Map[
			Function[name, TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, machine}]],
			{"matrixTransposeTwice", "matrixDimensionsOfTranspose", "matrixOfPartitionOfNatural", "matrixRowLeave", "matrixPartLeave"}
		]
	},
	{True, True, {<||>, <||>, <|"quotientSoundness" -> "Proposition"|>, <|"quotientSoundness" -> "Proposition"|>, <|"quotientSoundness" -> "Proposition"|>}},
	TestID -> "A-matrix-is-the-array-of-rank-2-and-Transpose-twice-needs-no-axiom"
]

(* Partition, Length, a row, an element, Dimensions and Transpose of Partition[{1, 2, 3, 4, 5}, 2], as the evaluator
   gives them; a matrix of no rows keeps its columns, which the evaluator's list of lists does not: Dimensions of
   Partition[{1, 2}, 3] is {0, 3}, and of its transpose {3, 0}. The product as Dot gives it *)
VerificationTest[
	{
		onMatrix["sampleMatrix", rowsOf],
		onMatrix["sampleMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> Typed["left"["matrixLength"[m]], "Integer64" | Failure]],
		Map[Function[i, onMatrix["sampleMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> "matrixRow"[m, Typed[i, Integers]]]], {1, 2, -1}],
		Apply[Function[{i, j}, onMatrix["sampleMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> "matrixPart"[m, Typed[i, Integers], Typed[j, Integers]]]], {{1, 1}, {2, 1}, {-1, -1}, {1, -2}}, {1}],
		onMatrix["sampleMatrix", dimensionsOf],
		onMatrix["sampleMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> Typed["left"["matrixTranspose"[m][["rows"]]], {{NonNegativeIntegers}} | Failure]],
		onMatrix["emptyMatrix", dimensionsOf],
		With[{dimensions = dimensionsOf}, onMatrix["emptyMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> dimensions["matrixTranspose"[m]]]],
		TypeTheoryExpression[NormalForm[TypeTheoryTerm["sampleProduct", matrixSamples]]]
	},
	{
		Partition[{1, 2, 3, 4, 5}, 2],
		Length[Partition[{1, 2, 3, 4, 5}, 2]],
		Map[Function[i, Part[Partition[{1, 2, 3, 4, 5}, 2], i]], {1, 2, -1}],
		Apply[Function[{i, j}, Part[Partition[{1, 2, 3, 4, 5}, 2], i, j]], {{1, 1}, {2, 1}, {-1, -1}, {1, -2}}, {1}],
		Dimensions[Partition[{1, 2, 3, 4, 5}, 2]],
		Transpose[Partition[{1, 2, 3, 4, 5}, 2]],
		{0, 3},
		{3, 0},
		Dot[Partition[{3, 2, 2, 2, 2, 2}, 3], {1, 1, 1}]
	},
	TestID -> "Partition-Length-parts-Dimensions-Transpose-and-the-product-are-the-evaluators"
]

(* Partition by a count below 1 leaves with Failure["Range", <||>], a row or an element that is not there with
   Failure["PartRange", <||>] *)
VerificationTest[
	{
		Map[Function[k, TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			"confirmBind"["arrayOfList"[Typed[{1, 2}, {NonNegativeIntegers}]], Typed[a, "PackedArray"[NonNegativeIntegers, 1]] |-> "matrixOfPartition"[a, Typed[k, Integers]]],
			matrixSamples
		]]]], {0, -1}],
		Map[Function[i, onMatrix["sampleMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> "matrixRow"[m, Typed[i, Integers]]]], {0, 3, -3}],
		Apply[Function[{i, j}, onMatrix["sampleMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> "matrixPart"[m, Typed[i, Integers], Typed[j, Integers]]]], {{3, 1}, {1, 3}, {0, 1}, {1, -3}}, {1}],
		onMatrix["emptyMatrix", Typed[m, "PackedArray"[NonNegativeIntegers, 2]] |-> "matrixPart"[m, 1, 1]]
	},
	{
		ConstantArray[Failure["Range", <||>], 2],
		ConstantArray[Failure["PartRange", <||>], 3],
		ConstantArray[Failure["PartRange", <||>], 4],
		Failure["PartRange", <||>]
	},
	TestID -> "Partition-by-less-than-1-and-a-part-that-is-not-there-leave"
]

(* what the theorems say *)
VerificationTest[
	Map[
		Function[pair, With[{theorem = TypeTheoryTerm @@ {First[pair], machine}}, DefinitionallyEqualQ[TypeTheoryType[theorem], Last[pair]]]],
		{
			{"matrixTransposeTwice", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]}, "matrixTranspose"["matrixTranspose"[m]] == m], machine]},
			{"matrixDimensionsOfTranspose", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]]},
				"matrixDimensions"["matrixTranspose"[m]] == Reverse["matrixDimensions"[m]]], machine]},
			{"matrixRowLeave", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]], Typed[i, Integers], Typed[f, Failure]},
				Implies["matrixRow"[m, i] == Typed["right"[f], "PackedArray"[A, 1] | Failure], f == Failure["PartRange", <||>]]], machine]},
			{"matrixPartLeave", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[m, "PackedArray"[A, 2]], Typed[i, Integers], Typed[j, Integers], Typed[f, Failure]},
				Implies["matrixPart"[m, i, j] == Typed["right"[f], A | Failure], f == Failure["PartRange", <||>]]], machine]},
			{"matrixOfPartitionRange", TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[k, Integers]},
				Implies["integerLessEqualQ"[1, k] == "false", "matrixOfPartition"[a, k] == Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 2] | Failure]]], machine]}
		}
	],
	ConstantArray[True, 5],
	TestID -> "Transpose-twice-is-the-identity-and-the-operations-leave-where-typed-code-does"
]

(* a matrix needs the proof of its range: rows of another length than the columns, or the proof of something else, are
   refused *)
VerificationTest[
	TypeTheoryEnvironment[machine, {TypeTheoryDefinition["forgedMatrix", Typed["matrix"[2, Typed[{{1}}, {{NonNegativeIntegers}}], "trueIntroduction"], "PackedArray"[NonNegativeIntegers, 2]]]}]["Tag"],
	"TypeMismatch",
	TestID -> "A-matrix-needs-the-proof-of-its-range"
]

(* the Wolfram Language names of the operations on packed arrays: in the machine environment Length chooses among the
   lists', the associations', the vectors' and the matrices' by the type, and Partition, Take, Total, ConstantArray,
   Dimensions and Transpose are the library's, so theorems are stated as the Wolfram Language writes them; in the
   prelude the names mean what they meant *)
VerificationTest[
	{
		Map[
			Function[term, First[TypeTheoryType[term]]],
			{
				TypeTheoryTerm[Typed[m, "PackedArray"["Integer64", 2]] |-> Transpose[m], machine],
				TypeTheoryTerm[Typed[m, "PackedArray"["Integer64", 2]] |-> Dimensions[m], machine],
				TypeTheoryTerm[Typed[m, "PackedArray"["Integer64", 2]] |-> Length[m], machine],
				TypeTheoryTerm[Typed[v, "PackedArray"["Integer64", 1]] |-> Length[v], machine],
				TypeTheoryTerm[Typed[l, {NonNegativeIntegers}] |-> Length[l], machine],
				TypeTheoryTerm[Typed[a, Association[Strings, NonNegativeIntegers]] |-> Length[a], machine],
				TypeTheoryTerm[Typed[v, "PackedArray"["Integer64", 1]] |-> Partition[v, 2], machine],
				TypeTheoryTerm[Typed[v, "PackedArray"["Integer64", 1]] |-> Take[v, 2], machine],
				TypeTheoryTerm[Typed[v, "PackedArray"["Integer64", 1]] |-> Total[v], machine],
				TypeTheoryTerm[Transpose[x]]
			}
		],
		Head[TypeTheoryProof[ForAll[{Typed[m, "PackedArray"["Integer64", 2]]}, Transpose[Transpose[m]] == m], machine, {"Introduce"[m], "Exact"["matrixTransposeTwice"["Integer64", m]]}]]
	},
	{
		{
			"PackedArray"["Integer64", 2] -> "PackedArray"["Integer64", 2],
			"PackedArray"["Integer64", 2] -> {NonNegativeIntegers},
			"PackedArray"["Integer64", 2] -> "Integer64",
			"PackedArray"["Integer64", 1] -> "Integer64",
			{NonNegativeIntegers} -> NonNegativeIntegers,
			Association[Strings, NonNegativeIntegers] -> NonNegativeIntegers,
			"PackedArray"["Integer64", 1] -> DisjointUnionType["PackedArray"["Integer64", 2], Failure],
			"PackedArray"["Integer64", 1] -> DisjointUnionType["PackedArray"["Integer64", 1], Failure],
			"PackedArray"["Integer64", 1] -> DisjointUnionType["Integer64", Failure],
			Expressions
		},
		TypeTheoryProof
	},
	TestID -> "The-Wolfram-Language-names-of-array-operations-are-the-librarys-in-the-machine-environment"
]

(* a name on its own has the type of the constant it stands for: Dimensions the class's method, for every type that has
   dimensions, Transpose the library's, and Length, overloaded, that of its first meaning, the lists', which elaboration
   takes where nothing decides *)
VerificationTest[
	{
		MatchQ[TypeTheoryType[Dimensions, machine], HoldPattern[TypeTheoryTerm[ForAll[{_, Annotation[Typed[_, "Dimensional"[_]], "InstanceImplicit"]}, _ -> {NonNegativeIntegers}], _]]],
		MatchQ[First[TypeTheoryType[Transpose, machine]], "PackedArray"[a_, b_] -> "PackedArray"[a_, b_]],
		MatchQ[First[TypeTheoryType[Length, machine]], {_} -> NonNegativeIntegers],
		MatchQ[First[TypeTheoryType[Length]], {_} -> NonNegativeIntegers]
	},
	{True, True, True, True},
	TestID -> "An-overloaded-name-on-its-own-has-the-type-of-its-first-meaning"
]

(* every rank: Dimensions takes an array of any rank and gives as many dimensions as the rank; Transpose takes a rank of
   2 or more and swaps the first two levels, twice the identity, the dimensions of a transpose the first two swapped;
   the theorems use no axiom of their own, and a rank above 2 is a matrix of the levels below *)
VerificationTest[
	{
		Map[
			Function[term, First[TypeTheoryType[term]]],
			{
				TypeTheoryTerm[Typed[a, "PackedArray"["Integer64", 4]] |-> Dimensions[a], machine],
				TypeTheoryTerm[Typed[a, "PackedArray"["Integer64", 3]] |-> Transpose[a], machine]
			}
		],
		Map[Head, {
			TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[a, "PackedArray"["Integer64", n]]}, Length[Dimensions[a]] == n], machine,
				{"Introduce"[n, a], "Exact"["arrayDimensionsLength"["Integer64", n, a]]}],
			TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[a, "PackedArray"["Integer64", n + 2]]}, Transpose[Transpose[a]] == a], machine,
				{"Introduce"[n, a], "Exact"["arrayTransposeTwice"["Integer64", n, a]]}],
			TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[a, "PackedArray"["Integer64", n + 2]]}, Dimensions[Transpose[a]] == "dimensionsTransposed"[Dimensions[a]]], machine,
				{"Introduce"[n, a], "Exact"["arrayDimensionsOfTranspose"["Integer64", n, a]]}],
			TypeTheoryProof[ForAll[{Typed[m, "PackedArray"["Integer64", 2]]}, Dimensions[Transpose[m]] == Reverse[Dimensions[m]]], machine,
				{"Introduce"[m], "Exact"["arrayDimensionsOfTranspose"["Integer64", 0, m]]}]
		}],
		Map[
			Function[name, TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, machine}]],
			{"arrayDimensionsLength", "arrayTransposeTwice", "arrayDimensionsOfTranspose"}
		],
		DefinitionallyEqualQ[TypeTheoryTerm["PackedArray"["Integer64", 5], machine], TypeTheoryTerm["Tensor"["Integer64", 2], machine]]
	},
	{
		{"PackedArray"["Integer64", 4] -> {NonNegativeIntegers}, "PackedArray"["Integer64", 3] -> "PackedArray"["Integer64", 3]},
		{TypeTheoryProof, TypeTheoryProof, TypeTheoryProof, TypeTheoryProof},
		{<||>, <||>, <||>},
		True
	},
	TestID -> "Dimensions-and-Transpose-take-every-rank-and-their-theorems-hold-for-every-rank"
]
