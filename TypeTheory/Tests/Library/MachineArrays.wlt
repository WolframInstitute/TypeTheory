(* ::Package:: *)

(* Tests for Library/MachineArrays.wl: the vectors of typed code, lists that a machine can hold, with the operations of
   typed code on them and their leaves, in TypeTheoryEnvironment["Machine"]. A part is counted from 1, or below 0 from
   the end; one that is not there is Failure["PartRange", <||>].
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
