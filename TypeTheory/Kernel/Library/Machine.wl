(* ::Package:: *)

(*
The machine integers: TypeTheoryEnvironment["Machine"] is the environment of the integers with the 64-bit integers of
the compiler's typed entries, built and checked the first time it is asked for. A machine integer is an integer in
[-2^63, 2^63), a subtype of the integers, and an operation on machine integers gives the machine integer of the
integer it computes where that integer is in range, and a failure, Failure["IntegerOverflow", <||>], where it is
not: a typed entry of the compiler leaves its machine code for the generic code of the Wolfram Language where a
value is out of its type, and the failure is that leave.

	"Int64"                          Subtype["int64Range"], an integer x with -2^63 <= x < 2^63
	"machineResult"[x]               the machine integer of x where x is in range, "left", and the failure where it
	                                 is not, "right": Int64 | Failure
	"machinePlus", "machineTimes"    the sum and the product of machine integers, as machine results

The range is decided by the order of the integers, "integerLessEqualDecidable", so a machine result of literals
computes: "machineResult"[5] is the machine integer 5, and "machineResult"[2^63] the failure. Where an exact result is
in range it is the machine value, "machineResultInRange", and the natural numbers below 2^63 are machine integers,
"naturalInt64Range": the first steps of the bridge from the machine's arithmetic to the mathematics, which
TypeTheoryFormalize[f, "Machine"] is to state of a compiled function.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[machineEnvironment]


(* ::Section:: *)
(*Usage Messages*)


machineEnvironment::usage = "machineEnvironment[] gives the environment of the integers with the 64-bit integers of the compiler's typed entries, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations in order, each theorem proved by its tactics in the environment so far *)
machineEnvironment[] := machineEnvironment[] = withoutStoreTracking[
	libraryEnvironment["Machine", integersEnvironment[], withStoreCleanup[Fold[addMachineDeclaration, integersEnvironment[], $machineDeclarations]]]
]

SetAttributes[machineTheorem, HoldAll]

addMachineDeclaration[failure_Failure, _] := failure
addMachineDeclaration[environment_, machineTheorem[name_, statement_, tactics_List]] :=
	TypeTheoryEnvironment[environment, {TypeTheoryTheorem[name, TypeTheoryProof[statement, environment, tactics]]}]
addMachineDeclaration[environment_, declaration_] := TypeTheoryEnvironment[environment, {declaration}]

(* the bounds written as literals, never as powers, which the integers would compute one factor at a time *)
$machineDeclarations = With[{lower = -9223372036854775808, upper = 9223372036854775808}, {
	TypeTheoryDefinition["machineDecision", Function[{Typed[q, TypeUniverse[0]], Annotation[Typed[d, Decidable[q]], "InstanceImplicit"]}, d]],
	TypeTheoryDefinition["int64Range", Typed[Typed[x, Integers] |-> Typed[lower, Integers] <= x && x < Typed[upper, Integers], Integers -> TypeUniverse[0]]],
	TypeTheoryDefinition["Int64", Subtype["int64Range"]],
	TypeTheoryDefinition["machineResult", Typed[
		Typed[x, Integers] |-> InductiveRecursor[Decidable][
			Typed[d, Decidable["int64Range"[x]]] |-> "Int64" | Failure,
			Typed[h, Not["int64Range"[x]]] |-> Typed["right"[Failure["IntegerOverflow", <||>]], "Int64" | Failure],
			Typed[h, "int64Range"[x]] |-> Typed["left"["subtype"[x, h]], "Int64" | Failure],
			"machineDecision"["int64Range"[x]]
		],
		Integers -> ("Int64" | Failure)
	]],
	(* an exact result in range is the machine value, with no overflow: the decision of the range, whatever the instance,
	   takes its true case, and any two proofs of the range are one *)
	TypeTheoryTheorem["machineResultInRange",
		ForAll[{Typed[x, Integers], Typed[h, "int64Range"[x]]}, "machineResult"[x] == Typed["left"["subtype"[x, h]], "Int64" | Failure]],
		Function[{Typed[x, Integers], Typed[h, "int64Range"[x]]}, InductiveRecursor[Decidable][
			Typed[d, Decidable["int64Range"[x]]] |-> InductiveRecursor[Decidable][
				Typed[e, Decidable["int64Range"[x]]] |-> "Int64" | Failure,
				Typed[k, Not["int64Range"[x]]] |-> Typed["right"[Failure["IntegerOverflow", <||>]], "Int64" | Failure],
				Typed[k, "int64Range"[x]] |-> Typed["left"["subtype"[x, k]], "Int64" | Failure],
				d
			] == Typed["left"["subtype"[x, h]], "Int64" | Failure],
			Typed[k, Not["int64Range"[x]]] |-> "falseElimination"[k[h]],
			Typed[k, "int64Range"[x]] |-> "equalityReflexivity"[Typed["left"["subtype"[x, h]], "Int64" | Failure]],
			"machineDecision"["int64Range"[x]]
		]]
	],
	TypeTheoryDefinition["machinePlus", Typed[{a, b} |-> "machineResult"[a[[1]] + b[[1]]], "Int64" -> "Int64" -> ("Int64" | Failure)]],
	TypeTheoryDefinition["machineTimes", Typed[{a, b} |-> "machineResult"[a[[1]] b[[1]]], "Int64" -> "Int64" -> ("Int64" | Failure)]],
	(* the natural numbers below 2^63 are machine integers, the arithmetic stated of the bound so that LinearArithmetic
	   reads it as an offset *)
	(* the arithmetic stated of a bound b, not of the literal, which LinearArithmetic then never meets *)
	machineTheorem["int64LowerRelation", ForAll[{Typed[m, NonNegativeIntegers]}, m + (upper + 0) == (0 + (m + upper)) + 0], {"Introduce"[m], "LinearArithmetic"}],
	machineTheorem["int64UpperRelation",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[upper == m + 1 + k, upper + (0 + 0 + 0) == ((m + 1) + k) + 0]],
		{"Introduce"[m, k, e], "LinearArithmetic"}
	],
	machineTheorem["naturalInt64Range",
		ForAll[{Typed[m, NonNegativeIntegers]}, Implies[m < upper, "int64Range"["integerOfNatural"[m]]]],
		{
			"Introduce"[m, h], "Constructor",
			"Exact"["existsIntroduction"[m + upper, "quotientSoundness"["int64LowerRelation"[m]]]],
			"Exact"[InductiveRecursor[Exists][
				Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, upper == m + 1 + k]] |-> "integerOfNatural"[m] < Typed[upper, Integers],
				{Typed[k, NonNegativeIntegers], Typed[e, upper == m + 1 + k]} |-> "existsIntroduction"[k, "quotientSoundness"["int64UpperRelation"[m, k, e]]],
				"lessEqualWitness"[m + 1, upper, h]
			]]
		}
	]
}]
