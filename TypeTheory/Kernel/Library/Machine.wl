(* ::Package:: *)

(*
The machine integers: TypeTheoryEnvironment["Machine"] is the environment of the integers with the 64-bit integers of
the compiler's typed entries, built and checked the first time it is asked for. A machine integer is an integer in
[-2^63, 2^63), a subtype of the integers, and an operation on machine integers gives the machine integer of the
integer it computes where that integer is in range, and a failure, Failure["IntegerOverflow", <||>], where it is
not: a typed entry of the compiler leaves its machine code for the generic code of the Wolfram Language where a
value is out of its type, and the failure is that leave.

	"Integer64"                      Subtype["integer64Range"], an integer x with -2^63 <= x < 2^63, as the
	                                 compiler and NumericArray name the type
	"MachineInteger", "Boolean"      the compiler's other names: "Integer64" on a 64-bit machine, and the Booleans
	"machineResult"[x]               the machine integer of x where x is in range, "left", and the failure where it
	                                 is not, "right": Integer64 | Failure
	"machinePlus", "machineTimes"    the sum and the product of machine integers, as machine results
	"machineIf"[b, x, y]             the compiler's If of a Boolean test
	"machineQuotient", "machineMod"  the quotient rounded down and the remainder of two machine integers' values, as
	                                 machine results, leaving with Failure["DivideByZero", <||>] by 0

The range is decided by the order of the integers, "integerLessEqualDecidable", so a machine result of literals
computes: "machineResult"[5] is the machine integer 5, and "machineResult"[2^63] the failure. Where an exact result is
in range it is the machine value, "machineResultInRange", and the natural numbers below 2^63 are machine integers,
"naturalInteger64Range": the first steps of the bridge from the machine's arithmetic to the mathematics, which
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
	TypeTheoryDefinition["integer64Range", Typed[Typed[x, Integers] |-> Typed[lower, Integers] <= x && x < Typed[upper, Integers], Integers -> TypeUniverse[0]]],
	TypeTheoryDefinition["Integer64", Subtype["integer64Range"]],
	(* the compiler's names: "MachineInteger" is "Integer64" on a 64-bit machine, and "Boolean" the Booleans *)
	TypeTheoryDefinition["MachineInteger", "Integer64"],
	TypeTheoryDefinition["Boolean", Booleans],
	TypeTheoryDefinition["machineResult", Typed[
		Typed[x, Integers] |-> InductiveRecursor[Decidable][
			Typed[d, Decidable["integer64Range"[x]]] |-> "Integer64" | Failure,
			Typed[h, Not["integer64Range"[x]]] |-> Typed["right"[Failure["IntegerOverflow", <||>]], "Integer64" | Failure],
			Typed[h, "integer64Range"[x]] |-> Typed["left"["subtype"[x, h]], "Integer64" | Failure],
			"machineDecision"["integer64Range"[x]]
		],
		Integers -> ("Integer64" | Failure)
	]],
	(* an exact result in range is the machine value, with no overflow: the decision of the range, whatever the instance,
	   takes its true case, and any two proofs of the range are one *)
	TypeTheoryTheorem["machineResultInRange",
		ForAll[{Typed[x, Integers], Typed[h, "integer64Range"[x]]}, "machineResult"[x] == Typed["left"["subtype"[x, h]], "Integer64" | Failure]],
		Function[{Typed[x, Integers], Typed[h, "integer64Range"[x]]}, InductiveRecursor[Decidable][
			Typed[d, Decidable["integer64Range"[x]]] |-> InductiveRecursor[Decidable][
				Typed[e, Decidable["integer64Range"[x]]] |-> "Integer64" | Failure,
				Typed[k, Not["integer64Range"[x]]] |-> Typed["right"[Failure["IntegerOverflow", <||>]], "Integer64" | Failure],
				Typed[k, "integer64Range"[x]] |-> Typed["left"["subtype"[x, k]], "Integer64" | Failure],
				d
			] == Typed["left"["subtype"[x, h]], "Integer64" | Failure],
			Typed[k, Not["integer64Range"[x]]] |-> "falseElimination"[k[h]],
			Typed[k, "integer64Range"[x]] |-> "equalityReflexivity"[Typed["left"["subtype"[x, h]], "Integer64" | Failure]],
			"machineDecision"["integer64Range"[x]]
		]]
	],
	(* the compiler's If of a Boolean test, the first value where it is true and the second where it is false *)
	TypeTheoryDefinition["machineIf", Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[b, "Boolean"], Typed[x, A], Typed[y, A]},
		InductiveRecursor[Booleans][Function[{Typed[c, Booleans]}, A], y, x, b]
	]],
	(* the machine quotient and remainder of the values of two machine integers, as the compiler's C computes them: by a 0
	   divisor the typed entry leaves, Failure["DivideByZero", <||>]; otherwise the quotient rounded down, which is out of
	   range only for -2^63 / -1, and the remainder, which is always in range *)
	TypeTheoryDefinition["machineQuotient", Typed[
		Function[{Typed[x, Integers], Typed[y, Integers]}, "machineIf"["integerEqual"[y, 0], Typed["right"[Failure["DivideByZero", <||>]], "Integer64" | Failure], "machineResult"[Quotient[x, y]]]],
		Integers -> Integers -> ("Integer64" | Failure)
	]],
	TypeTheoryDefinition["machineMod", Typed[
		Function[{Typed[x, Integers], Typed[y, Integers]}, "machineIf"["integerEqual"[y, 0], Typed["right"[Failure["DivideByZero", <||>]], "Integer64" | Failure], "machineResult"[Mod[x, y]]]],
		Integers -> Integers -> ("Integer64" | Failure)
	]],
	TypeTheoryDefinition["machinePlus", Typed[{a, b} |-> "machineResult"[a[[1]] + b[[1]]], "Integer64" -> "Integer64" -> ("Integer64" | Failure)]],
	TypeTheoryDefinition["machineTimes", Typed[{a, b} |-> "machineResult"[a[[1]] b[[1]]], "Integer64" -> "Integer64" -> ("Integer64" | Failure)]],
	(* the natural numbers below 2^63 are machine integers: the relations of the pairs, stated as the integers' order
	   unfolds them, proved by terms that reduce no sum that holds the bound, only sums of literals, so that a kernel
	   that unfolds a literal one unit at a time, as Lean's does for m + 2^63, checks them too: x + 0 == x of such a
	   sum is "additionZeroRight", not a computation *)
	TypeTheoryTheorem["integer64LowerRelation",
		ForAll[{Typed[m, NonNegativeIntegers]}, m + (upper + 0) == (0 + (m + upper)) + 0],
		Function[{Typed[m, NonNegativeIntegers]}, "equalityTransitivity"["equalitySymmetry"["additionZeroLeft"[m + upper]], "equalitySymmetry"["additionZeroRight"[0 + (m + upper)]]]]
	],
	TypeTheoryTheorem["integer64UpperRelation",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[upper == m + 1 + k, upper + (0 + 0 + 0) == ((m + 1) + k) + 0]],
		Function[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[e, upper == m + 1 + k]}, e]
	],
	machineTheorem["naturalInteger64Range",
		ForAll[{Typed[m, NonNegativeIntegers]}, Implies[m < upper, "integer64Range"["integerOfNatural"[m]]]],
		{
			"Introduce"[m, h], "Constructor",
			"Exact"["existsIntroduction"[m + upper, "quotientSoundness"["integer64LowerRelation"[m]]]],
			"Exact"[InductiveRecursor[Exists][
				Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, upper == m + 1 + k]] |-> "integerOfNatural"[m] < Typed[upper, Integers],
				{Typed[k, NonNegativeIntegers], Typed[e, upper == m + 1 + k]} |-> "existsIntroduction"[k, "quotientSoundness"["integer64UpperRelation"[m, k, e]]],
				"lessEqualWitness"[m + 1, upper, h]
			]]
		}
	]
}]
