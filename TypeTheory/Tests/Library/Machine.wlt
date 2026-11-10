(* ::Package:: *)

(* Tests for Library/Machine.wl: the 64-bit integers of the compiler's typed entries, a subtype of the integers, whose
   operations give the machine integer of an exact result in range and the failure IntegerOverflow, the leave of a
   typed entry, out of it.
   Run with: TestReport["TypeTheory/Tests/Library/Machine.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

machine = TypeTheoryEnvironment["Machine"]


VerificationTest[
	{
		Length[Information[machine, "Constants"]] - Length[Information[TypeTheoryEnvironment["Integers"], "Constants"]],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["machinePlus", machine]], TypeTheoryTerm[Integers -> Integers -> ("Integer64" | Failure), machine]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["naturalInteger64Range", machine]],
		(* the compiler's names for the types *)
		DefinitionallyEqualQ[TypeTheoryTerm["MachineInteger", machine], TypeTheoryTerm["Integer64", machine]],
		DefinitionallyEqualQ[TypeTheoryTerm["Boolean", machine], TypeTheoryTerm[Booleans, machine]]
	},
	{25, True, <|"quotientSoundness" -> "Proposition"|>, True, True},
	TestID -> "The-machine-integers-extend-the-integers"
]

(* a result in range is the machine integer, read as the integer, and one out of range the leave, at both ends of
   [-2^63, 2^63) *)
VerificationTest[
	Map[
		Function[value, TypeTheoryExpression[NormalForm[TypeTheoryTerm["machineResult"[Typed[value, Integers]], machine]]]],
		{5, -9223372036854775808, 9223372036854775807, 9223372036854775808, -9223372036854775809}
	],
	{5, -9223372036854775808, 9223372036854775807, Failure["IntegerOverflow", <||>], Failure["IntegerOverflow", <||>]},
	TestID -> "A-machine-result-is-the-integer-in-range-and-a-leave-out-of-it"
]

(* the machine's sum and product of integers are machine results: 3 + 3 and 3 3, and 2^62 + 2^62, which overflows; a
   machine integer made of an integer in range, the range decided, has that integer as its part "integer" *)
VerificationTest[
	Module[{three},
		(* a symbol whose value is a finished proof stands for its proof in a term *)
		three = TypeTheoryProof[TypeTheoryTerm["integer64Range"[Typed[3, Integers]], machine], {"Decide"}];
		{
			TypeTheoryExpression[NormalForm[TypeTheoryTerm["machinePlus"[3, 3], machine]]],
			TypeTheoryExpression[NormalForm[TypeTheoryTerm["machineTimes"[3, 3], machine]]],
			TypeTheoryExpression[NormalForm[TypeTheoryTerm["machinePlus"[4611686018427387904, 4611686018427387904], machine]]],
			TypeTheoryExpression[NormalForm[TypeTheoryTerm["machinePlus"[Typed["subtype"[Typed[3, Integers], three], "Integer64"]["integer"], 4], machine]]]
		}
	],
	{6, 9, Failure["IntegerOverflow", <||>], 7},
	TestID -> "Machine-sums-and-products-overflow-as-a-leave"
]
