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
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["machinePlus", machine]], TypeTheoryTerm[TypeSpecifier[{"Int64", "Int64"} -> ("Int64" | Failure)], machine]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["naturalInt64Range", machine]]
	},
	{10, True, <|"quotientSoundness" -> "Proposition"|>},
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

(* machine integers made of integers in range, the range decided; their sum and product are machine results: 3 + 3 and
   3 3, and 2^62 + 2^62, which overflows *)
VerificationTest[
	Module[{three, half},
		(* a symbol whose value is a finished proof stands for its proof in a term *)
		three = TypeTheoryProof[TypeTheoryTerm["int64Range"[Typed[3, Integers]], machine], {"Decide"}];
		half = TypeTheoryProof[TypeTheoryTerm["int64Range"[Typed[4611686018427387904, Integers]], machine], {"Decide"}];
		{
			TypeTheoryExpression[NormalForm[TypeTheoryTerm["machinePlus"["subtype"[Typed[3, Integers], three], "subtype"[Typed[3, Integers], three]], machine]]],
			TypeTheoryExpression[NormalForm[TypeTheoryTerm["machineTimes"["subtype"[Typed[3, Integers], three], "subtype"[Typed[3, Integers], three]], machine]]],
			TypeTheoryExpression[NormalForm[TypeTheoryTerm["machinePlus"["subtype"[Typed[4611686018427387904, Integers], half], "subtype"[Typed[4611686018427387904, Integers], half]], machine]]]
		}
	],
	{6, 9, Failure["IntegerOverflow", <||>]},
	TestID -> "Machine-sums-and-products-overflow-as-a-leave"
]
