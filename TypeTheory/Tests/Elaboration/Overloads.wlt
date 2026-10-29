(* ::Package:: *)

(* Tests for user-declared overloads: an axiom or a definition declared with "Overloads" -> operation is one more
   meaning of the operation, chosen by the types as the integers' and rationals' operations are.
   Run with: TestReport["TypeTheory/Tests/Elaboration/Overloads.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

polynomials = TypeTheoryEnvironment[{
	TypeTheoryAxiom["Polynomials", TypeUniverse[1]],
	TypeTheoryAxiom["polynomialAddition", TypeSpecifier[{"Polynomials", "Polynomials"} -> "Polynomials"], "Overloads" -> Plus],
	TypeTheoryAxiom["polynomialPower", TypeSpecifier[{"Polynomials", Naturals} -> "Polynomials"], "Overloads" -> Power],
	TypeTheoryAxiom["polynomialNegation", TypeSpecifier[{"Polynomials"} -> "Polynomials"], "Overloads" -> Minus],
	TypeTheoryAxiom[FormSpace, TypeSpecifier[{Naturals} -> TypeUniverse[1]]],
	TypeTheoryAxiom["formAddition", ForAll[{TypedImplicit[k, Naturals]}, TypeSpecifier[{FormSpace[k], FormSpace[k]} -> FormSpace[k]]], "Overloads" -> Plus],
	TypeTheoryAxiom["formPower", ForAll[{TypedImplicit[k, Naturals], Typed[f, FormSpace[k]], Typed[n, Naturals]}, FormSpace[k n]], "Overloads" -> Power]
}]


VerificationTest[
	{
		First[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, "Polynomials"]}, x^2 + x], polynomials]]],
		First[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, "Polynomials"]}, -x], polynomials]]],
		First[WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, "Polynomials"]}, x^2 + x], polynomials]]],
		First[TypeTheoryCheck[TypeTheoryTerm[2 + 3, polynomials]]]
	},
	{
		TypeSpecifier[{"Polynomials"} -> "Polynomials"],
		TypeSpecifier[{"Polynomials"} -> "Polynomials"],
		Function[{Typed[x, "Polynomials"]}, "polynomialAddition"["polynomialPower"[x, 2], x]],
		NonNegativeIntegers
	},
	TestID -> "An-operation-declared-to-overload-Plus-is-chosen-by-the-types"
]

VerificationTest[
	First[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[e, FormSpace[4]], Typed[g, FormSpace[6]]}, e^3 + g^2], polynomials]]],
	TypeSpecifier[{FormSpace[4]} -> TypeSpecifier[{FormSpace[6]} -> FormSpace[12]]],
	TestID -> "An-overload-with-an-implicit-argument-is-solved-through-computation"
]

VerificationTest[
	FreeQ[First[ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, "Polynomials"]}, {x^2 + x, -x}], polynomials]]]], "\"polynomialAddition\"" | "\"polynomialPower\"" | "\"polynomialNegation\""],
	True,
	TestID -> "An-overloading-constant-shows-as-its-operation"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[polynomials], _Success],
		Normal[TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[polynomials]]] === Normal[polynomials],
		polynomials["polynomialAddition"],
		TypeTheoryEnvironment[{TypeTheoryAxiom["thing", Naturals, "Overloads" -> Sin]}]["Tag"]
	},
	{True, True, TypeTheoryAxiom["polynomialAddition", TypeSpecifier[{"Polynomials"} -> TypeSpecifier[{"Polynomials"} -> "Polynomials"]], "Overloads" -> Plus], "OverloadedOperation"},
	TestID -> "Overloads-replay-read-back-and-name-only-the-operations-that-take-them"
]
