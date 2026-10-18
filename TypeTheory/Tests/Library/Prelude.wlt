(* ::Package:: *)

(* Tests for Library/Prelude.wl: the declarations of the default environment and the theorems proved
   from the recursors. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]


VerificationTest[
	Head[$TypeTheoryEnvironment],
	TypeTheoryEnvironment,
	TestID -> "The-prelude-builds"
]

VerificationTest[
	Complement[
		{
			HoldForm[True], HoldForm[False], HoldForm[Not], HoldForm[And], HoldForm[Or], HoldForm[Equal], HoldForm[Exists], HoldForm[NonNegativeIntegers], HoldForm[Plus],
			HoldForm[FalseElimination], HoldForm[AndEliminationLeft], HoldForm[AndEliminationRight],
			HoldForm[EqualitySymmetry], HoldForm[EqualityTransitivity], HoldForm[EqualityCongruence], HoldForm[EqualitySubstitution]
		},
		$TypeTheoryEnvironment["Constants"]
	],
	{},
	TestID -> "The-prelude-declares-logic-equality-and-the-natural-numbers"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[EqualitySymmetry[EqualityReflexivity[3]]], TypeTheoryTerm[3 == 3]],
		TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, False]}, FalseElimination[h]]], TypeTheoryTerm[Implies[False, 1 == 2]]],
		TypeTheoryCheck[TypeTheoryTerm[AndEliminationRight[AndIntroduction[TrueIntroduction, EqualityReflexivity[2]]]], TypeTheoryTerm[1 + 1 == 2]],
		TypeTheoryCheck[TypeTheoryTerm[EqualityCongruence[NaturalNumberSuccessor, EqualityReflexivity[2]]], TypeTheoryTerm[3 == 3]],
		TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x == 2]}, EqualitySubstitution[EqualitySymmetry[h], EqualityReflexivity[2]]]],
			TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == 2, x == 2]]]
		]
	},
	{True, True, True, True, True},
	TestID -> "The-prelude-theorems-apply"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[OrIntroductionLeft[TrueIntroduction]], TypeTheoryTerm[Or[True, False]]],
		TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight[TrueIntroduction]], TypeTheoryTerm[Or[False, True]]]
	},
	{True, True},
	TestID -> "Disjunction-introduction"
]
