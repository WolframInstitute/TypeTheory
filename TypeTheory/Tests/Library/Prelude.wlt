(* ::Package:: *)

(* Tests for Library/Prelude.wl: the declarations of the prelude and the theorems proved from the
   recursors. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]


VerificationTest[
	{Head[prelude], prelude === TypeTheoryEnvironment["Prelude"]},
	{TypeTheoryEnvironment, True},
	TestID -> "The-prelude-is-built-once"
]

VerificationTest[
	Complement[
		{
			True, False, Not, And, Or, Equal, Exists, NonNegativeIntegers, Plus,
			FalseElimination, AndEliminationLeft, AndEliminationRight,
			EqualitySymmetry, EqualityTransitivity, EqualityCongruence, EqualitySubstitution
		},
		Keys[prelude]
	],
	{},
	TestID -> "The-prelude-declares-logic-equality-and-the-natural-numbers"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[EqualitySymmetry[EqualityReflexivity[3]], prelude], TypeTheoryTerm[3 == 3]],
		TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, False]}, FalseElimination[h]], prelude], TypeTheoryTerm[Implies[False, 1 == 2]]],
		TypeTheoryCheck[TypeTheoryTerm[AndEliminationRight[AndIntroduction[TrueIntroduction, EqualityReflexivity[2]]], prelude], TypeTheoryTerm[1 + 1 == 2]],
		TypeTheoryCheck[TypeTheoryTerm[EqualityCongruence[NaturalNumberSuccessor, EqualityReflexivity[2]], prelude], TypeTheoryTerm[3 == 3]],
		TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x == 2]}, EqualitySubstitution[EqualitySymmetry[h], EqualityReflexivity[2]]], prelude],
			TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == 2, x == 2]]]
		]
	},
	{True, True, True, True, True},
	TestID -> "The-prelude-theorems-apply"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[OrIntroductionLeft[TrueIntroduction], prelude], TypeTheoryTerm[Or[True, False]]],
		TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight[TrueIntroduction], prelude], TypeTheoryTerm[Or[False, True]]]
	},
	{True, True},
	TestID -> "Disjunction-introduction"
]
