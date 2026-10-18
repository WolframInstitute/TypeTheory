(* ::Package:: *)

(* Tests for Elaboration/Elaboration.wl: implicit arguments, universe levels, binder types taken from the
   expected type, and the errors elaboration reports. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]


VerificationTest[
	TypeOf[TypeTheoryTerm[EqualityReflexivity[TrueIntroduction]]],
	TypeTheoryTerm[TrueIntroduction == TrueIntroduction],
	TestID -> "An-implicit-type-argument-is-inferred"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[EqualityReflexivity[NonNegativeIntegers]]],
	TypeTheoryTerm[NonNegativeIntegers == NonNegativeIntegers],
	TestID -> "A-universe-level-is-inferred"
]

VerificationTest[
	{TypeOf[TypeTheoryTerm[Subscript[EqualityReflexivity, 1][3]]], First @ TypeOf[TypeTheoryTerm[Subscript[EqualityReflexivity, 0][3]]]},
	{TypeTheoryTerm[3 == 3], "TypeMismatch"},
	TestID -> "Explicit-universe-levels-with-Subscript"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Typed[Function[{x}, x + 1], TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]]]],
	TypeTheoryTerm[TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]],
	TestID -> "A-binder-takes-its-type-from-the-expected-type"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[NonNegativeIntegers -> TypeUniverse[0]]],
	TypeTheoryTerm[TypeUniverse[1]],
	TestID -> "A-rule-is-a-function-type"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[1 + 2 + 3 + 4]],
	TypeTheoryTerm[NonNegativeIntegers],
	TestID -> "A-sum-of-several-terms-is-read-left-to-right"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4]]],
	TypeTheoryTerm[TypeUniverse[0]],
	TestID -> "Exists-takes-binders"
]

VerificationTest[
	TypeTheoryCheck[TypeTheoryTerm[ExistsIntroduction[2, EqualityReflexivity[4]]], TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4]]],
	True,
	TestID -> "A-witness-proves-an-existential-statement"
]

VerificationTest[
	First /@ {
		TypeOf[TypeTheoryTerm[Unknown]],
		TypeOf[TypeTheoryTerm[Function[{x}, x]]],
		TypeOf[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, EqualityReflexivity]]],
		TypeOf[TypeTheoryTerm[NaturalNumberZero[1]]]
	},
	{"ElaborationFailed", "ElaborationFailed", "UnsolvedImplicitArgument", "ElaborationFailed"},
	SameTest -> MatchQ,
	TestID -> "Elaboration-errors-are-Failures"
]
