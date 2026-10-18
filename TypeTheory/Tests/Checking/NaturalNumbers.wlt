(* ::Package:: *)

(* Tests for Checking/NaturalNumbers.wl: only an inductive type of the right shape can be registered as
   the natural numbers, and only operations of the right types; the kernel computes those on literals. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

(* the prelude up to, and without, its natural numbers *)
beforeNaturalNumbers = TypeTheoryEnvironment[TypeTheoryEnvironment[], TakeWhile[Normal[prelude], Function[declaration, Head[declaration] =!= TypeTheoryNaturalNumbers]]]


VerificationTest[
	Information[Append[beforeNaturalNumbers, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor]], "NaturalNumbers"],
	<|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Operations" -> <||>|>,
	TestID -> "The-natural-numbers-register-without-operations"
]

VerificationTest[
	First @ Append[beforeNaturalNumbers, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberSuccessor, NaturalNumberZero]],
	"InvalidNaturalNumbers",
	TestID -> "Zero-and-successor-cannot-be-swapped"
]

VerificationTest[
	First /@ {
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, <|"Quotient" -> NaturalNumberPredecessor|>]],
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, <|"Modulo" -> Times|>]],
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, <|"Addition" -> Times|>]],
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, <|"GCD" -> Times|>]]
	},
	{"InvalidNaturalNumberOperation", "InvalidNaturalNumberOperation", "InvalidNaturalNumberOperation", "InvalidNaturalNumberOperation"},
	TestID -> "An-operation-needs-the-type-of-a-role-that-is-free"
]

VerificationTest[
	First /@ {
		WeakHeadNormalForm[TypeTheoryTerm[2^64 - 1]],
		WeakHeadNormalForm[TypeTheoryTerm[123456789 * 987654321]],
		WeakHeadNormalForm[TypeTheoryTerm[3 - 5]],
		WeakHeadNormalForm[TypeTheoryTerm[0^0]],
		WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n * 2][2^100]]]
	},
	{18446744073709551615, 121932631112635269, 0, 1, 2535301200456458802993406410752},
	TestID -> "The-prelude-computes-its-arithmetic-on-literals"
]

(* the comparison of natural numbers on Booleans, registered after the prelude by the alias Naturals *)
withEquality = TypeTheoryEnvironment[prelude, {
	TypeTheoryDefinition[
		NaturalNumberEqual,
		Function[{Typed[m, Naturals], Typed[n, Naturals]},
			InductiveRecursor[Naturals][Function[{Typed[t, Naturals]}, Booleans], "true", Function[{Typed[k, Naturals], Typed[r, Booleans]}, "false"], (m - n) + (n - m)]
		]
	],
	TypeTheoryNaturalNumbers[Naturals, NaturalNumberZero, NaturalNumberSuccessor, <|"Equal" -> NaturalNumberEqual|>]
}]

VerificationTest[
	{
		First /@ {WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberEqual[2^70, 2^70], withEquality]], WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberEqual[2^70, 2^70 + 1], withEquality]]},
		Information[withEquality, "NaturalNumbers"]["Operations"]["Equal"],
		Count[Normal[withEquality], _TypeTheoryNaturalNumbers],
		MatchQ[TypeTheoryCheck[withEquality], _Success]
	},
	{{"true", "false"}, NaturalNumberEqual, 3, True},
	TestID -> "A-later-registration-adds-an-operation-with-Boolean-values"
]

(* the kernel trusts a registration: here a projection registered as addition computes as addition *)
VerificationTest[
	First @ WeakHeadNormalForm[TypeTheoryTerm[FirstNumber[2, 3], TypeTheoryEnvironment[beforeNaturalNumbers, {
		TypeTheoryDefinition[
			FirstNumber,
			Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
		],
		TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, FirstNumber]
	}]]],
	5,
	TestID -> "A-registered-operation-is-trusted"
]

VerificationTest[
	First @ TypeTheoryEnvironment[TypeTheoryEnvironment[], {
		TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
		TypeTheoryNaturalNumbers[Bit, BitZero, BitOne]
	}],
	"InvalidNaturalNumbers",
	TestID -> "A-type-without-a-successor-cannot-be-registered"
]

VerificationTest[
	First @ Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor]],
	"NaturalNumbersRegistered",
	TestID -> "The-natural-numbers-are-registered-once"
]

VerificationTest[
	First @ TypeOf[TypeTheoryTerm[3, beforeNaturalNumbers]],
	"ElaborationFailed",
	TestID -> "Literals-need-natural-numbers"
]
