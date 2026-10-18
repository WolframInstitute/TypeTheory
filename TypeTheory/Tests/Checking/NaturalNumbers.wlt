(* ::Package:: *)

(* Tests for Checking/NaturalNumbers.wl: only an inductive type of the right shape, with addition
   defined exactly by recursion on its second argument, can be registered as the natural numbers. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

registerNaturalNumbers = Symbol["WolframInstitute`TypeTheory`PackageScope`registerNaturalNumbers"]
catchKernelFailure = Symbol["WolframInstitute`TypeTheory`PackageScope`catchKernelFailure"]

settings[type_, zero_, successor_, addition_] := <|"Type" -> type, "Zero" -> zero, "Successor" -> successor, "Addition" -> addition|>


VerificationTest[
	Head @ catchKernelFailure @ registerNaturalNumbers[
		$TypeTheoryEnvironment,
		settings[HoldComplete[NonNegativeIntegers], HoldComplete[NaturalNumberZero], HoldComplete[NaturalNumberSuccessor], HoldComplete[Plus]]
	],
	TypeTheoryEnvironment,
	TestID -> "The-prelude-natural-numbers-register"
]

VerificationTest[
	First @ catchKernelFailure @ registerNaturalNumbers[
		$TypeTheoryEnvironment,
		settings[HoldComplete[NonNegativeIntegers], HoldComplete[NaturalNumberSuccessor], HoldComplete[NaturalNumberZero], HoldComplete[Plus]]
	],
	"InvalidNaturalNumbers",
	TestID -> "Zero-and-successor-cannot-be-swapped"
]

VerificationTest[
	Block[{$TypeTheoryEnvironment = $TypeTheoryEnvironment},
		DeclareDefinition[
			FirstNumber,
			Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
		];
		First @ catchKernelFailure @ registerNaturalNumbers[
			$TypeTheoryEnvironment,
			settings[HoldComplete[NonNegativeIntegers], HoldComplete[NaturalNumberZero], HoldComplete[NaturalNumberSuccessor], HoldComplete[FirstNumber]]
		]
	],
	"InvalidNaturalNumbers",
	TestID -> "Only-recursive-addition-can-be-registered"
]

VerificationTest[
	Block[{$TypeTheoryEnvironment = $TypeTheoryEnvironment},
		DeclareInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}];
		First @ catchKernelFailure @ registerNaturalNumbers[$TypeTheoryEnvironment, settings[HoldComplete[Bit], HoldComplete[BitZero], HoldComplete[BitOne], None]]
	],
	"InvalidNaturalNumbers",
	TestID -> "A-type-without-a-successor-cannot-be-registered"
]
