(* ::Package:: *)

(* Tests for Checking/NaturalNumbers.wl: only an inductive type of the right shape, with addition
   defined exactly by recursion on its second argument, can be registered as the natural numbers. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

(* the prelude up to, and without, its natural numbers *)
beforeNaturalNumbers = TypeTheoryEnvironment[TakeWhile[Normal[prelude], Function[declaration, Head[declaration] =!= TypeTheoryNaturalNumbers]]]


VerificationTest[
	Information[Append[beforeNaturalNumbers, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor]], "NaturalNumbers"],
	<|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Addition" -> None|>,
	TestID -> "The-natural-numbers-register-without-addition"
]

VerificationTest[
	First @ Append[beforeNaturalNumbers, TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberSuccessor, NaturalNumberZero]],
	"InvalidNaturalNumbers",
	TestID -> "Zero-and-successor-cannot-be-swapped"
]

VerificationTest[
	First @ TypeTheoryEnvironment[beforeNaturalNumbers, {
		TypeTheoryDefinition[
			FirstNumber,
			Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
		],
		TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, FirstNumber]
	}],
	"InvalidNaturalNumbers",
	TestID -> "Only-recursive-addition-can-be-registered"
]

VerificationTest[
	First @ TypeTheoryEnvironment[{
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
