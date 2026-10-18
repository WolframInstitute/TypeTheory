(* ::Package:: *)

(* Tests for Checking/Queries.wl: the public questions about terms, and checking a whole environment
   again from scratch, which catches forged records. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

constantReference = Symbol["WolframInstitute`TypeTheory`PackageScope`constantReference"]
lambdaAbstraction = Symbol["WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction"]
boundVariable = Symbol["WolframInstitute`TypeTheory`PackageScope`boundVariable"]

natural = constantReference[HoldComplete[NonNegativeIntegers], {}]
firstProjection = lambdaAbstraction[HoldComplete[m], natural, lambdaAbstraction[HoldComplete[n], natural, boundVariable[1], "Explicit"], "Explicit"]

(* the environment with one record changed *)
forge[TypeTheoryEnvironment[data_], name_HoldComplete, change_] := TypeTheoryEnvironment[MapAt[change, data, {"Constants", Key[name]}]]


VerificationTest[
	TypeOf[TypeTheoryTerm[AndIntroduction]],
	TypeTheoryTerm[ForAll[
		{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"]},
		Implies[\[FormalA], Implies[\[FormalB], \[FormalA] && \[FormalB]]]
	]],
	TestID -> "A-constant-has-its-declared-type"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[2 + 3], $TypeTheoryEnvironment],
	TypeTheoryTerm[NonNegativeIntegers],
	TestID -> "TypeOf-takes-an-environment"
]

VerificationTest[
	{TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]], TypeTheoryTerm[2 + 2 == 4]], First @ TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]], TypeTheoryTerm[2 + 2 == 5]]},
	{True, "TypeMismatch"},
	TestID -> "TypeTheoryCheck-checks-a-term-against-a-type"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[True], TypeTheoryTerm[NotATerm]],
	False,
	TestID -> "DefinitionallyEqualQ-answers-False-for-a-term-that-does-not-check"
]

VerificationTest[
	Head /@ {TypeTheoryCheck[3], WeakHeadNormalForm[3], DefinitionallyEqualQ[1, 2]},
	{TypeTheoryCheck, WeakHeadNormalForm, DefinitionallyEqualQ},
	TestID -> "Arguments-that-are-not-terms-stay-unevaluated"
]


(* === checking an environment === *)

VerificationTest[
	TypeTheoryCheck[$TypeTheoryEnvironment],
	True,
	TestID -> "The-prelude-checks-from-scratch"
]

VerificationTest[
	First @ TypeTheoryCheck[forge[$TypeTheoryEnvironment, HoldComplete[FalseElimination], Function[record, Append[record, "Type" -> constantReference[HoldComplete[False], {}]]]]],
	"TypeMismatch",
	TestID -> "A-forged-theorem-statement-is-caught"
]

VerificationTest[
	First @ TypeTheoryCheck[forge[$TypeTheoryEnvironment, HoldComplete[InductiveRecursor[Or]], Function[record, Append[record, "EliminationUniverse" -> True]]]],
	"DeclarationMismatch",
	TestID -> "A-forged-recursor-is-caught"
]

(* addition forged as the first projection: well typed, so only the natural number check can catch it *)
VerificationTest[
	First @ TypeTheoryCheck[forge[$TypeTheoryEnvironment, HoldComplete[Plus], Function[record, Append[record, "Value" -> firstProjection]]]],
	"InvalidNaturalNumbers",
	TestID -> "A-forged-addition-is-caught"
]
