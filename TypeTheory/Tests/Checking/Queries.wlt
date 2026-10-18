(* ::Package:: *)

(* Tests for Checking/Queries.wl: the questions about terms, environments as associations, and checking
   a whole environment again from scratch, which catches records changed by hand. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

constantReference = Symbol["WolframInstitute`TypeTheory`PackageScope`constantReference"]
lambdaAbstraction = Symbol["WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction"]
boundVariable = Symbol["WolframInstitute`TypeTheory`PackageScope`boundVariable"]

natural = constantReference[HoldComplete[NonNegativeIntegers], {}]
firstProjection = lambdaAbstraction[HoldComplete[m], natural, lambdaAbstraction[HoldComplete[n], natural, boundVariable[1], "Explicit"], "Explicit"]

(* a copy of the environment's store with one record changed by hand *)
forge[TypeTheoryEnvironment[store_Symbol], name_HoldComplete, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy[name] = change[copy[name]];
	TypeTheoryEnvironment[copy]
]


VerificationTest[
	TypeOf[TypeTheoryTerm[AndIntroduction, prelude]],
	With[{a = WolframInstitute`TypeTheory`Library`Prelude`Private`a, b = WolframInstitute`TypeTheory`Library`Prelude`Private`b},
		TypeTheoryTerm[
			ForAll[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"]}, Implies[a, Implies[b, a && b]]],
			prelude
		]
	],
	TestID -> "A-constant-has-its-declared-type"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[2 + 3], prelude],
	TypeTheoryTerm[NonNegativeIntegers, prelude],
	TestID -> "TypeOf-takes-an-environment"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4], prelude], TypeTheoryTerm[2 + 2 == 4]],
		First @ TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4], prelude], TypeTheoryTerm[2 + 2 == 5]]
	},
	{True, "TypeMismatch"},
	TestID -> "TypeTheoryCheck-checks-a-term-against-a-type"
]

VerificationTest[
	First @ TypeTheoryCheck[TypeTheoryTerm[True, prelude], TypeTheoryTerm[TypeUniverse[0], Append[prelude, TypeTheoryAxiom[Extra, True]]]],
	"DifferentEnvironments",
	TestID -> "Two-terms-must-share-their-environment"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[True, prelude], TypeTheoryTerm[NotATerm, prelude]],
	False,
	TestID -> "DefinitionallyEqualQ-answers-False-for-a-term-that-does-not-check"
]

VerificationTest[
	Head /@ {TypeTheoryCheck[3], WeakHeadNormalForm[3], DefinitionallyEqualQ[1, 2]},
	{TypeTheoryCheck, WeakHeadNormalForm, DefinitionallyEqualQ},
	TestID -> "Arguments-that-are-not-terms-stay-unevaluated"
]


(* === environments as associations === *)

VerificationTest[
	{Length[prelude], Take[Keys[prelude], 3], KeyExistsQ[prelude, Plus], KeyExistsQ[prelude, Divide]},
	{89, {True, TrueIntroduction, InductiveRecursor[True]}, True, False},
	TestID -> "Keys-Length-and-KeyExistsQ"
]

VerificationTest[
	{prelude[NaturalNumberSuccessor] === prelude[NonNegativeIntegers], Head[prelude[Plus]], prelude[Divide]},
	{True, TypeTheoryDefinition, Missing["KeyAbsent", Divide]},
	TestID -> "Indexing-gives-the-declaration-of-a-constant"
]

VerificationTest[
	{Information[prelude, "Kinds"], Information[prelude, "Axioms"], Information[prelude, "NaturalNumbers"]},
	{
		<|"InductiveType" -> 9, "Constructor" -> 11, "Recursor" -> 9, "Definition" -> 12, "Theorem" -> 48|>,
		{},
		<|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Addition" -> Plus|>
	},
	TestID -> "Information-about-an-environment"
]

VerificationTest[
	With[{rebuilt = TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[prelude]]}, {Keys[rebuilt] === Keys[prelude], TypeTheoryCheck[rebuilt]}],
	{True, True},
	TestID -> "Normal-gives-the-declarations-to-rebuild-an-environment-from"
]


(* === checking an environment === *)

VerificationTest[
	TypeTheoryCheck[prelude],
	True,
	TestID -> "The-prelude-checks-from-scratch"
]

VerificationTest[
	First @ TypeTheoryCheck[forge[prelude, HoldComplete[FalseElimination], Function[record, Append[record, "Type" -> constantReference[HoldComplete[False], {}]]]]],
	"TypeMismatch",
	TestID -> "A-forged-theorem-statement-is-caught"
]

VerificationTest[
	First @ TypeTheoryCheck[forge[prelude, HoldComplete[InductiveRecursor[Or]], Function[record, Append[record, "EliminationUniverse" -> True]]]],
	"DeclarationMismatch",
	TestID -> "A-forged-recursor-is-caught"
]

(* addition forged as the first projection: well typed, so only the natural number check can catch it *)
VerificationTest[
	First @ TypeTheoryCheck[forge[prelude, HoldComplete[Plus], Function[record, Append[record, "Value" -> firstProjection]]]],
	"InvalidNaturalNumbers",
	TestID -> "A-forged-addition-is-caught"
]
