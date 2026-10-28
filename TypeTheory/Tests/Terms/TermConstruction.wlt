(* ::Package:: *)

(* Tests for the construction check of Terms/CoreTerms.wl. The composite heads hold their parts completely, so a
   term is built from parts computed first: a call or a Module variable written inside a composite head stays
   there. The check catches a construction that leaves one; these tests run the forged tests, the random
   substitutions and a slice of the suite under it, and expect none.
   Run with: TestReport["TypeTheory/Tests/Terms/TermConstruction.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

$scope = "WolframInstitute`TypeTheory`PackageScope`"

withTermConstructionCheck = Symbol[$scope <> "withTermConstructionCheck"]

(* the places where a construction left a part uncomputed; data the check does not know, as the pending
   abstraction of a proof under construction, is no failure *)
uncomputedPlaces[sites_Association] := Select[Keys[sites], MatchQ[{"Uncomputed", ___}]]


VerificationTest[
	With[{application = Symbol[$scope <> "application"], freeVariable = Symbol[$scope <> "freeVariable"]},
		Replace[
			withTermConstructionCheck[Module[{variable = freeVariable[1]}, application[variable, variable]]],
			{term_, sites_} :> {term === application[freeVariable[1], freeVariable[1]], Length[uncomputedPlaces[sites]]}
		]
	],
	{True, 1},
	TestID -> "A-construction-that-leaves-a-variable-is-caught-and-built-from-its-value"
]

VerificationTest[
	With[{heads = Symbol[$scope <> #]& /@ {"application", "lambdaAbstraction", "dependentFunctionType", "localDefinition", "projection", "cubicalSystem"}},
		{Union[Attributes /@ heads], Length /@ DownValues /@ heads}
	],
	{{{HoldAllComplete}}, {0, 0, 0, 0, 0, 0}},
	TestID -> "The-composite-heads-hold-their-parts-and-the-check-is-off-by-default"
]

(* the forged declarations and the prelude checked from scratch in Queries.wlt, the random substitutions in
   CoreTerms.wlt, and the tactics, the cubical terms and the quotients of other files *)
VerificationTest[
	Replace[
		withTermConstructionCheck[
			Function[file, TestReport[FileNameJoin[{Directory[], "TypeTheory", "Tests", file}]]["TestsFailedCount"]] /@ {
				"Terms/CoreTerms.wlt",
				"Checking/Queries.wlt",
				"Checking/InductiveTypes.wlt",
				"Checking/Cubical.wlt",
				"Checking/Quotients.wlt",
				"Elaboration/Elaboration.wlt",
				"Proofs/ProofStates.wlt",
				"Proofs/Ring.wlt"
			}
		],
		{failed_, sites_} :> {failed, uncomputedPlaces[sites]}
	],
	{{0, 0, 0, 0, 0, 0, 0, 0}, {}},
	TestID -> "Forged-random-and-suite-tests-build-every-term-from-computed-parts",
	TimeConstraint -> 600
]
