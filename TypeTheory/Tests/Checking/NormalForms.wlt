(* ::Package:: *)

(* Tests for normal forms: a normal form holds no beta-redex, a function applied to an argument, since a normal form is
   a term that reduces no further. withNormalFormCheck collects every normal form NormalForm computes that does; these
   tests run the files that compute normal forms under it, and expect none.
   Run with: TestReport["TypeTheory/Tests/Checking/NormalForms.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

withNormalFormCheck = Symbol["WolframInstitute`TypeTheory`PackageScope`withNormalFormCheck"]


(* a sum stuck on its second argument stays a sum: its function, Plus[0], is not unfolded on its own into a function
   applied to n *)
VerificationTest[
	{
		ToString[NormalForm[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n]]], InputForm] === ToString[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], TypeTheoryEnvironment["Prelude"]], InputForm],
		Last[withNormalFormCheck[NormalForm[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> (0 + n) + 2 n]]]]
	},
	{True, {}},
	TestID -> "A-sum-stuck-on-its-second-argument-stays-a-sum"
]

(* every normal form the files that compute them compute *)
VerificationTest[
	Replace[
		withNormalFormCheck[
			Function[file, TestReport[FileNameJoin[{Directory[], "TypeTheory", "Tests", file}]]["TestsFailedCount"]] /@ {
				"Checking/Cubical.wlt",
				"Checking/InductiveTypes.wlt",
				"Checking/Declarations.wlt",
				"Checking/Quotients.wlt",
				"Checking/NaturalNumbers.wlt",
				"Checking/Queries.wlt",
				"Checking/RewriteRules.wlt",
				"Checking/TypeChecking.wlt",
				"Elaboration/Overloads.wlt",
				"Elaboration/Elaboration.wlt",
				"Elaboration/Instances.wlt",
				"Elaboration/WolframDefinitions.wlt",
				"Library/Cubical.wlt",
				"Library/Rationals.wlt",
				"Library/Integers.wlt",
				"Library/Prelude.wlt",
				"Library/HomotopyTypeTheory.wlt",
				"Library/WolframLanguage.wlt",
				"Terms/SurfaceSyntax.wlt"
			}
		],
		{failed_, redexes_} :> {Total[failed], Length[redexes]}
	],
	{0, 0},
	TestID -> "No-normal-form-the-suite-computes-holds-a-redex",
	TimeConstraint -> 900
]
