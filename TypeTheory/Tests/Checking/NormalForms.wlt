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

(* A natural number over a base that does not compute has one normal form, the base and a number, however it is written:
   a sum with a number is not reduced a successor at a time, which k + 1000000 would be a million calls deep, and a
   successor adds 1 to the number. The normal form is equal to the term by computation, and is its own normal form. A sum
   with the number on the left stays as it is: the addition recurses on its second argument. *)
VerificationTest[
	With[{prelude = TypeTheoryEnvironment["Prelude"]},
		Map[
			Function[term, With[{normal = NormalForm[term]}, {First[normal], NormalForm[normal] === normal, DefinitionallyEqualQ[term, normal]}]],
			{
				TypeTheoryTerm[Function[{Typed[k, NonNegativeIntegers]}, k + 1000000], prelude],
				TypeTheoryTerm[Function[{Typed[k, NonNegativeIntegers]}, "successor"["successor"["successor"[k]]]], prelude],
				TypeTheoryTerm[Function[{Typed[b, NonNegativeIntegers]}, (b + 2) + 3], prelude],
				TypeTheoryTerm[Function[{Typed[b, NonNegativeIntegers]}, "successor"[b + 2] + 3], prelude],
				TypeTheoryTerm[Function[{Typed[k, NonNegativeIntegers], Typed[j, NonNegativeIntegers]}, k + (j + 1000000)], prelude],
				TypeTheoryTerm[4 + 1000000, prelude],
				TypeTheoryTerm["successor"["successor"["zero"]], prelude],
				TypeTheoryTerm[Function[{Typed[k, NonNegativeIntegers]}, 1000000 + k], prelude]
			}
		]
	],
	{
		{HoldPattern[Function[{Typed[k, NonNegativeIntegers]}, k + 1000000]], True, True},
		{HoldPattern[Function[{Typed[k, NonNegativeIntegers]}, k + 3]], True, True},
		{HoldPattern[Function[{Typed[b, NonNegativeIntegers]}, b + 5]], True, True},
		{HoldPattern[Function[{Typed[b, NonNegativeIntegers]}, b + 6]], True, True},
		{HoldPattern[Function[{Typed[k, NonNegativeIntegers], Typed[j, NonNegativeIntegers]}, (k + j) + 1000000]], True, True},
		{1000004, True, True},
		{2, True, True},
		{HoldPattern[Function[{Typed[k, NonNegativeIntegers]}, 1000000 + k]], True, True}
	},
	SameTest -> MatchQ,
	TimeConstraint -> 120,
	TestID -> "A-natural-number-over-a-stuck-base-has-one-normal-form-the-base-and-a-number"
]

(* where no addition is registered there is no sum to write an offset with, and a successor stays a successor *)
VerificationTest[
	With[{prelude = TypeTheoryEnvironment["Prelude"]},
		With[{bare = Append[
				TypeTheoryEnvironment[TypeTheoryEnvironment[], TakeWhile[Normal[prelude], Function[declaration, Head[declaration] =!= TypeTheoryNaturalNumbers]]],
				TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor"]
			]},
			{
				Information[bare, "NaturalNumbers"]["Operations"],
				First[NormalForm[TypeTheoryTerm[Function[{Typed[k, NonNegativeIntegers]}, "successor"["successor"[k]]], bare]]]
			}
		]
	],
	{<||>, HoldPattern[Function[{Typed[k, NonNegativeIntegers]}, "successor"["successor"[k]]]]},
	SameTest -> MatchQ,
	TestID -> "Without-a-registered-addition-a-successor-stays-a-successor"
]

(* the spine is taken of the weak head normal form of the whole application, so a function defined on a literal still
   computes to its value, on its own and as an argument of a sum, m + 6, six successors of m *)
VerificationTest[
	With[{doubling = TypeTheoryEnvironment[TypeTheoryEnvironment["Prelude"], {TypeTheoryDefinition["twice", Function[{Typed[k, NonNegativeIntegers]}, k + k]]}]},
		{
			NormalForm[TypeTheoryTerm["twice"[3], doubling]] === TypeTheoryTerm[6, doubling],
			With[{normal = NormalForm[TypeTheoryTerm[Typed[m, NonNegativeIntegers] |-> m + "twice"[3], doubling]]},
				FreeQ[normal, "twice"] && DefinitionallyEqualQ[normal, TypeTheoryTerm[Typed[m, NonNegativeIntegers] |-> m + 6, doubling]]
			],
			Last[withNormalFormCheck[NormalForm[TypeTheoryTerm[Typed[m, NonNegativeIntegers] |-> "twice"[m] + "twice"[2], doubling]]]]
		}
	],
	{True, True, {}},
	TestID -> "A-defined-function-on-a-literal-still-computes-to-its-value"
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
