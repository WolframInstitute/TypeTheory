(* ::Package:: *)

(* Tests for Library/Rationals.wl: the rationals as a quotient of pairs of an integer and a natural number,
   their operations lifted from pairs, the laws of a commutative ring and the inverse proved by the
   tactics, decisions of equations by computation, and the arithmetic notation read as the rationals'
   where the types say so. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

rationals = TypeTheoryEnvironment["Rationals"]


VerificationTest[
	{
		MatchQ[TypeTheoryCheck[rationals], _Success],
		Information[rationals, "Axioms"],
		Function[name, MatchQ[rationals[name], TypeTheoryTheorem[__]]] /@ {
			RationalAdditionCommutativity, RationalAdditionAssociativity, RationalAdditionZero, RationalAdditionNegation,
			RationalMultiplicationCommutativity, RationalMultiplicationAssociativity, RationalMultiplicationOne, RationalDistributivity,
			RationalSubtractionNegation, RationalOfIntegerAddition, RationalOfIntegerMultiplication, RationalMultiplicationInverse,
			RationalInverseZero, RationalLessEqualReflexivity, RationalSquareNonnegative
		},
		MatchQ[rationals[RationalEqualityDecidable], TypeTheoryDefinition[__, "Instance" -> True]]
	},
	{True, {PropositionalExtensionality, QuotientSoundness, Choice}, ConstantArray[True, 15], True},
	TestID -> "The-rationals-and-their-laws-check"
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeOf[TypeTheoryTerm[Function[{Typed[x, Rationals], Typed[y, Rationals]}, x + y x - y / 2], rationals]],
			TypeTheoryTerm[TypeSpecifier[{Rationals, Rationals} -> Rationals], rationals]
		],
		TypeOf[TypeTheoryTerm[Typed[1/2, Rationals], rationals]],
		TypeOf[TypeTheoryTerm[2 + 3, rationals]],
		DefinitionallyEqualQ[
			TypeOf[TypeTheoryTerm[Function[{Typed[a, Integers], Typed[x, Rationals]}, a + x], rationals]],
			TypeTheoryTerm[TypeSpecifier[{Integers, Rationals} -> Rationals], rationals]
		]
	},
	{True, TypeTheoryTerm[Rationals, rationals], TypeTheoryTerm[NonNegativeIntegers, rationals], True},
	TestID -> "Arithmetic-is-the-rationals'-where-the-types-say-so"
]

VerificationTest[
	{
		TypeTheoryProof[Typed[1/2 + 1/3, Rationals] == 5/6, rationals, {TypeTheoryTactic["Decide"]}]["Goals"],
		TypeTheoryProof[Typed[(2/3)^-1, Rationals] == 3/2, rationals, {TypeTheoryTactic["Decide"]}]["Goals"],
		TypeTheoryProof[Typed[-3/4 * 4, Rationals] == -3, rationals, {TypeTheoryTactic["Decide"]}]["Goals"],
		WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[1/2, Rationals] == 1/3], rationals]]
	},
	{{}, {}, {}, TypeTheoryTerm["false", rationals]},
	TestID -> "Equations-of-rationals-are-decided-by-computation"
]

VerificationTest[
	With[
		{
			difference = TypeTheoryProof[ForAll[{Typed[x, Rationals]}, (x + 1) (x - 1) == x^2 - 1], rationals, {
				TypeTheoryTactic["Introduce", x],
				TypeTheoryTactic["Ring"]
			}],
			fractions = TypeTheoryProof[ForAll[{Typed[x, Rationals]}, x / 2 + x / 3 == 5 x / 6], rationals, {
				TypeTheoryTactic["Introduce", x],
				TypeTheoryTactic["Ring"]
			}]
		},
		{difference["Goals"], fractions["Goals"], MatchQ[TypeTheoryEnvironment[rationals, {TypeTheoryTheorem[DifferenceOfSquares, difference], TypeTheoryTheorem[Fractions, fractions]}], _TypeTheoryEnvironment]}
	],
	{{}, {}, True},
	TestID -> "Ring-proves-identities-of-rationals-by-their-classes"
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationInverse, rationals]],
			TypeTheoryTerm[ForAll[{Typed[x, Rationals]}, Implies[Not[x == 0], x x^-1 == 1]], rationals]
		],
		DefinitionallyEqualQ[TypeTheoryCheck[TypeTheoryTerm[RationalInverseZero, rationals]], TypeTheoryTerm[Typed[0^-1, Rationals] == 0, rationals]],
		DefinitionallyEqualQ[TypeTheoryCheck[TypeTheoryTerm[RationalSquareNonnegative, rationals]], TypeTheoryTerm[ForAll[{Typed[x, Rationals]}, 0 <= x x], rationals]]
	},
	{True, True, True},
	TestID -> "The-inverse-and-the-order"
]

(* a natural number among the rationals is cast to an integer and then to a rational, which a goal shows as
   Lean does, ↑↑n *)
VerificationTest[
	Cases[ToBoxes[TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Typed[n, Rationals] + 0 == n], rationals]], TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, _], Infinity],
	{TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, "RowDefault"], TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, "RowDefault"]},
	TestID -> "A-natural-number-among-the-rationals-shows-as-Lean-shows-it"
]

(* a factor that is itself a fraction is parenthesized in a product: (1/2) 1 keeps its factor 1, which merged into one
   fraction it lost, and (2/3) 5 == 5 (2/3) shows which factor is which *)
VerificationTest[
	With[
		{
			parenthesized = TemplateBox[{"\"(\"", FractionBox["1", "2"], "\")\""}, "RowDefault"],
			one = ToBoxes[TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationOne[1/2], rationals]]],
			swapped = ToBoxes[TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationCommutativity[2/3, 5], rationals]]]
		},
		{
			Cases[one, RowBox[{parenthesized, " ", "1"}], Infinity] =!= {},
			Length[Cases[swapped, TemplateBox[{"\"(\"", FractionBox["2", "3"], "\")\""}, "RowDefault"], Infinity]]
		}
	],
	{True, 2},
	TestID -> "A-fraction-among-the-factors-of-a-product-is-parenthesized"
]
