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
			"rationalAdditionCommutativity", "rationalAdditionAssociativity", "rationalAdditionZero", "rationalAdditionNegation",
			"rationalMultiplicationCommutativity", "rationalMultiplicationAssociativity", "rationalMultiplicationOne", "rationalDistributivity",
			"rationalSubtractionNegation", "rationalOfIntegerAddition", "rationalOfIntegerMultiplication", "rationalMultiplicationInverse",
			"rationalInverseZero", "rationalLessEqualReflexivity", "rationalSquareNonnegative"
		},
		MatchQ[rationals["rationalEqualityDecidable"], TypeTheoryDefinition[__, "Instance" -> True]]
	},
	{True, {"propositionalExtensionality", "quotientSoundness", "choice"}, ConstantArray[True, 15], True},
	TestID -> "The-rationals-and-their-laws-check"
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm[Function[{Typed[x, Rationals], Typed[y, Rationals]}, x + y x - y / 2], rationals]],
			TypeTheoryTerm[TypeSpecifier[{Rationals, Rationals} -> Rationals], rationals]
		],
		TypeTheoryType[TypeTheoryTerm[Typed[1/2, Rationals], rationals]],
		TypeTheoryType[TypeTheoryTerm[2 + 3, rationals]],
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm[Function[{Typed[a, Integers], Typed[x, Rationals]}, a + x], rationals]],
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
			TypeTheoryCheck[TypeTheoryTerm["rationalMultiplicationInverse", rationals]],
			TypeTheoryTerm[ForAll[{Typed[x, Rationals]}, Implies[Not[x == 0], x x^-1 == 1]], rationals]
		],
		DefinitionallyEqualQ[TypeTheoryCheck[TypeTheoryTerm["rationalInverseZero", rationals]], TypeTheoryTerm[Typed[0^-1, Rationals] == 0, rationals]],
		DefinitionallyEqualQ[TypeTheoryCheck[TypeTheoryTerm["rationalSquareNonnegative", rationals]], TypeTheoryTerm[ForAll[{Typed[x, Rationals]}, 0 <= x x], rationals]]
	},
	{True, True, True},
	TestID -> "The-inverse-and-the-order"
]

(* a natural number among the rationals is cast to an integer and then to a rational, which a goal shows as
   Lean does, ↑↑n *)
VerificationTest[
	Cases[ToBoxes[TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Typed[n, Rationals] + 0 == n], rationals]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes, TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, _], Infinity],
	{TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, "RowDefault"], TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, "RowDefault"]},
	TestID -> "A-natural-number-among-the-rationals-shows-as-Lean-shows-it"
]

(* a literal fraction among the factors of a product shows as the fraction, 1/2 (x + y) and 1/2 1, which keeps its
   factor 1; after a number it is parenthesized, 5 (2/3), so it does not read as a mixed number *)
VerificationTest[
	With[
		{
			parenthesized = TemplateBox[{"\"(\"", FractionBox["2", "3"], "\")\""}, "RowDefault"],
			one = ToBoxes[TypeTheoryCheck[TypeTheoryTerm["rationalMultiplicationOne"[1/2], rationals]]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes,
			swapped = ToBoxes[TypeTheoryCheck[TypeTheoryTerm["rationalMultiplicationCommutativity"[2/3, 5], rationals]]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes
		},
		{
			Cases[one, RowBox[{FractionBox["1", "2"], " ", "1"}], Infinity] =!= {},
			Length[Cases[swapped, parenthesized, Infinity]],
			Cases[swapped, RowBox[{FractionBox["2", "3"], " ", "5"}], Infinity] =!= {}
		}
	],
	{True, 1, True},
	TestID -> "A-literal-fraction-among-the-factors-of-a-product-shows-bare-but-after-a-number"
]
