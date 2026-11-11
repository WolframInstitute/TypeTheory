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
	{True, {"propositionalExtensionality", "quotientSoundness", "choice", ExpressionEvaluate}, ConstantArray[True, 15], True},
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
			TypeTheoryType[TypeTheoryTerm["rationalMultiplicationInverse", rationals]],
			TypeTheoryTerm[ForAll[{Typed[x, Rationals]}, Implies[Not[x == 0], x x^-1 == 1]], rationals]
		],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["rationalInverseZero", rationals]], TypeTheoryTerm[Typed[0^-1, Rationals] == 0, rationals]],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["rationalSquareNonnegative", rationals]], TypeTheoryTerm[ForAll[{Typed[x, Rationals]}, 0 <= x x], rationals]]
	},
	{True, True, True},
	TestID -> "The-inverse-and-the-order"
]

(* a natural number among the rationals is cast to an integer and then to a rational, which a goal shows with
   an arrow for each cast, ↑↑n *)
VerificationTest[
	Cases[ToBoxes[TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Typed[n, Rationals] + 0 == n], rationals]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes, TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, _], Infinity],
	{TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, "RowDefault"], TemplateBox[{"\"\[UpArrow]\[UpArrow]\"", "n"}, "RowDefault"]},
	TestID -> "A-natural-number-among-the-rationals-shows-an-arrow-for-each-cast"
]

(* a literal fraction among the factors of a product shows as the fraction, 1/2 (x + y) and 1/2 1, which keeps its
   factor 1; after a number it is parenthesized, 5 (2/3), so it does not read as a mixed number *)
VerificationTest[
	With[
		{
			parenthesized = TemplateBox[{"\"(\"", FractionBox["2", "3"], "\")\""}, "RowDefault"],
			one = ToBoxes[TypeTheoryType[TypeTheoryTerm["rationalMultiplicationOne"[1/2], rationals]]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes,
			swapped = ToBoxes[TypeTheoryType[TypeTheoryTerm["rationalMultiplicationCommutativity"[2/3, 5], rationals]]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes
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

(* The order of the rationals: x <= y where y - x is a nonnegative rational, one with a natural number over a positive
   one in its class. It is total, transitive and antisymmetric, sums keep it and so do products by a nonnegative
   rational; the laws rest on the soundness of quotients and on nothing classical. The strict order is the negation of
   the converse, and each way of that is a theorem. *)
VerificationTest[
	{
		Function[statement, With[{theorem = TypeTheoryTerm @@ {First[statement], rationals}, stated = TypeTheoryTerm @@ Append[Last[statement], rationals]},
			DefinitionallyEqualQ[TypeTheoryType[theorem], stated]
		]] /@ {
			{"rationalLessEqualTotality", HoldComplete[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x <= y || y <= x]]},
			{"rationalLessEqualTransitivity", HoldComplete[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, Implies[x <= y, Implies[y <= z, x <= z]]]]},
			{"rationalLessEqualAntisymmetry", HoldComplete[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x <= y, Implies[y <= x, x == y]]]]},
			{"rationalLessEqualAddition", HoldComplete[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, Implies[x <= y, x + z <= y + z]]]},
			{"rationalLessEqualScaling", HoldComplete[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, Implies[0 <= z, Implies[x <= y, x z <= y z]]]]},
			{"rationalNonnegativeMultiplication", HoldComplete[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[0 <= x, Implies[0 <= y, 0 <= x y]]]]},
			{"rationalLessOfNotLessEqual", HoldComplete[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[Not[y <= x], x < y]]]}
		},
		Function[name, KeySort[TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, rationals}]]] /@ {"rationalLessEqualTotality", "rationalLessEqualTransitivity", "rationalLessEqualScaling"},
		TypeTheoryProof[
			ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x <= y, x + 1 <= y + 1]],
			rationals,
			{"Introduce"[x, y, h], "Exact"["rationalLessEqualAddition"[x, y, 1, h]]}
		]["Goals"],
		TypeTheoryProof[
			ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[Not[x <= y], y <= x]],
			rationals,
			{"Introduce"[x, y, h], "Cases"["rationalLessEqualTotality"[x, y]], "Introduce"[g], "Exact"["falseElimination"[h[g]]], "Introduce"[g], "Exact"[g]}
		]["Goals"]
	},
	{ConstantArray[True, 7], ConstantArray[<|"quotientSoundness" -> "Proposition"|>, 3], {}, {}},
	TestID -> "The-order-of-the-rationals-is-total-and-sums-and-products-keep-it"
]

(* The order has its Booleans, which the kernel computes, and they decide it: "Decide" proves an inequality of literal
   rationals, a strict one and the negation of one, and refuses a false one; the decision is a Boolean of the kernel. *)
VerificationTest[
	{
		TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			{
				"rationalLessEqualQ"[Typed[1/3, Rationals], 1/2], "rationalLessEqualQ"[Typed[1/2, Rationals], 1/3], "rationalLessEqualQ"[Typed[-1/2, Rationals], -1/3],
				"rationalLessQ"[Typed[1/2, Rationals], 1/2], "rationalNonNegativeQ"[Typed[-1/1000000, Rationals]]
			},
			rationals
		]]],
		TypeTheoryProof[Typed[1/3, Rationals] <= 1/2, rationals, {"Decide"}]["Goals"],
		TypeTheoryProof[Typed[1/3, Rationals] < 1/2, rationals, {"Decide"}]["Goals"],
		TypeTheoryProof[Not[Typed[1/2, Rationals] <= 1/3], rationals, {"Decide"}]["Goals"],
		TypeTheoryProof[Typed[1/2, Rationals] < 1/3, rationals, {"Decide"}]["Tag"],
		MatchQ[rationals["rationalLessEqualDecidable"], TypeTheoryDefinition[__, "Instance" -> True]],
		MatchQ[rationals["rationalLessDecidable"], TypeTheoryDefinition[__, "Instance" -> True]]
	},
	{{True, False, True, False, False}, {}, {}, {}, "DecidedFalse", True, True},
	TestID -> "The-order-of-the-rationals-is-decided-by-its-Booleans"
]
