(* ::Package:: *)

(*
The rationals: TypeTheoryEnvironment["Rationals"] is the environment of the integers with them, built and
checked the first time it is asked for. A rational is a class of pairs (a, b) of an integer and a natural
number, standing for a / (b + 1), by the relation that relates (a, b) and (c, d) when a (d + 1) == c (b + 1):
a quotient type over the integers, as the integers are one over the natural numbers, with no pair whose
denominator is 0.

	Rationals                       QuotientType["rationalRelation"], shown as ℚ
	"rationalOfInteger"[x]          the class of (x, 0), a coercion: an integer, or a natural number by way of the
	                                integers, where a rational is expected
	-x, x + y, x - y, x y, x^n      "rationalNegation", "rationalAddition", "rationalSubtraction",
	                                "rationalMultiplication" and "rationalPower"
	x^-1, x / y                     "rationalInverse" and "rationalDivision"; the inverse of 0 is 0
	x <= y, x < y, x >= y, x > y    "rationalLessEqual" and the others: y is x plus the class of (n, d) for natural
	                                numbers n and d, with n at least 1 for <

An operation lifts a function on pairs with QuotientLift, as the integers' operations do. That a function
respects the relation follows from the relation by a polynomial combination, which "PolynomialReduce" finds
over the integers, and the laws of a commutative ring follow by "Induction" on each rational,
QuotientSoundness, and "Ring" on the equation of integers of the pairs.

The inverse computes. For a pair (m, n) of natural numbers, standing for the integer m - n, the inverse of
(m - n) / (b + 1) is (b + 1) / (m - n), by recursion on m and then on n, and 0 where m - n is 0. It takes the
same value on (m + k, n + k), so on every pair of an integer, and lifts to the integers. Where a is not 0,
its product with the class of (a, b) is 1. So the inverses of related pairs are both 0, or are inverses of
the same rational and equal: the inverse lifts to the rationals.

Equations of rationals are decidable: RationalEqualityDecidable decides x == y with the Boolean
"rationalEqual", which compares a (d + 1) and c (b + 1) with "integerEqual", so Decide and the tactic
"Decide" settle an equation of rational literals by computation.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[RationalAdditionCommutativity]
PackageExported[RationalAdditionAssociativity]
PackageExported[RationalAdditionZero]
PackageExported[RationalAdditionNegation]
PackageExported[RationalMultiplicationCommutativity]
PackageExported[RationalMultiplicationAssociativity]
PackageExported[RationalMultiplicationOne]
PackageExported[RationalDistributivity]
PackageExported[RationalSubtractionNegation]
PackageExported[RationalOfIntegerAddition]
PackageExported[RationalOfIntegerMultiplication]
PackageExported[RationalMultiplicationInverse]
PackageExported[RationalInverseZero]
PackageExported[RationalEqualityDecidable]
PackageExported[RationalLessEqualReflexivity]
PackageExported[RationalSquareNonnegative]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[rationalsEnvironment]


(* ::Section:: *)
(*Usage Messages*)


RationalAdditionCommutativity::usage = "RationalAdditionCommutativity[x, y] proves x + y == y + x for rationals x and y. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalAdditionAssociativity::usage = "RationalAdditionAssociativity[x, y, z] proves (x + y) + z == x + (y + z) for rationals. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalAdditionZero::usage = "RationalAdditionZero[x] proves x + 0 == x for a rational x. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalAdditionNegation::usage = "RationalAdditionNegation[x] proves x + -x == 0 for a rational x. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalMultiplicationCommutativity::usage = "RationalMultiplicationCommutativity[x, y] proves x y == y x for rationals x and y. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalMultiplicationAssociativity::usage = "RationalMultiplicationAssociativity[x, y, z] proves (x y) z == x (y z) for rationals. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalMultiplicationOne::usage = "RationalMultiplicationOne[x] proves x * 1 == x for a rational x. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalDistributivity::usage = "RationalDistributivity[x, y, z] proves x (y + z) == x y + x z for rationals. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalSubtractionNegation::usage = "RationalSubtractionNegation[x, y] proves x - y == x + -y for rationals, which holds by computation. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalOfIntegerAddition::usage = "RationalOfIntegerAddition[a, b] proves that the rational of a + b is the sum of the rationals of the integers a and b. \
It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalOfIntegerMultiplication::usage = "RationalOfIntegerMultiplication[a, b] proves that the rational of a b is the product of the rationals of the integers a and b. \
It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalMultiplicationInverse::usage = "RationalMultiplicationInverse[x, h] proves x x^-1 == 1 from a proof h of Not[x == 0], for a rational x. \
It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalInverseZero::usage = "RationalInverseZero proves 0^-1 == 0 for the rationals, which holds by computation. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalEqualityDecidable::usage = "RationalEqualityDecidable[x, y] decides x == y for rationals x and y; it is the instance of Decidable[x == y] in \
TypeTheoryEnvironment[\"Rationals\"], so Decide and the tactic \"Decide\" settle equations of rationals by computation."
RationalLessEqualReflexivity::usage = "RationalLessEqualReflexivity[x] proves x <= x for a rational x. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."
RationalSquareNonnegative::usage = "RationalSquareNonnegative[x] proves 0 <= x x for a rational x. It is a theorem of TypeTheoryEnvironment[\"Rationals\"]."

rationalsEnvironment::usage = "rationalsEnvironment[] gives the environment of the integers with the rationals, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations in order, each theorem proved by its tactics in the environment so far *)
rationalsEnvironment[] := rationalsEnvironment[] = withoutStoreTracking[
	libraryEnvironment["Rationals", integersEnvironment[], withStoreCleanup[Fold[addRationalDeclaration, integersEnvironment[], $rationalDeclarations]]]
]

SetAttributes[rationalTheorem, HoldAll]

addRationalDeclaration[failure_Failure, _] := failure
addRationalDeclaration[environment_, rationalTheorem[name_, statement_, tactics_List]] :=
	TypeTheoryEnvironment[environment, {TypeTheoryTheorem[name, TypeTheoryProof[statement, environment, tactics]]}]
addRationalDeclaration[environment_, declaration_] := TypeTheoryEnvironment[environment, {declaration}]

$rationalDeclarations = With[{pairs = CartesianProductType[Integers, NonNegativeIntegers], differences = CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]}, {
	(* Integers first. The class of (n + k, n) is k, and that of (n, n + k) is -k. *)
	rationalTheorem[
		"integerOfDifference",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, "integerOfPair"[Pair[n + k, n]] == "integerOfNatural"[k]],
		{TypeTheoryTactic["Introduce", n, k], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		"integerOfDifferenceNegative",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, "integerOfPair"[Pair[n, n + k]] == "integerNegation"["integerOfNatural"[k]]],
		{TypeTheoryTactic["Introduce", n, k], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],

	(* A multiple of an integer by a positive natural number is 0 only where the integer is: the pair of
	   (a, b) (d + 1) is ((d + 1) a, (d + 1) b), whose classes are 0 where (d + 1) a == (d + 1) b. So a positive
	   factor cancels. *)
	rationalTheorem[
		"scaledPairEquation",
		ForAll[
			{Typed[d, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
			Implies[(a (d + 1) + b 0) + 0 == 0 + (a 0 + b (d + 1)), (d + 1) a == (d + 1) b]
		],
		{TypeTheoryTactic["Introduce", d, a, b, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	rationalTheorem[
		"relationOfEqual",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[a == b, "integerRelation"[Pair[a, b], Pair[0, 0]]]],
		{TypeTheoryTactic["Introduce", a, b, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	TypeTheoryTheorem[
		"integerZeroOfScaled",
		ForAll[{Typed[d, NonNegativeIntegers], Typed[x, Integers]}, Implies[x "integerOfNatural"[d + 1] == 0, x == 0]],
		Function[{Typed[d, NonNegativeIntegers], Typed[x, Integers]}, Construct[
			QuotientInduction,
			differences,
			"integerRelation",
			Function[{Typed[w, Integers]}, Implies[w "integerOfNatural"[d + 1] == 0, w == 0]],
			Function[{Typed[r, differences], Typed[h, "integerOfPair"[r] "integerOfNatural"[d + 1] == 0]},
				QuotientSoundness["relationOfEqual"[r[[1]], r[[2]], MultiplicationCancellation[d, r[[1]], r[[2]], "scaledPairEquation"[d, r[[1]], r[[2]],
					"integerExact"[Pair[r[[1]] (d + 1) + r[[2]] 0, r[[1]] 0 + r[[2]] (d + 1)], Pair[0, 0], h]
				]]]]
			],
			x
		]]
	],
	rationalTheorem[
		"scaledDifference",
		ForAll[
			{Typed[d, NonNegativeIntegers], Typed[x, Integers], Typed[y, Integers]},
			Implies[x "integerOfNatural"[d + 1] == y "integerOfNatural"[d + 1], (x - y) "integerOfNatural"[d + 1] == 0]
		],
		{TypeTheoryTactic["Introduce", d, x, y, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"equalOfDifference",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x - y == 0, x == y]],
		{TypeTheoryTactic["Introduce", x, y, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	TypeTheoryTheorem[
		"integerCancelScaled",
		ForAll[
			{Typed[d, NonNegativeIntegers], Typed[x, Integers], Typed[y, Integers]},
			Implies[x "integerOfNatural"[d + 1] == y "integerOfNatural"[d + 1], x == y]
		],
		Function[
			{Typed[d, NonNegativeIntegers], Typed[x, Integers], Typed[y, Integers], Typed[h, x "integerOfNatural"[d + 1] == y "integerOfNatural"[d + 1]]},
			"equalOfDifference"[x, y, "integerZeroOfScaled"[d, x - y, "scaledDifference"[d, x, y, h]]]
		]
	],

	(* Equivalent equations of integers have the same Boolean, as "equalOfEquivalent" for natural numbers *)
	TypeTheoryTheorem[
		"integerEqualOfEquivalent",
		ForAll[
			{Typed[a, Integers], Typed[b, Integers], Typed[c, Integers], Typed[d, Integers]},
			Implies[Equivalent[a == b, c == d], "integerEqual"[a, b] == "integerEqual"[c, d]]
		],
		Function[{Typed[a, Integers], Typed[b, Integers], Typed[c, Integers], Typed[d, Integers], Typed[h, Equivalent[a == b, c == d]]},
			InductiveRecursor[Booleans][
				Function[{Typed[x, Booleans]}, Implies["integerEqual"[a, b] == x, "integerEqual"[a, b] == "integerEqual"[c, d]]],
				Function[{Typed[e, "integerEqual"[a, b] == "false"]}, InductiveRecursor[Booleans][
					Function[{Typed[y, Booleans]}, Implies["integerEqual"[c, d] == y, "integerEqual"[a, b] == "integerEqual"[c, d]]],
					Function[{Typed[f, "integerEqual"[c, d] == "false"]}, EqualityTransitivity[e, EqualitySymmetry[f]]],
					Function[{Typed[f, "integerEqual"[c, d] == "true"]},
						FalseElimination["integerEqualFalse"[a, b, e][EquivalentBackward[h]["integerEqualTrue"[c, d, f]]]]
					],
					"integerEqual"[c, d]
				][EqualityReflexivity["integerEqual"[c, d]]]],
				Function[{Typed[e, "integerEqual"[a, b] == "true"]}, InductiveRecursor[Booleans][
					Function[{Typed[y, Booleans]}, Implies["integerEqual"[c, d] == y, "integerEqual"[a, b] == "integerEqual"[c, d]]],
					Function[{Typed[f, "integerEqual"[c, d] == "false"]},
						FalseElimination["integerEqualFalse"[c, d, f][EquivalentForward[h]["integerEqualTrue"[a, b, e]]]]
					],
					Function[{Typed[f, "integerEqual"[c, d] == "true"]}, EqualityTransitivity[e, EqualitySymmetry[f]]],
					"integerEqual"[c, d]
				][EqualityReflexivity["integerEqual"[c, d]]]],
				"integerEqual"[a, b]
			][EqualityReflexivity["integerEqual"[a, b]]]
		]
	],

	(* The rationals: pairs (a, b) and (c, d) are related when a (d + 1) == c (b + 1) *)
	TypeTheoryDefinition[
		"rationalRelation",
		Function[{Typed[p, pairs], Typed[q, pairs]}, p[[1]] "integerOfNatural"[q[[2]] + 1] == q[[1]] "integerOfNatural"[p[[2]] + 1]]
	],
	TypeTheoryDefinition[Rationals, Typed[QuotientType["rationalRelation"], TypeUniverse[1]]],
	TypeTheoryDefinition[
		"rationalOfPair",
		Typed[Function[{Typed[p, pairs]}, QuotientIntroduction["rationalRelation", p]], TypeSpecifier[{pairs} -> Rationals]]
	],
	TypeTheoryDefinition[
		"rationalOfInteger",
		Typed[Function[{Typed[x, Integers]}, "rationalOfPair"[Pair[x, 0]]], TypeSpecifier[{Integers} -> Rationals]],
		"Coercion" -> True
	],

	(* negating, adding and multiplying pairs respect the relation, each a polynomial combination of it:
	   -(a, b) is (-a, b), (a, b) + (c, d) is (a (d + 1) + c (b + 1), b d + b + d), and (a, b) (c, d) is (a c, b d + b + d) *)
	rationalTheorem[
		"rationalNegationRespects",
		ForAll[{Typed[p, pairs], Typed[q, pairs]}, Implies["rationalRelation"[p, q], "rationalRelation"[Pair[-p[[1]], p[[2]]], Pair[-q[[1]], q[[2]]]]]],
		{TypeTheoryTactic["Introduce", p, q, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalAdditionRespectsLeft",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[p, q], "rationalRelation"[
				Pair[p[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] s[[2]] + p[[2]] + s[[2]]],
				Pair[q[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[q[[2]] + 1], q[[2]] s[[2]] + q[[2]] + s[[2]]]
			]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalAdditionRespectsRight",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[q, s], "rationalRelation"[
				Pair[p[[1]] "integerOfNatural"[q[[2]] + 1] + q[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] q[[2]] + p[[2]] + q[[2]]],
				Pair[p[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] s[[2]] + p[[2]] + s[[2]]]
			]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalMultiplicationRespectsLeft",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[p, q], "rationalRelation"[
				Pair[p[[1]] s[[1]], p[[2]] s[[2]] + p[[2]] + s[[2]]],
				Pair[q[[1]] s[[1]], q[[2]] s[[2]] + q[[2]] + s[[2]]]
			]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalMultiplicationRespectsRight",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[q, s], "rationalRelation"[
				Pair[p[[1]] q[[1]], p[[2]] q[[2]] + p[[2]] + q[[2]]],
				Pair[p[[1]] s[[1]], p[[2]] s[[2]] + p[[2]] + s[[2]]]
			]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],

	(* the operations; a binary one lifts in its second argument for each pair, then in its first, whose
	   proof is by induction on the second *)
	TypeTheoryDefinition[
		"rationalNegation",
		Typed[
			Function[{Typed[x, Rationals]}, QuotientLift[
				Function[{Typed[p, pairs]}, "rationalOfPair"[Pair[-p[[1]], p[[2]]]]],
				Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]}, QuotientSoundness["rationalNegationRespects"[p, q, e]]],
				x
			]],
			TypeSpecifier[{Rationals} -> Rationals]
		]
	],
	TypeTheoryDefinition[
		"rationalAdditionOfPair",
		Typed[
			Function[{Typed[p, pairs], Typed[y, Rationals]}, QuotientLift[
				Function[{Typed[q, pairs]}, "rationalOfPair"[
					Pair[p[[1]] "integerOfNatural"[q[[2]] + 1] + q[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] q[[2]] + p[[2]] + q[[2]]]
				]],
				Function[{Typed[q, pairs], Typed[s, pairs], Typed[e, "rationalRelation"[q, s]]}, QuotientSoundness["rationalAdditionRespectsRight"[p, q, s, e]]],
				y
			]],
			TypeSpecifier[{pairs, Rationals} -> Rationals]
		]
	],
	TypeTheoryDefinition[
		"rationalAddition",
		Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]}, QuotientLift[
				Function[{Typed[p, pairs]}, "rationalAdditionOfPair"[p, y]],
				Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]},
					Construct[
						QuotientInduction,
						pairs,
						"rationalRelation",
						Function[{Typed[z, Rationals]}, "rationalAdditionOfPair"[p, z] == "rationalAdditionOfPair"[q, z]],
						Function[{Typed[s, pairs]}, QuotientSoundness["rationalAdditionRespectsLeft"[p, q, s, e]]],
						y
					]
				],
				x
			]],
			TypeSpecifier[{Rationals, Rationals} -> Rationals]
		]
	],
	TypeTheoryDefinition[
		"rationalMultiplicationOfPair",
		Typed[
			Function[{Typed[p, pairs], Typed[y, Rationals]}, QuotientLift[
				Function[{Typed[q, pairs]}, "rationalOfPair"[Pair[p[[1]] q[[1]], p[[2]] q[[2]] + p[[2]] + q[[2]]]]],
				Function[{Typed[q, pairs], Typed[s, pairs], Typed[e, "rationalRelation"[q, s]]}, QuotientSoundness["rationalMultiplicationRespectsRight"[p, q, s, e]]],
				y
			]],
			TypeSpecifier[{pairs, Rationals} -> Rationals]
		]
	],
	TypeTheoryDefinition[
		"rationalMultiplication",
		Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]}, QuotientLift[
				Function[{Typed[p, pairs]}, "rationalMultiplicationOfPair"[p, y]],
				Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]},
					Construct[
						QuotientInduction,
						pairs,
						"rationalRelation",
						Function[{Typed[z, Rationals]}, "rationalMultiplicationOfPair"[p, z] == "rationalMultiplicationOfPair"[q, z]],
						Function[{Typed[s, pairs]}, QuotientSoundness["rationalMultiplicationRespectsLeft"[p, q, s, e]]],
						y
					]
				],
				x
			]],
			TypeSpecifier[{Rationals, Rationals} -> Rationals]
		]
	],
	TypeTheoryDefinition[
		"rationalSubtraction",
		Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalAddition"[x, "rationalNegation"[y]]], TypeSpecifier[{Rationals, Rationals} -> Rationals]]
	],
	(* x^0 is 1 and x^(n + 1) is x^n x *)
	TypeTheoryDefinition[
		"rationalPower",
		Typed[
			Function[{Typed[x, Rationals], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[k, NonNegativeIntegers]}, Rationals],
				"rationalOfInteger"["integerOfNatural"[1]],
				Function[{Typed[k, NonNegativeIntegers], Typed[v, Rationals]}, "rationalMultiplication"[v, x]],
				n
			]],
			TypeSpecifier[{Rationals, NonNegativeIntegers} -> Rationals]
		]
	],

	(* Two classes of pairs with equal integers and equal natural numbers are equal by congruence, and scaling a
	   pair by k + 1 keeps its class: a law whose sides compute to such pairs needs only identities of the
	   components, of a lower degree than the relation of the two pairs. *)
	TypeTheoryTheorem[
		"pairClassEquality",
		ForAll[
			{TypedImplicit[a, Integers], TypedImplicit[c, Integers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[d, NonNegativeIntegers]},
			Implies[a == c, Implies[b == d, "rationalOfPair"[Pair[a, b]] == "rationalOfPair"[Pair[c, d]]]]
		],
		Function[
			{
				TypedImplicit[a, Integers], TypedImplicit[c, Integers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[d, NonNegativeIntegers],
				Typed[e, a == c], Typed[f, b == d]
			},
			EqualityTransitivity[
				EqualityCongruence[Function[{Typed[w, Integers]}, "rationalOfPair"[Pair[w, b]]], e],
				EqualityCongruence[Function[{Typed[w, NonNegativeIntegers]}, "rationalOfPair"[Pair[c, w]]], f]
			]
		]
	],
	rationalTheorem[
		"scaledClass",
		ForAll[
			{Typed[a, Integers], Typed[b, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"rationalOfPair"[Pair[a, b]] == "rationalOfPair"[Pair[a "integerOfNatural"[k + 1], b k + b + k]]
		],
		{TypeTheoryTactic["Introduce", a, b, k], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],

	(* the laws of a commutative ring: by induction on each rational, then the relation of the two pairs,
	   an equation of integers, or the equations of their components *)
	rationalTheorem[
		RationalAdditionCommutativity,
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x + y == y + x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		RationalAdditionAssociativity,
		ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x + y) + z == x + (y + z)],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", "pairClassEquality"],
			TypeTheoryTactic["Ring"],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		RationalAdditionZero,
		ForAll[{Typed[x, Rationals]}, x + 0 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	(* x + -x is read as x - x, so the negation is written out *)
	rationalTheorem[
		RationalAdditionNegation,
		ForAll[{Typed[x, Rationals]}, x + "rationalNegation"[x] == 0],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		RationalMultiplicationCommutativity,
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x y == y x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		RationalMultiplicationAssociativity,
		ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x y) z == x (y z)],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		RationalMultiplicationOne,
		ForAll[{Typed[x, Rationals]}, x * 1 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	(* x (y + z) is the class of a pair that, scaled by the denominator of x, is that of x y + x z *)
	rationalTheorem[
		"distributivityNumerator",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			p[[1]] (q[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[q[[2]] + 1]) "integerOfNatural"[p[[2]] + 1] ==
				p[[1]] q[[1]] "integerOfNatural"[p[[2]] s[[2]] + p[[2]] + s[[2]] + 1] + p[[1]] s[[1]] "integerOfNatural"[p[[2]] q[[2]] + p[[2]] + q[[2]] + 1]
		],
		{TypeTheoryTactic["Introduce", p, q, s], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		"distributivityDenominator",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			(p[[2]] (q[[2]] s[[2]] + q[[2]] + s[[2]]) + p[[2]] + (q[[2]] s[[2]] + q[[2]] + s[[2]])) p[[2]] +
				(p[[2]] (q[[2]] s[[2]] + q[[2]] + s[[2]]) + p[[2]] + (q[[2]] s[[2]] + q[[2]] + s[[2]])) + p[[2]] ==
			(p[[2]] q[[2]] + p[[2]] + q[[2]]) (p[[2]] s[[2]] + p[[2]] + s[[2]]) + (p[[2]] q[[2]] + p[[2]] + q[[2]]) + (p[[2]] s[[2]] + p[[2]] + s[[2]])
		],
		{TypeTheoryTactic["Introduce", p, q, s], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		RationalDistributivity,
		ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, x (y + z) == x y + x z],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Exact", EqualityTransitivity[
				"scaledClass"[
					p[[1]] (q[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[q[[2]] + 1]),
					p[[2]] (q[[2]] s[[2]] + q[[2]] + s[[2]]) + p[[2]] + (q[[2]] s[[2]] + q[[2]] + s[[2]]),
					p[[2]]
				],
				"pairClassEquality"["distributivityNumerator"[p, q, s], "distributivityDenominator"[p, q, s]]
			]]
		}
	],
	(* a difference is a sum with the negation, by computation *)
	rationalTheorem[
		RationalSubtractionNegation,
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x - y == x + "rationalNegation"[y]],
		{TypeTheoryTactic["Introduce", x, y], TypeTheoryTactic["Reflexivity"]}
	],
	(* the integers keep their sums and products among the rationals; the coercion is written out *)
	rationalTheorem[
		RationalOfIntegerAddition,
		ForAll[{Typed[a, Integers], Typed[b, Integers]}, "rationalOfInteger"[a + b] == "rationalOfInteger"[a] + "rationalOfInteger"[b]],
		{TypeTheoryTactic["Introduce", a, b], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		RationalOfIntegerMultiplication,
		ForAll[{Typed[a, Integers], Typed[b, Integers]}, "rationalOfInteger"[a b] == "rationalOfInteger"[a] "rationalOfInteger"[b]],
		{TypeTheoryTactic["Introduce", a, b], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],

	(* The inverse. (b + 1) / (m - n) is the class of (b + 1, m - n - 1) where m is larger, that of
	   (-(b + 1), n - m - 1) where n is, and 0 where they are equal, by recursion on m and then on n. *)
	TypeTheoryDefinition[
		"differenceInverse",
		Typed[
			Function[{Typed[b, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[t, NonNegativeIntegers]}, TypeSpecifier[{NonNegativeIntegers} -> Rationals]],
				Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[t, NonNegativeIntegers]}, Rationals],
					"rationalOfPair"[Pair["integerOfNatural"[0], 0]],
					Function[{Typed[k, NonNegativeIntegers], Typed[v, Rationals]}, "rationalOfPair"[Pair["integerNegation"["integerOfNatural"[b + 1]], k]]],
					n
				]],
				Function[{Typed[j, NonNegativeIntegers], Typed[f, TypeSpecifier[{NonNegativeIntegers} -> Rationals]]}, Function[{Typed[n, NonNegativeIntegers]},
					InductiveRecursor[NonNegativeIntegers][
						Function[{Typed[t, NonNegativeIntegers]}, Rationals],
						"rationalOfPair"[Pair["integerOfNatural"[b + 1], j]],
						Function[{Typed[k, NonNegativeIntegers], Typed[v, Rationals]}, f[k]],
						n
					]
				]],
				m
			]],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers, NonNegativeIntegers} -> Rationals]
		]
	],
	(* (m + k, n + k) gives what (m, n) gives, so related pairs give the same *)
	rationalTheorem[
		"differenceInverseShift",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"differenceInverse"[b, m + k, n + k] == "differenceInverse"[b, m, n]
		],
		{
			TypeTheoryTactic["Introduce", b, m, n, k],
			TypeTheoryTactic["Induction", k],
			TypeTheoryTactic["Reflexivity"],
			TypeTheoryTactic["Introduce", k, ih],
			TypeTheoryTactic["Exact", ih]
		}
	],
	rationalTheorem[
		"differenceInverseShiftLeft",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"differenceInverse"[b, k + m, k + n] == "differenceInverse"[b, m, n]
		],
		{
			TypeTheoryTactic["Introduce", b, m, n, k],
			TypeTheoryTactic["Rewrite", AdditionCommutativity[k, m]],
			TypeTheoryTactic["Rewrite", AdditionCommutativity[k, n]],
			TypeTheoryTactic["Exact", "differenceInverseShift"[b, m, n, k]]
		}
	],
	TypeTheoryTheorem[
		"differenceInverseRespects",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[q, differences], Typed[s, differences]},
			Implies["integerRelation"[q, s], "differenceInverse"[b, q[[1]], q[[2]]] == "differenceInverse"[b, s[[1]], s[[2]]]]
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[q, differences], Typed[s, differences], Typed[e, "integerRelation"[q, s]]},
			EqualityTransitivity[
				EqualitySymmetry["differenceInverseShift"[b, q[[1]], q[[2]], s[[2]]]],
				EqualityTransitivity[
					EqualityCongruence[Function[{Typed[c, NonNegativeIntegers]}, "differenceInverse"[b, c, q[[2]] + s[[2]]]], e],
					EqualityTransitivity[
						EqualityCongruence[Function[{Typed[c, NonNegativeIntegers]}, "differenceInverse"[b, s[[1]] + q[[2]], c]], AdditionCommutativity[q[[2]], s[[2]]]],
						"differenceInverseShift"[b, s[[1]], s[[2]], q[[2]]]
					]
				]
			]
		]
	],
	TypeTheoryDefinition[
		"inverseOfPair",
		Typed[
			Function[{Typed[p, pairs]}, QuotientLift[
				Function[{Typed[r, differences]}, "differenceInverse"[p[[2]], r[[1]], r[[2]]]],
				Function[{Typed[q, differences], Typed[s, differences], Typed[e, "integerRelation"[q, s]]}, "differenceInverseRespects"[p[[2]], q, s, e]],
				p[[1]]
			]],
			TypeSpecifier[{pairs} -> Rationals]
		]
	],

	(* Where a is 0, the inverse of (a, b) is 0. Where it is not, its product with the class of (a, b) is 1:
	   for the pair (n + (i + 1), n) of a, the inverse is (b + 1) / (i + 1), and so with signs where a is negative. *)
	TypeTheoryTheorem[
		"inverseOfPairZero",
		ForAll[{Typed[p, pairs]}, Implies[p[[1]] == 0, "inverseOfPair"[p] == 0]],
		Function[{Typed[p, pairs], Typed[h, p[[1]] == 0]}, Construct[
			EqualitySubstitution,
			Integers,
			Function[{Typed[w, Integers]}, "inverseOfPair"[Pair[w, p[[2]]]] == 0],
			"integerOfNatural"[0],
			p[[1]],
			EqualitySymmetry[h],
			EqualityReflexivity["rationalOfInteger"["integerOfNatural"[0]]]
		]]
	],
	rationalTheorem[
		"unitProduct",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			"rationalMultiplication"["differenceInverse"[b, i + 1, 0], "rationalOfPair"[Pair["integerOfNatural"[i + 1], b]]] == 1
		],
		{TypeTheoryTactic["Introduce", b, i], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		"negativeUnitProduct",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			"rationalMultiplication"["differenceInverse"[b, 0, i + 1], "rationalOfPair"[Pair["integerNegation"["integerOfNatural"[i + 1]], b]]] == 1
		],
		{TypeTheoryTactic["Introduce", b, i], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],
	TypeTheoryTheorem[
		"positiveInverseProduct",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			"rationalMultiplication"["differenceInverse"[b, n + (i + 1), n], "rationalOfPair"[Pair["integerOfPair"[Pair[n + (i + 1), n]], b]]] == 1
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, EqualityTransitivity[
			EqualityCongruence[
				Function[{Typed[w, Rationals]}, "rationalMultiplication"[w, "rationalOfPair"[Pair["integerOfPair"[Pair[n + (i + 1), n]], b]]]],
				"differenceInverseShiftLeft"[b, i + 1, 0, n]
			],
			EqualityTransitivity[
				EqualityCongruence[
					Function[{Typed[w, Integers]}, "rationalMultiplication"["differenceInverse"[b, i + 1, 0], "rationalOfPair"[Pair[w, b]]]],
					"integerOfDifference"[n, i + 1]
				],
				"unitProduct"[b, i]
			]
		]]
	],
	TypeTheoryTheorem[
		"negativeInverseProduct",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			"rationalMultiplication"["differenceInverse"[b, n, n + (i + 1)], "rationalOfPair"[Pair["integerOfPair"[Pair[n, n + (i + 1)]], b]]] == 1
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, EqualityTransitivity[
			EqualityCongruence[
				Function[{Typed[w, Rationals]}, "rationalMultiplication"[w, "rationalOfPair"[Pair["integerOfPair"[Pair[n, n + (i + 1)]], b]]]],
				"differenceInverseShiftLeft"[b, 0, i + 1, n]
			],
			EqualityTransitivity[
				EqualityCongruence[
					Function[{Typed[w, Integers]}, "rationalMultiplication"["differenceInverse"[b, 0, i + 1], "rationalOfPair"[Pair[w, b]]]],
					"integerOfDifferenceNegative"[n, i + 1]
				],
				"negativeUnitProduct"[b, i]
			]
		]]
	],
	rationalTheorem[
		"successorAddition",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[j, NonNegativeIntegers]}, m + (j + 1) == m + 1 + j],
		{TypeTheoryTactic["Introduce", m, j], TypeTheoryTactic["Ring"]}
	],
	TypeTheoryTheorem[
		"nonnegativeInverseOrZero",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[j, NonNegativeIntegers]},
			Or[
				"integerOfPair"[Pair[n + j, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, n + j, n], "rationalOfPair"[Pair["integerOfPair"[Pair[n + j, n]], b]]] == 1
			]
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[j, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[t, NonNegativeIntegers]}, Or[
				"integerOfPair"[Pair[n + t, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, n + t, n], "rationalOfPair"[Pair["integerOfPair"[Pair[n + t, n]], b]]] == 1
			]],
			OrIntroductionLeft["integerOfDifference"[n, 0]],
			Function[
				{
					Typed[t, NonNegativeIntegers],
					Typed[ih, Or[
						"integerOfPair"[Pair[n + t, n]] == 0,
						"rationalMultiplication"["differenceInverse"[b, n + t, n], "rationalOfPair"[Pair["integerOfPair"[Pair[n + t, n]], b]]] == 1
					]]
				},
				OrIntroductionRight["positiveInverseProduct"[b, t, n]]
			],
			j
		]]
	],
	TypeTheoryTheorem[
		"pairInverseOrZero",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Or[
				"integerOfPair"[Pair[m, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"[Pair["integerOfPair"[Pair[m, n]], b]]] == 1
			]
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[Or][
			Function[{Typed[t, Or[n <= m, m < n]]}, Or[
				"integerOfPair"[Pair[m, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"[Pair["integerOfPair"[Pair[m, n]], b]]] == 1
			]],
			Function[{Typed[le, n <= m]}, InductiveRecursor[Exists][
				Function[{Typed[o, Exists[{Typed[j, NonNegativeIntegers]}, m == n + j]]}, Or[
					"integerOfPair"[Pair[m, n]] == 0,
					"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"[Pair["integerOfPair"[Pair[m, n]], b]]] == 1
				]],
				Function[{Typed[j, NonNegativeIntegers], Typed[ej, m == n + j]}, Construct[
					EqualitySubstitution,
					NonNegativeIntegers,
					Function[{Typed[c, NonNegativeIntegers]}, Or[
						"integerOfPair"[Pair[c, n]] == 0,
						"rationalMultiplication"["differenceInverse"[b, c, n], "rationalOfPair"[Pair["integerOfPair"[Pair[c, n]], b]]] == 1
					]],
					n + j,
					m,
					EqualitySymmetry[ej],
					"nonnegativeInverseOrZero"[b, n, j]
				]],
				"lessEqualWitness"[n, m, le]
			]],
			Function[{Typed[lt, m < n]}, InductiveRecursor[Exists][
				Function[{Typed[o, Exists[{Typed[j, NonNegativeIntegers]}, n == m + 1 + j]]}, Or[
					"integerOfPair"[Pair[m, n]] == 0,
					"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"[Pair["integerOfPair"[Pair[m, n]], b]]] == 1
				]],
				Function[{Typed[j, NonNegativeIntegers], Typed[ej, n == m + 1 + j]}, Construct[
					EqualitySubstitution,
					NonNegativeIntegers,
					Function[{Typed[c, NonNegativeIntegers]}, Or[
						"integerOfPair"[Pair[m, c]] == 0,
						"rationalMultiplication"["differenceInverse"[b, m, c], "rationalOfPair"[Pair["integerOfPair"[Pair[m, c]], b]]] == 1
					]],
					m + (j + 1),
					n,
					EqualityTransitivity["successorAddition"[m, j], EqualitySymmetry[ej]],
					OrIntroductionRight["negativeInverseProduct"[b, j, m]]
				]],
				"lessEqualWitness"[m + 1, n, lt]
			]],
			LessEqualTotality[n, m]
		]]
	],
	TypeTheoryTheorem[
		"inverseOrZero",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[x, Integers]},
			Or[x == 0, "rationalMultiplication"["inverseOfPair"[Pair[x, b]], "rationalOfPair"[Pair[x, b]]] == 1]
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[x, Integers]}, Construct[
			QuotientInduction,
			differences,
			"integerRelation",
			Function[{Typed[w, Integers]}, Or[w == 0, "rationalMultiplication"["inverseOfPair"[Pair[w, b]], "rationalOfPair"[Pair[w, b]]] == 1]],
			Function[{Typed[r, differences]}, "pairInverseOrZero"[b, r[[1]], r[[2]]]],
			x
		]]
	],

	(* so the inverses of related pairs are equal: both 0 where a numerator is 0, and otherwise both
	   inverses of the same rational, which has one inverse *)
	rationalTheorem[
		"numeratorZero",
		ForAll[{Typed[p, pairs], Typed[q, pairs]}, Implies["rationalRelation"[p, q], Implies[p[[1]] == 0, q[[1]] == 0]]],
		{
			TypeTheoryTactic["Introduce", p, q, e, h],
			TypeTheoryTactic["Apply", "integerZeroOfScaled"[p[[2]]]],
			TypeTheoryTactic["PolynomialReduce"]
		}
	],
	TypeTheoryTheorem[
		"inverseUniqueness",
		ForAll[{Typed[u, Rationals], Typed[v, Rationals], Typed[x, Rationals]}, Implies[u x == 1, Implies[v x == 1, u == v]]],
		Function[{Typed[u, Rationals], Typed[v, Rationals], Typed[x, Rationals], Typed[hu, u x == 1], Typed[hv, v x == 1]},
			EqualityTransitivity[
				EqualitySymmetry[RationalMultiplicationOne[u]],
				EqualityTransitivity[
					EqualityCongruence[Function[{Typed[w, Rationals]}, u w], EqualitySymmetry[hv]],
					EqualityTransitivity[
						EqualityCongruence[Function[{Typed[w, Rationals]}, u w], RationalMultiplicationCommutativity[v, x]],
						EqualityTransitivity[
							EqualitySymmetry[RationalMultiplicationAssociativity[u, x, v]],
							EqualityTransitivity[
								EqualityCongruence[Function[{Typed[w, Rationals]}, w v], hu],
								EqualityTransitivity[RationalMultiplicationCommutativity["rationalOfInteger"["integerOfNatural"[1]], v], RationalMultiplicationOne[v]]
							]
						]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"inverseRespects",
		ForAll[{Typed[p, pairs], Typed[q, pairs]}, Implies["rationalRelation"[p, q], "inverseOfPair"[p] == "inverseOfPair"[q]]],
		Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]}, InductiveRecursor[Or][
			Function[{Typed[t, Or[p[[1]] == 0, "rationalMultiplication"["inverseOfPair"[p], "rationalOfPair"[p]] == 1]]}, "inverseOfPair"[p] == "inverseOfPair"[q]],
			Function[{Typed[zp, p[[1]] == 0]}, EqualityTransitivity["inverseOfPairZero"[p, zp], EqualitySymmetry["inverseOfPairZero"[q, "numeratorZero"[p, q, e, zp]]]]],
			Function[{Typed[up, "rationalMultiplication"["inverseOfPair"[p], "rationalOfPair"[p]] == 1]}, InductiveRecursor[Or][
				Function[{Typed[t, Or[q[[1]] == 0, "rationalMultiplication"["inverseOfPair"[q], "rationalOfPair"[q]] == 1]]}, "inverseOfPair"[p] == "inverseOfPair"[q]],
				Function[{Typed[zq, q[[1]] == 0]},
					EqualityTransitivity["inverseOfPairZero"[p, "numeratorZero"[q, p, EqualitySymmetry[e], zq]], EqualitySymmetry["inverseOfPairZero"[q, zq]]]
				],
				Function[{Typed[uq, "rationalMultiplication"["inverseOfPair"[q], "rationalOfPair"[q]] == 1]}, "inverseUniqueness"[
					"inverseOfPair"[p],
					"inverseOfPair"[q],
					"rationalOfPair"[q],
					EqualityTransitivity[
						EqualityCongruence[Function[{Typed[w, Rationals]}, "rationalMultiplication"["inverseOfPair"[p], w]], EqualitySymmetry[QuotientSoundness[e]]],
						up
					],
					uq
				]],
				"inverseOrZero"[q[[2]], q[[1]]]
			]],
			"inverseOrZero"[p[[2]], p[[1]]]
		]]
	],
	TypeTheoryDefinition[
		"rationalInverse",
		Typed[
			Function[{Typed[x, Rationals]}, QuotientLift[
				Function[{Typed[p, pairs]}, "inverseOfPair"[p]],
				Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]}, "inverseRespects"[p, q, e]],
				x
			]],
			TypeSpecifier[{Rationals} -> Rationals]
		]
	],
	TypeTheoryDefinition[
		"rationalDivision",
		Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalMultiplication"[x, "rationalInverse"[y]]], TypeSpecifier[{Rationals, Rationals} -> Rationals]]
	],
	(* a class with numerator 0 is 0 *)
	rationalTheorem[
		"zeroClass",
		ForAll[{Typed[p, pairs]}, Implies[p[[1]] == 0, "rationalOfPair"[p] == 0]],
		{TypeTheoryTactic["Introduce", p, h], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["PolynomialReduce"]}
	],
	TypeTheoryTheorem[
		RationalMultiplicationInverse,
		ForAll[{Typed[x, Rationals]}, Implies[Not[x == 0], x "rationalInverse"[x] == 1]],
		Function[{Typed[x, Rationals]}, Construct[
			QuotientInduction,
			pairs,
			"rationalRelation",
			Function[{Typed[w, Rationals]}, Implies[Not[w == 0], w "rationalInverse"[w] == 1]],
			Function[{Typed[p, pairs], Typed[nonzero, Not["rationalOfPair"[p] == 0]]}, InductiveRecursor[Or][
				Function[{Typed[t, Or[p[[1]] == 0, "rationalMultiplication"["inverseOfPair"[p], "rationalOfPair"[p]] == 1]]},
					"rationalOfPair"[p] "rationalInverse"["rationalOfPair"[p]] == 1
				],
				Function[{Typed[z, p[[1]] == 0]}, FalseElimination[nonzero["zeroClass"[p, z]]]],
				Function[{Typed[u, "rationalMultiplication"["inverseOfPair"[p], "rationalOfPair"[p]] == 1]},
					EqualityTransitivity[RationalMultiplicationCommutativity["rationalOfPair"[p], "inverseOfPair"[p]], u]
				],
				"inverseOrZero"[p[[2]], p[[1]]]
			]],
			x
		]]
	],
	rationalTheorem[RationalInverseZero, "rationalInverse"[0] == 0, {TypeTheoryTactic["Reflexivity"]}],

	(* Deciding equations: "rationalEqual" lifts the comparison of a (d + 1) and c (b + 1) with "integerEqual"
	   from pairs; related pairs give equivalent equations, so the same Boolean *)
	rationalTheorem[
		"crossEquationRight",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]}, Implies["rationalRelation"[q, s], Implies[
			p[[1]] "integerOfNatural"[q[[2]] + 1] == q[[1]] "integerOfNatural"[p[[2]] + 1],
			p[[1]] "integerOfNatural"[s[[2]] + 1] == s[[1]] "integerOfNatural"[p[[2]] + 1]
		]]],
		{TypeTheoryTactic["Introduce", p, q, s, e, h], TypeTheoryTactic["Apply", "integerCancelScaled"[q[[2]]]], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"crossEquationRightBack",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]}, Implies["rationalRelation"[q, s], Implies[
			p[[1]] "integerOfNatural"[s[[2]] + 1] == s[[1]] "integerOfNatural"[p[[2]] + 1],
			p[[1]] "integerOfNatural"[q[[2]] + 1] == q[[1]] "integerOfNatural"[p[[2]] + 1]
		]]],
		{TypeTheoryTactic["Introduce", p, q, s, e, h], TypeTheoryTactic["Apply", "integerCancelScaled"[s[[2]]]], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"crossEquationLeft",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]}, Implies["rationalRelation"[p, q], Implies[
			p[[1]] "integerOfNatural"[s[[2]] + 1] == s[[1]] "integerOfNatural"[p[[2]] + 1],
			q[[1]] "integerOfNatural"[s[[2]] + 1] == s[[1]] "integerOfNatural"[q[[2]] + 1]
		]]],
		{TypeTheoryTactic["Introduce", p, q, s, e, h], TypeTheoryTactic["Apply", "integerCancelScaled"[p[[2]]]], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"crossEquationLeftBack",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]}, Implies["rationalRelation"[p, q], Implies[
			q[[1]] "integerOfNatural"[s[[2]] + 1] == s[[1]] "integerOfNatural"[q[[2]] + 1],
			p[[1]] "integerOfNatural"[s[[2]] + 1] == s[[1]] "integerOfNatural"[p[[2]] + 1]
		]]],
		{TypeTheoryTactic["Introduce", p, q, s, e, h], TypeTheoryTactic["Apply", "integerCancelScaled"[q[[2]]]], TypeTheoryTactic["PolynomialReduce"]}
	],
	TypeTheoryDefinition[
		"rationalEqualOfPair",
		Typed[
			Function[{Typed[p, pairs], Typed[y, Rationals]}, QuotientLift[
				Function[{Typed[q, pairs]}, "integerEqual"[p[[1]] "integerOfNatural"[q[[2]] + 1], q[[1]] "integerOfNatural"[p[[2]] + 1]]],
				Function[{Typed[q, pairs], Typed[s, pairs], Typed[e, "rationalRelation"[q, s]]}, "integerEqualOfEquivalent"[
					p[[1]] "integerOfNatural"[q[[2]] + 1],
					q[[1]] "integerOfNatural"[p[[2]] + 1],
					p[[1]] "integerOfNatural"[s[[2]] + 1],
					s[[1]] "integerOfNatural"[p[[2]] + 1],
					EquivalentIntroduction["crossEquationRight"[p, q, s, e], "crossEquationRightBack"[p, q, s, e]]
				]],
				y
			]],
			TypeSpecifier[{pairs, Rationals} -> Booleans]
		]
	],
	TypeTheoryDefinition[
		"rationalEqual",
		Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]}, QuotientLift[
				Function[{Typed[p, pairs]}, "rationalEqualOfPair"[p, y]],
				Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]},
					Construct[
						QuotientInduction,
						pairs,
						"rationalRelation",
						Function[{Typed[z, Rationals]}, "rationalEqualOfPair"[p, z] == "rationalEqualOfPair"[q, z]],
						Function[{Typed[s, pairs]}, "integerEqualOfEquivalent"[
							p[[1]] "integerOfNatural"[s[[2]] + 1],
							s[[1]] "integerOfNatural"[p[[2]] + 1],
							q[[1]] "integerOfNatural"[s[[2]] + 1],
							s[[1]] "integerOfNatural"[q[[2]] + 1],
							EquivalentIntroduction["crossEquationLeft"[p, q, s, e], "crossEquationLeftBack"[p, q, s, e]]
						]],
						y
					]
				],
				x
			]],
			TypeSpecifier[{Rationals, Rationals} -> Booleans]
		]
	],
	rationalTheorem[
		"rationalEqualTrue",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies["rationalEqual"[x, y] == "true", x == y]],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q, h],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Exact", "integerEqualTrue"[p[[1]] "integerOfNatural"[q[[2]] + 1], q[[1]] "integerOfNatural"[p[[2]] + 1], h]]
		}
	],
	rationalTheorem[
		"rationalEqualSelf",
		ForAll[{Typed[x, Rationals]}, "rationalEqual"[x, x] == "true"],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Exact", "integerEqualSelf"[p[[1]] "integerOfNatural"[p[[2]] + 1]]]
		}
	],
	TypeTheoryTheorem[
		"rationalEqualFalse",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies["rationalEqual"[x, y] == "false", Not[x == y]]],
		Function[{Typed[x, Rationals], Typed[y, Rationals], Typed[e, "rationalEqual"[x, y] == "false"], Typed[k, x == y]},
			"falseNotTrue"[EqualityTransitivity[
				EqualitySymmetry[e],
				EqualityTransitivity[EqualityCongruence[Function[{Typed[z, Rationals]}, "rationalEqual"[x, z]], EqualitySymmetry[k]], "rationalEqualSelf"[x]]
			]]
		]
	],
	TypeTheoryDefinition[
		RationalEqualityDecidable,
		Function[{Typed[x, Rationals], Typed[y, Rationals]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["rationalEqual"[x, y] == b, Decidable[x == y]]],
			Function[{Typed[e, "rationalEqual"[x, y] == "false"]}, DecidableFalse["rationalEqualFalse"[x, y, e]]],
			Function[{Typed[e, "rationalEqual"[x, y] == "true"]}, DecidableTrue["rationalEqualTrue"[x, y, e]]],
			"rationalEqual"[x, y]
		][EqualityReflexivity["rationalEqual"[x, y]]]],
		"Instance" -> True
	],

	(* Order: x <= y when y is x plus n / (d + 1) for natural numbers n and d, and x < y when n is at least 1 *)
	TypeTheoryDefinition[
		"rationalLessEqual",
		Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]},
				Exists[{Typed[n, NonNegativeIntegers], Typed[d, NonNegativeIntegers]}, y == "rationalAddition"[x, "rationalOfPair"[Pair["integerOfNatural"[n], d]]]]
			],
			TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]
		]
	],
	TypeTheoryDefinition[
		"rationalLess",
		Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]},
				Exists[{Typed[n, NonNegativeIntegers], Typed[d, NonNegativeIntegers]}, y == "rationalAddition"[x, "rationalOfPair"[Pair["integerOfNatural"[n + 1], d]]]]
			],
			TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]
		]
	],
	TypeTheoryDefinition["rationalGreaterEqual", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalLessEqual"[y, x]], TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]]],
	TypeTheoryDefinition["rationalGreater", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalLess"[y, x]], TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]]],
	(* x is x plus 0 / 1 *)
	TypeTheoryTheorem[
		RationalLessEqualReflexivity,
		ForAll[{Typed[x, Rationals]}, x <= x],
		Function[{Typed[x, Rationals]}, ExistsIntroduction[0, ExistsIntroduction[0, EqualitySymmetry[RationalAdditionZero[x]]]]]
	],
	(* the square of the class of (a, b) is that of (a a, b b + b + b), and a a is a natural number *)
	rationalTheorem[
		"squareWitness",
		ForAll[
			{Typed[p, pairs], Typed[n, NonNegativeIntegers]},
			Implies[
				p[[1]] p[[1]] == 0 + "integerOfNatural"[n],
				"rationalOfPair"[p] "rationalOfPair"[p] == 0 + "rationalOfPair"[Pair["integerOfNatural"[n], p[[2]] p[[2]] + p[[2]] + p[[2]]]]
			]
		],
		{TypeTheoryTactic["Introduce", p, n, h], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["PolynomialReduce"]}
	],
	TypeTheoryTheorem[
		RationalSquareNonnegative,
		ForAll[{Typed[x, Rationals]}, 0 <= x x],
		Function[{Typed[x, Rationals]}, Construct[
			QuotientInduction,
			pairs,
			"rationalRelation",
			Function[{Typed[w, Rationals]}, 0 <= w w],
			Function[{Typed[p, pairs]}, InductiveRecursor[Exists][
				Function[{Typed[o, 0 <= p[[1]] p[[1]]]}, 0 <= "rationalOfPair"[p] "rationalOfPair"[p]],
				Function[{Typed[n, NonNegativeIntegers], Typed[e, p[[1]] p[[1]] == 0 + "integerOfNatural"[n]]},
					ExistsIntroduction[n, ExistsIntroduction[p[[2]] p[[2]] + p[[2]] + p[[2]], "squareWitness"[p, n, e]]]
				],
				IntegerSquareNonnegative[p[[1]]]
			]],
			x
		]]
	]
}]
