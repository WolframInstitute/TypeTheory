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
"quotientSoundness", and "Ring" on the equation of integers of the pairs.

The inverse computes. For a pair (m, n) of natural numbers, standing for the integer m - n, the inverse of
(m - n) / (b + 1) is (b + 1) / (m - n), by recursion on m and then on n, and 0 where m - n is 0. It takes the
same value on (m + k, n + k), so on every pair of an integer, and lifts to the integers. Where a is not 0,
its product with the class of (a, b) is 1. So the inverses of related pairs are both 0, or are inverses of
the same rational and equal: the inverse lifts to the rationals.

Equations of rationals are decidable: "rationalEqualityDecidable" decides x == y with the Boolean
"rationalEqual", which compares a (d + 1) and c (b + 1) with "integerEqual", so Decide and the tactic
"Decide" settle an equation of rational literals by computation.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[rationalsEnvironment]


(* ::Section:: *)
(*Usage Messages*)



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
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, "integerOfPair"["pair"[n + k, n]] == "integerOfNatural"[k]],
		{TypeTheoryTactic["Introduce", n, k], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		"integerOfDifferenceNegative",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, "integerOfPair"["pair"[n, n + k]] == "integerNegation"["integerOfNatural"[k]]],
		{TypeTheoryTactic["Introduce", n, k], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
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
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[a == b, "integerRelation"["pair"[a, b], "pair"[0, 0]]]],
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
				"quotientSoundness"["relationOfEqual"[r[[1]], r[[2]], "multiplicationCancellation"[d, r[[1]], r[[2]], "scaledPairEquation"[d, r[[1]], r[[2]],
					"integerExact"["pair"[r[[1]] (d + 1) + r[[2]] 0, r[[1]] 0 + r[[2]] (d + 1)], "pair"[0, 0], h]
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
					Function[{Typed[f, "integerEqual"[c, d] == "false"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
					Function[{Typed[f, "integerEqual"[c, d] == "true"]},
						"falseElimination"["integerEqualFalse"[a, b, e]["equivalentBackward"[h]["integerEqualTrue"[c, d, f]]]]
					],
					"integerEqual"[c, d]
				]["equalityReflexivity"["integerEqual"[c, d]]]],
				Function[{Typed[e, "integerEqual"[a, b] == "true"]}, InductiveRecursor[Booleans][
					Function[{Typed[y, Booleans]}, Implies["integerEqual"[c, d] == y, "integerEqual"[a, b] == "integerEqual"[c, d]]],
					Function[{Typed[f, "integerEqual"[c, d] == "false"]},
						"falseElimination"["integerEqualFalse"[c, d, f]["equivalentForward"[h]["integerEqualTrue"[a, b, e]]]]
					],
					Function[{Typed[f, "integerEqual"[c, d] == "true"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
					"integerEqual"[c, d]
				]["equalityReflexivity"["integerEqual"[c, d]]]],
				"integerEqual"[a, b]
			]["equalityReflexivity"["integerEqual"[a, b]]]
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
		Typed[Function[{Typed[x, Integers]}, "rationalOfPair"["pair"[x, 0]]], TypeSpecifier[{Integers} -> Rationals]],
		"Coercion" -> True
	],

	(* negating, adding and multiplying pairs respect the relation, each a polynomial combination of it:
	   -(a, b) is (-a, b), (a, b) + (c, d) is (a (d + 1) + c (b + 1), b d + b + d), and (a, b) (c, d) is (a c, b d + b + d) *)
	rationalTheorem[
		"rationalNegationRespects",
		ForAll[{Typed[p, pairs], Typed[q, pairs]}, Implies["rationalRelation"[p, q], "rationalRelation"["pair"[-p[[1]], p[[2]]], "pair"[-q[[1]], q[[2]]]]]],
		{TypeTheoryTactic["Introduce", p, q, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalAdditionRespectsLeft",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[p, q], "rationalRelation"[
				"pair"[p[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] s[[2]] + p[[2]] + s[[2]]],
				"pair"[q[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[q[[2]] + 1], q[[2]] s[[2]] + q[[2]] + s[[2]]]
			]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalAdditionRespectsRight",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[q, s], "rationalRelation"[
				"pair"[p[[1]] "integerOfNatural"[q[[2]] + 1] + q[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] q[[2]] + p[[2]] + q[[2]]],
				"pair"[p[[1]] "integerOfNatural"[s[[2]] + 1] + s[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] s[[2]] + p[[2]] + s[[2]]]
			]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalMultiplicationRespectsLeft",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[p, q], "rationalRelation"[
				"pair"[p[[1]] s[[1]], p[[2]] s[[2]] + p[[2]] + s[[2]]],
				"pair"[q[[1]] s[[1]], q[[2]] s[[2]] + q[[2]] + s[[2]]]
			]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	rationalTheorem[
		"rationalMultiplicationRespectsRight",
		ForAll[{Typed[p, pairs], Typed[q, pairs], Typed[s, pairs]},
			Implies["rationalRelation"[q, s], "rationalRelation"[
				"pair"[p[[1]] q[[1]], p[[2]] q[[2]] + p[[2]] + q[[2]]],
				"pair"[p[[1]] s[[1]], p[[2]] s[[2]] + p[[2]] + s[[2]]]
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
				Function[{Typed[p, pairs]}, "rationalOfPair"["pair"[-p[[1]], p[[2]]]]],
				Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]}, "quotientSoundness"["rationalNegationRespects"[p, q, e]]],
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
					"pair"[p[[1]] "integerOfNatural"[q[[2]] + 1] + q[[1]] "integerOfNatural"[p[[2]] + 1], p[[2]] q[[2]] + p[[2]] + q[[2]]]
				]],
				Function[{Typed[q, pairs], Typed[s, pairs], Typed[e, "rationalRelation"[q, s]]}, "quotientSoundness"["rationalAdditionRespectsRight"[p, q, s, e]]],
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
						Function[{Typed[s, pairs]}, "quotientSoundness"["rationalAdditionRespectsLeft"[p, q, s, e]]],
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
				Function[{Typed[q, pairs]}, "rationalOfPair"["pair"[p[[1]] q[[1]], p[[2]] q[[2]] + p[[2]] + q[[2]]]]],
				Function[{Typed[q, pairs], Typed[s, pairs], Typed[e, "rationalRelation"[q, s]]}, "quotientSoundness"["rationalMultiplicationRespectsRight"[p, q, s, e]]],
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
						Function[{Typed[s, pairs]}, "quotientSoundness"["rationalMultiplicationRespectsLeft"[p, q, s, e]]],
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
			Implies[a == c, Implies[b == d, "rationalOfPair"["pair"[a, b]] == "rationalOfPair"["pair"[c, d]]]]
		],
		Function[
			{
				TypedImplicit[a, Integers], TypedImplicit[c, Integers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[d, NonNegativeIntegers],
				Typed[e, a == c], Typed[f, b == d]
			},
			"equalityTransitivity"[
				"equalityCongruence"[Function[{Typed[w, Integers]}, "rationalOfPair"["pair"[w, b]]], e],
				"equalityCongruence"[Function[{Typed[w, NonNegativeIntegers]}, "rationalOfPair"["pair"[c, w]]], f]
			]
		]
	],
	rationalTheorem[
		"scaledClass",
		ForAll[
			{Typed[a, Integers], Typed[b, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"rationalOfPair"["pair"[a, b]] == "rationalOfPair"["pair"[a "integerOfNatural"[k + 1], b k + b + k]]
		],
		{TypeTheoryTactic["Introduce", a, b, k], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],

	(* the laws of a commutative ring: by induction on each rational, then the relation of the two pairs,
	   an equation of integers, or the equations of their components *)
	rationalTheorem[
		"rationalAdditionCommutativity",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x + y == y + x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		"rationalAdditionAssociativity",
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
		"rationalAdditionZero",
		ForAll[{Typed[x, Rationals]}, x + 0 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	(* x + -x is read as x - x, so the negation is written out *)
	rationalTheorem[
		"rationalAdditionNegation",
		ForAll[{Typed[x, Rationals]}, x + "rationalNegation"[x] == 0],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		"rationalMultiplicationCommutativity",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x y == y x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		"rationalMultiplicationAssociativity",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x y) z == x (y z)],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		"rationalMultiplicationOne",
		ForAll[{Typed[x, Rationals]}, x * 1 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", "quotientSoundness"],
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
		"rationalDistributivity",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, x (y + z) == x y + x z],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Exact", "equalityTransitivity"[
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
		"rationalSubtractionNegation",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x - y == x + "rationalNegation"[y]],
		{TypeTheoryTactic["Introduce", x, y], TypeTheoryTactic["Reflexivity"]}
	],
	(* the integers keep their sums and products among the rationals; the coercion is written out *)
	rationalTheorem[
		"rationalOfIntegerAddition",
		ForAll[{Typed[a, Integers], Typed[b, Integers]}, "rationalOfInteger"[a + b] == "rationalOfInteger"[a] + "rationalOfInteger"[b]],
		{TypeTheoryTactic["Introduce", a, b], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		"rationalOfIntegerMultiplication",
		ForAll[{Typed[a, Integers], Typed[b, Integers]}, "rationalOfInteger"[a b] == "rationalOfInteger"[a] "rationalOfInteger"[b]],
		{TypeTheoryTactic["Introduce", a, b], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],

	(* The rest of the laws of a commutative ring, as "Ring" names them, with which it builds the normal forms of
	   rationals from the rationals' own laws: the laws on the other side, the products with 0, a negation as the
	   product with -1, the powers, and the rational of a negation and of a power of integers. *)
	rationalTheorem[
		"rationalAdditionZeroLeft",
		ForAll[{Typed[x, Rationals]}, 0 + x == x],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Rewrite", "rationalAdditionCommutativity"], TypeTheoryTactic["Exact", "rationalAdditionZero"[x]]}
	],
	rationalTheorem[
		"rationalMultiplicationOneLeft",
		ForAll[{Typed[x, Rationals]}, 1 x == x],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Rewrite", "rationalMultiplicationCommutativity"], TypeTheoryTactic["Exact", "rationalMultiplicationOne"[x]]}
	],
	rationalTheorem[
		"rationalMultiplicationZeroRight",
		ForAll[{Typed[x, Rationals]}, x 0 == 0],
		{
			TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem[
		"rationalMultiplicationZeroLeft",
		ForAll[{Typed[x, Rationals]}, 0 x == 0],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Rewrite", "rationalMultiplicationCommutativity"], TypeTheoryTactic["Exact", "rationalMultiplicationZeroRight"[x]]}
	],
	rationalTheorem[
		"rationalDistributivityRight",
		ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x + y) z == x z + y z],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["RewriteRepeated",
				"rationalMultiplicationCommutativity"[x + y, z], "rationalDistributivity", "rationalMultiplicationCommutativity"[z, x], "rationalMultiplicationCommutativity"[z, y]
			]
		}
	],
	rationalTheorem[
		"rationalNegationProduct",
		ForAll[{Typed[x, Rationals]}, -x == Typed[-1, Rationals] x],
		{
			TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]
		}
	],
	rationalTheorem["rationalPowerZero", ForAll[{Typed[x, Rationals]}, x^0 == 1], {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Reflexivity"]}],
	rationalTheorem[
		"rationalPowerSuccessor",
		ForAll[{Typed[x, Rationals], Typed[n, NonNegativeIntegers]}, x^(n + 1) == x^n x],
		{TypeTheoryTactic["Introduce", x, n], TypeTheoryTactic["Reflexivity"]}
	],
	rationalTheorem[
		"rationalPowerOne",
		ForAll[{Typed[x, Rationals]}, x^1 == x],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Change", 1 x == x], TypeTheoryTactic["Exact", "rationalMultiplicationOneLeft"[x]]}
	],
	rationalTheorem[
		"rationalPowerAddition",
		ForAll[{Typed[x, Rationals], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, x^(a + b) == x^a x^b],
		{
			TypeTheoryTactic["Introduce", x, a, b], TypeTheoryTactic["Induction", b],
			TypeTheoryTactic["Change", x^a == x^a 1], TypeTheoryTactic["Exact", "equalitySymmetry"["rationalMultiplicationOne"[x^a]]],
			TypeTheoryTactic["Introduce", k, ih], TypeTheoryTactic["Change", x^(a + k) x == x^a (x^k x)], TypeTheoryTactic["Rewrite", ih],
			TypeTheoryTactic["Exact", "rationalMultiplicationAssociativity"[x^a, x^k, x]]
		}
	],
	rationalTheorem[
		"rationalOfIntegerNegation",
		ForAll[{Typed[z, Integers]}, "rationalOfInteger"[-z] == -"rationalOfInteger"[z]],
		{TypeTheoryTactic["Introduce", z], TypeTheoryTactic["Reflexivity"]}
	],
	rationalTheorem[
		"rationalOfIntegerPower",
		ForAll[{Typed[z, Integers], Typed[n, NonNegativeIntegers]}, "rationalOfInteger"[z^n] == "rationalOfInteger"[z]^n],
		{
			TypeTheoryTactic["Introduce", z, n], TypeTheoryTactic["Induction", n], TypeTheoryTactic["Reflexivity"],
			TypeTheoryTactic["Introduce", k, ih], TypeTheoryTactic["Change", "rationalOfInteger"[z^k z] == "rationalOfInteger"[z]^k "rationalOfInteger"[z]],
			TypeTheoryTactic["Rewrite", "rationalOfIntegerMultiplication"], TypeTheoryTactic["Rewrite", ih]
		}
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
					"rationalOfPair"["pair"["integerOfNatural"[0], 0]],
					Function[{Typed[k, NonNegativeIntegers], Typed[v, Rationals]}, "rationalOfPair"["pair"["integerNegation"["integerOfNatural"[b + 1]], k]]],
					n
				]],
				Function[{Typed[j, NonNegativeIntegers], Typed[f, TypeSpecifier[{NonNegativeIntegers} -> Rationals]]}, Function[{Typed[n, NonNegativeIntegers]},
					InductiveRecursor[NonNegativeIntegers][
						Function[{Typed[t, NonNegativeIntegers]}, Rationals],
						"rationalOfPair"["pair"["integerOfNatural"[b + 1], j]],
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
			TypeTheoryTactic["Rewrite", "additionCommutativity"[k, m]],
			TypeTheoryTactic["Rewrite", "additionCommutativity"[k, n]],
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
			"equalityTransitivity"[
				"equalitySymmetry"["differenceInverseShift"[b, q[[1]], q[[2]], s[[2]]]],
				"equalityTransitivity"[
					"equalityCongruence"[Function[{Typed[c, NonNegativeIntegers]}, "differenceInverse"[b, c, q[[2]] + s[[2]]]], e],
					"equalityTransitivity"[
						"equalityCongruence"[Function[{Typed[c, NonNegativeIntegers]}, "differenceInverse"[b, s[[1]] + q[[2]], c]], "additionCommutativity"[q[[2]], s[[2]]]],
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
			"equalitySubstitution",
			Integers,
			Function[{Typed[w, Integers]}, "inverseOfPair"["pair"[w, p[[2]]]] == 0],
			"integerOfNatural"[0],
			p[[1]],
			"equalitySymmetry"[h],
			"equalityReflexivity"["rationalOfInteger"["integerOfNatural"[0]]]
		]]
	],
	rationalTheorem[
		"unitProduct",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			"rationalMultiplication"["differenceInverse"[b, i + 1, 0], "rationalOfPair"["pair"["integerOfNatural"[i + 1], b]]] == 1
		],
		{TypeTheoryTactic["Introduce", b, i], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],
	rationalTheorem[
		"negativeUnitProduct",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			"rationalMultiplication"["differenceInverse"[b, 0, i + 1], "rationalOfPair"["pair"["integerNegation"["integerOfNatural"[i + 1]], b]]] == 1
		],
		{TypeTheoryTactic["Introduce", b, i], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],
	TypeTheoryTheorem[
		"positiveInverseProduct",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			"rationalMultiplication"["differenceInverse"[b, n + (i + 1), n], "rationalOfPair"["pair"["integerOfPair"["pair"[n + (i + 1), n]], b]]] == 1
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "equalityTransitivity"[
			"equalityCongruence"[
				Function[{Typed[w, Rationals]}, "rationalMultiplication"[w, "rationalOfPair"["pair"["integerOfPair"["pair"[n + (i + 1), n]], b]]]],
				"differenceInverseShiftLeft"[b, i + 1, 0, n]
			],
			"equalityTransitivity"[
				"equalityCongruence"[
					Function[{Typed[w, Integers]}, "rationalMultiplication"["differenceInverse"[b, i + 1, 0], "rationalOfPair"["pair"[w, b]]]],
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
			"rationalMultiplication"["differenceInverse"[b, n, n + (i + 1)], "rationalOfPair"["pair"["integerOfPair"["pair"[n, n + (i + 1)]], b]]] == 1
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "equalityTransitivity"[
			"equalityCongruence"[
				Function[{Typed[w, Rationals]}, "rationalMultiplication"[w, "rationalOfPair"["pair"["integerOfPair"["pair"[n, n + (i + 1)]], b]]]],
				"differenceInverseShiftLeft"[b, 0, i + 1, n]
			],
			"equalityTransitivity"[
				"equalityCongruence"[
					Function[{Typed[w, Integers]}, "rationalMultiplication"["differenceInverse"[b, 0, i + 1], "rationalOfPair"["pair"[w, b]]]],
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
				"integerOfPair"["pair"[n + j, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, n + j, n], "rationalOfPair"["pair"["integerOfPair"["pair"[n + j, n]], b]]] == 1
			]
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[j, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[t, NonNegativeIntegers]}, Or[
				"integerOfPair"["pair"[n + t, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, n + t, n], "rationalOfPair"["pair"["integerOfPair"["pair"[n + t, n]], b]]] == 1
			]],
			"orIntroductionLeft"["integerOfDifference"[n, 0]],
			Function[
				{
					Typed[t, NonNegativeIntegers],
					Typed[ih, Or[
						"integerOfPair"["pair"[n + t, n]] == 0,
						"rationalMultiplication"["differenceInverse"[b, n + t, n], "rationalOfPair"["pair"["integerOfPair"["pair"[n + t, n]], b]]] == 1
					]]
				},
				"orIntroductionRight"["positiveInverseProduct"[b, t, n]]
			],
			j
		]]
	],
	TypeTheoryTheorem[
		"pairInverseOrZero",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Or[
				"integerOfPair"["pair"[m, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"["pair"["integerOfPair"["pair"[m, n]], b]]] == 1
			]
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[Or][
			Function[{Typed[t, Or[n <= m, m < n]]}, Or[
				"integerOfPair"["pair"[m, n]] == 0,
				"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"["pair"["integerOfPair"["pair"[m, n]], b]]] == 1
			]],
			Function[{Typed[le, n <= m]}, InductiveRecursor[Exists][
				Function[{Typed[o, Exists[{Typed[j, NonNegativeIntegers]}, m == n + j]]}, Or[
					"integerOfPair"["pair"[m, n]] == 0,
					"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"["pair"["integerOfPair"["pair"[m, n]], b]]] == 1
				]],
				Function[{Typed[j, NonNegativeIntegers], Typed[ej, m == n + j]}, Construct[
					"equalitySubstitution",
					NonNegativeIntegers,
					Function[{Typed[c, NonNegativeIntegers]}, Or[
						"integerOfPair"["pair"[c, n]] == 0,
						"rationalMultiplication"["differenceInverse"[b, c, n], "rationalOfPair"["pair"["integerOfPair"["pair"[c, n]], b]]] == 1
					]],
					n + j,
					m,
					"equalitySymmetry"[ej],
					"nonnegativeInverseOrZero"[b, n, j]
				]],
				"lessEqualWitness"[n, m, le]
			]],
			Function[{Typed[lt, m < n]}, InductiveRecursor[Exists][
				Function[{Typed[o, Exists[{Typed[j, NonNegativeIntegers]}, n == m + 1 + j]]}, Or[
					"integerOfPair"["pair"[m, n]] == 0,
					"rationalMultiplication"["differenceInverse"[b, m, n], "rationalOfPair"["pair"["integerOfPair"["pair"[m, n]], b]]] == 1
				]],
				Function[{Typed[j, NonNegativeIntegers], Typed[ej, n == m + 1 + j]}, Construct[
					"equalitySubstitution",
					NonNegativeIntegers,
					Function[{Typed[c, NonNegativeIntegers]}, Or[
						"integerOfPair"["pair"[m, c]] == 0,
						"rationalMultiplication"["differenceInverse"[b, m, c], "rationalOfPair"["pair"["integerOfPair"["pair"[m, c]], b]]] == 1
					]],
					m + (j + 1),
					n,
					"equalityTransitivity"["successorAddition"[m, j], "equalitySymmetry"[ej]],
					"orIntroductionRight"["negativeInverseProduct"[b, j, m]]
				]],
				"lessEqualWitness"[m + 1, n, lt]
			]],
			"lessEqualTotality"[n, m]
		]]
	],
	TypeTheoryTheorem[
		"inverseOrZero",
		ForAll[
			{Typed[b, NonNegativeIntegers], Typed[x, Integers]},
			Or[x == 0, "rationalMultiplication"["inverseOfPair"["pair"[x, b]], "rationalOfPair"["pair"[x, b]]] == 1]
		],
		Function[{Typed[b, NonNegativeIntegers], Typed[x, Integers]}, Construct[
			QuotientInduction,
			differences,
			"integerRelation",
			Function[{Typed[w, Integers]}, Or[w == 0, "rationalMultiplication"["inverseOfPair"["pair"[w, b]], "rationalOfPair"["pair"[w, b]]] == 1]],
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
			"equalityTransitivity"[
				"equalitySymmetry"["rationalMultiplicationOne"[u]],
				"equalityTransitivity"[
					"equalityCongruence"[Function[{Typed[w, Rationals]}, u w], "equalitySymmetry"[hv]],
					"equalityTransitivity"[
						"equalityCongruence"[Function[{Typed[w, Rationals]}, u w], "rationalMultiplicationCommutativity"[v, x]],
						"equalityTransitivity"[
							"equalitySymmetry"["rationalMultiplicationAssociativity"[u, x, v]],
							"equalityTransitivity"[
								"equalityCongruence"[Function[{Typed[w, Rationals]}, w v], hu],
								"equalityTransitivity"["rationalMultiplicationCommutativity"["rationalOfInteger"["integerOfNatural"[1]], v], "rationalMultiplicationOne"[v]]
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
			Function[{Typed[zp, p[[1]] == 0]}, "equalityTransitivity"["inverseOfPairZero"[p, zp], "equalitySymmetry"["inverseOfPairZero"[q, "numeratorZero"[p, q, e, zp]]]]],
			Function[{Typed[up, "rationalMultiplication"["inverseOfPair"[p], "rationalOfPair"[p]] == 1]}, InductiveRecursor[Or][
				Function[{Typed[t, Or[q[[1]] == 0, "rationalMultiplication"["inverseOfPair"[q], "rationalOfPair"[q]] == 1]]}, "inverseOfPair"[p] == "inverseOfPair"[q]],
				Function[{Typed[zq, q[[1]] == 0]},
					"equalityTransitivity"["inverseOfPairZero"[p, "numeratorZero"[q, p, "equalitySymmetry"[e], zq]], "equalitySymmetry"["inverseOfPairZero"[q, zq]]]
				],
				Function[{Typed[uq, "rationalMultiplication"["inverseOfPair"[q], "rationalOfPair"[q]] == 1]}, "inverseUniqueness"[
					"inverseOfPair"[p],
					"inverseOfPair"[q],
					"rationalOfPair"[q],
					"equalityTransitivity"[
						"equalityCongruence"[Function[{Typed[w, Rationals]}, "rationalMultiplication"["inverseOfPair"[p], w]], "equalitySymmetry"["quotientSoundness"[e]]],
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
		{TypeTheoryTactic["Introduce", p, h], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["PolynomialReduce"]}
	],
	TypeTheoryTheorem[
		"rationalMultiplicationInverse",
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
				Function[{Typed[z, p[[1]] == 0]}, "falseElimination"[nonzero["zeroClass"[p, z]]]],
				Function[{Typed[u, "rationalMultiplication"["inverseOfPair"[p], "rationalOfPair"[p]] == 1]},
					"equalityTransitivity"["rationalMultiplicationCommutativity"["rationalOfPair"[p], "inverseOfPair"[p]], u]
				],
				"inverseOrZero"[p[[2]], p[[1]]]
			]],
			x
		]]
	],
	rationalTheorem["rationalInverseZero", "rationalInverse"[0] == 0, {TypeTheoryTactic["Reflexivity"]}],

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
					"equivalentIntroduction"["crossEquationRight"[p, q, s, e], "crossEquationRightBack"[p, q, s, e]]
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
							"equivalentIntroduction"["crossEquationLeft"[p, q, s, e], "crossEquationLeftBack"[p, q, s, e]]
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
			TypeTheoryTactic["Apply", "quotientSoundness"],
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
			"falseNotTrue"["equalityTransitivity"[
				"equalitySymmetry"[e],
				"equalityTransitivity"["equalityCongruence"[Function[{Typed[z, Rationals]}, "rationalEqual"[x, z]], "equalitySymmetry"[k]], "rationalEqualSelf"[x]]
			]]
		]
	],
	TypeTheoryDefinition[
		"rationalEqualityDecidable",
		Function[{Typed[x, Rationals], Typed[y, Rationals]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["rationalEqual"[x, y] == b, Decidable[x == y]]],
			Function[{Typed[e, "rationalEqual"[x, y] == "false"]}, "decidableFalse"["rationalEqualFalse"[x, y, e]]],
			Function[{Typed[e, "rationalEqual"[x, y] == "true"]}, "decidableTrue"["rationalEqualTrue"[x, y, e]]],
			"rationalEqual"[x, y]
		]["equalityReflexivity"["rationalEqual"[x, y]]]],
		"Instance" -> True
	],

	(* Order: x <= y when y is x plus n / (d + 1) for natural numbers n and d, and x < y when n is at least 1 *)
	TypeTheoryDefinition[
		"rationalLessEqual",
		Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]},
				Exists[{Typed[n, NonNegativeIntegers], Typed[d, NonNegativeIntegers]}, y == "rationalAddition"[x, "rationalOfPair"["pair"["integerOfNatural"[n], d]]]]
			],
			TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]
		]
	],
	TypeTheoryDefinition[
		"rationalLess",
		Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]},
				Exists[{Typed[n, NonNegativeIntegers], Typed[d, NonNegativeIntegers]}, y == "rationalAddition"[x, "rationalOfPair"["pair"["integerOfNatural"[n + 1], d]]]]
			],
			TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]
		]
	],
	TypeTheoryDefinition["rationalGreaterEqual", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalLessEqual"[y, x]], TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]]],
	TypeTheoryDefinition["rationalGreater", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalLess"[y, x]], TypeSpecifier[{Rationals, Rationals} -> TypeUniverse[0]]]],
	(* x is x plus 0 / 1 *)
	TypeTheoryTheorem[
		"rationalLessEqualReflexivity",
		ForAll[{Typed[x, Rationals]}, x <= x],
		Function[{Typed[x, Rationals]}, "existsIntroduction"[0, "existsIntroduction"[0, "equalitySymmetry"["rationalAdditionZero"[x]]]]]
	],
	(* the square of the class of (a, b) is that of (a a, b b + b + b), and a a is a natural number *)
	rationalTheorem[
		"squareWitness",
		ForAll[
			{Typed[p, pairs], Typed[n, NonNegativeIntegers]},
			Implies[
				p[[1]] p[[1]] == 0 + "integerOfNatural"[n],
				"rationalOfPair"[p] "rationalOfPair"[p] == 0 + "rationalOfPair"["pair"["integerOfNatural"[n], p[[2]] p[[2]] + p[[2]] + p[[2]]]]
			]
		],
		{TypeTheoryTactic["Introduce", p, n, h], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["PolynomialReduce"]}
	],
	TypeTheoryTheorem[
		"rationalSquareNonnegative",
		ForAll[{Typed[x, Rationals]}, 0 <= x x],
		Function[{Typed[x, Rationals]}, Construct[
			QuotientInduction,
			pairs,
			"rationalRelation",
			Function[{Typed[w, Rationals]}, 0 <= w w],
			Function[{Typed[p, pairs]}, InductiveRecursor[Exists][
				Function[{Typed[o, 0 <= p[[1]] p[[1]]]}, 0 <= "rationalOfPair"[p] "rationalOfPair"[p]],
				Function[{Typed[n, NonNegativeIntegers], Typed[e, p[[1]] p[[1]] == 0 + "integerOfNatural"[n]]},
					"existsIntroduction"[n, "existsIntroduction"[p[[2]] p[[2]] + p[[2]] + p[[2]], "squareWitness"[p, n, e]]]
				],
				"integerSquareNonnegative"[p[[1]]]
			]],
			x
		]]
	]
}]
