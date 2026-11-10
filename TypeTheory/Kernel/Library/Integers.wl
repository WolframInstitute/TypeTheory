(* ::Package:: *)

(*
The integers: TypeTheoryEnvironment["Integers"] is the prelude with them, built and checked the first time
it is asked for. An integer is a class of pairs (a, b) of natural numbers, standing for a - b, by the
relation that relates (a, b) and (c, d) when a + d == c + b: a quotient type, the way many textbooks build
the integers.

	Integers                      QuotientType["integerRelation"], shown as ℤ
	"integerOfNatural"[n]         the class of (n, 0), a coercion: a natural number where an integer is expected
	-x, x + y, x - y, x * y       "integerNegation", "integerAddition", "integerSubtraction" and "integerMultiplication"
	x <= y, x < y, x >= y, x > y  "integerLessEqual" and the others: y is x plus a natural number, at least 1 for <
	Quotient[x, y], Mod[x, y]     "integerQuotient", rounded down, and "integerMod", of the divisor's sign

An operation lifts a function on pairs with QuotientLift, given a proof that the function respects the
relation; a binary one lifts in one argument, then in the other. The proofs that the functions respect
the relation and the laws of a commutative ring are proved by the library's own tactics: "Induction" on a
class gives the class of a pair, "quotientSoundness" reduces an equation of classes to the relation of the
pairs, and "LinearArithmetic", "PolynomialReduce" and "Ring" prove that equation of natural numbers. The
kernel checks every proof as it checks any other.

Elaboration reads +, *, -, the comparisons, -x and negative literals as the integers' where the arguments
or the expected type are integers, and as the natural numbers' otherwise.

The quotient and the remainder of natural numbers, Quotient and Mod, are defined by recursion on the dividend, as the
role equations of "Quotient" and "Remainder" are, and registered: the registration is checked, and they compute on
literals; by a 0 divisor, the quotient is 0 and the remainder the dividend.

Equations of integers are decidable: "integerEqualityDecidable" decides x == y with the Boolean
"integerEqual", which compares a + d and c + b for the pairs (a, b) and (c, d), so Decide and the tactic
"Decide" settle an equation of integer literals by computation.

A square is at least 0, and so are sums and natural multiples of what is at least 0. Then
"integerLessEqualOfMultiple" gives x <= y from (d + 1) (y - x) == s where 0 <= s, which is how the tactic
"SumOfSquares" proves an inequality, s being a sum of squares of polynomials that Wolfram finds.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[integersEnvironment]


(* ::Section:: *)
(*Usage Messages*)



integersEnvironment::usage = "integersEnvironment[] gives the prelude with the integers, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations in order, each theorem proved by its tactics in the environment so far *)
integersEnvironment[] := integersEnvironment[] = withoutStoreTracking[
	libraryEnvironment["Integers", preludeEnvironment[], withStoreCleanup[Fold[addIntegerDeclaration, preludeEnvironment[], $integerDeclarations]]]
]

SetAttributes[integerTheorem, HoldAll]

addIntegerDeclaration[failure_Failure, _] := failure
addIntegerDeclaration[environment_, integerTheorem[name_, statement_, tactics_List]] :=
	TypeTheoryEnvironment[environment, {TypeTheoryTheorem[name, TypeTheoryProof[statement, environment, tactics]]}]
addIntegerDeclaration[environment_, declaration_] := TypeTheoryEnvironment[environment, {declaration}]

$integerDeclarations = {
	(* pairs (a, b) and (c, d) are related when a + d == c + b *)
	TypeTheoryDefinition[
		"integerRelation",
		Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			p[[1]] + q[[2]] == q[[1]] + p[[2]]
		]
	],
	TypeTheoryDefinition[Integers, Typed[QuotientType["integerRelation"], TypeUniverse[1]]],
	TypeTheoryDefinition[
		"integerOfPair",
		Typed[
			Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, QuotientIntroduction["integerRelation", p]],
			TypeSpecifier[{CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerOfNatural",
		Typed[Function[{Typed[n, NonNegativeIntegers]}, "integerOfPair"["pair"[n, 0]]], TypeSpecifier[{NonNegativeIntegers} -> Integers]],
		"Coercion" -> True
	],

	(* swapping a pair, adding two and multiplying two respect the relation *)
	integerTheorem[
		"integerNegationRespects",
		ForAll[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[p, q], "integerRelation"["pair"[p[[2]], p[[1]]], "pair"[q[[2]], q[[1]]]]]
		],
		{TypeTheoryTactic["Introduce", p, q, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	integerTheorem[
		"integerAdditionRespectsLeft",
		ForAll[
			{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[p, q], "integerRelation"["pair"[p[[1]] + s[[1]], p[[2]] + s[[2]]], "pair"[q[[1]] + s[[1]], q[[2]] + s[[2]]]]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	integerTheorem[
		"integerAdditionRespectsRight",
		ForAll[
			{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[q, s], "integerRelation"["pair"[p[[1]] + q[[1]], p[[2]] + q[[2]]], "pair"[p[[1]] + s[[1]], p[[2]] + s[[2]]]]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	integerTheorem[
		"integerMultiplicationRespectsLeft",
		ForAll[
			{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies[
				"integerRelation"[p, q],
				"integerRelation"[
					"pair"[p[[1]] s[[1]] + p[[2]] s[[2]], p[[1]] s[[2]] + p[[2]] s[[1]]],
					"pair"[q[[1]] s[[1]] + q[[2]] s[[2]], q[[1]] s[[2]] + q[[2]] s[[1]]]
				]
			]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	integerTheorem[
		"integerMultiplicationRespectsRight",
		ForAll[
			{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies[
				"integerRelation"[q, s],
				"integerRelation"[
					"pair"[p[[1]] q[[1]] + p[[2]] q[[2]], p[[1]] q[[2]] + p[[2]] q[[1]]],
					"pair"[p[[1]] s[[1]] + p[[2]] s[[2]], p[[1]] s[[2]] + p[[2]] s[[1]]]
				]
			]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],

	(* the operations: -(a, b) is (b, a), (a, b) + (c, d) is (a + c, b + d), and (a, b) (c, d) is
	   (a c + b d, a d + b c); a binary one lifts in its second argument for each pair, then in its first,
	   whose proof is by induction on the second *)
	TypeTheoryDefinition[
		"integerNegation",
		Typed[
			Function[{Typed[x, Integers]}, QuotientLift[
				Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "integerOfPair"["pair"[p[[2]], p[[1]]]]],
				Function[
					{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					"quotientSoundness"["integerNegationRespects"[p, q, e]]
				],
				x
			]],
			TypeSpecifier[{Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerAdditionOfPair",
		Typed[
			Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "integerOfPair"["pair"[p[[1]] + q[[1]], p[[2]] + q[[2]]]]],
				Function[
					{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[q, s]]},
					"quotientSoundness"["integerAdditionRespectsRight"[p, q, s, e]]
				],
				y
			]],
			TypeSpecifier[{CartesianProductType[NonNegativeIntegers, NonNegativeIntegers], Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerAddition",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "integerAdditionOfPair"[p, y]],
				Function[
					{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					Construct[
						QuotientInduction,
						CartesianProductType[NonNegativeIntegers, NonNegativeIntegers],
						"integerRelation",
						Function[{Typed[z, Integers]}, "integerAdditionOfPair"[p, z] == "integerAdditionOfPair"[q, z]],
						Function[{Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "quotientSoundness"["integerAdditionRespectsLeft"[p, q, s, e]]],
						y
					]
				],
				x
			]],
			TypeSpecifier[{Integers, Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerMultiplicationOfPair",
		Typed[
			Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "integerOfPair"["pair"[p[[1]] q[[1]] + p[[2]] q[[2]], p[[1]] q[[2]] + p[[2]] q[[1]]]]],
				Function[
					{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[q, s]]},
					"quotientSoundness"["integerMultiplicationRespectsRight"[p, q, s, e]]
				],
				y
			]],
			TypeSpecifier[{CartesianProductType[NonNegativeIntegers, NonNegativeIntegers], Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerMultiplication",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "integerMultiplicationOfPair"[p, y]],
				Function[
					{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					Construct[
						QuotientInduction,
						CartesianProductType[NonNegativeIntegers, NonNegativeIntegers],
						"integerRelation",
						Function[{Typed[z, Integers]}, "integerMultiplicationOfPair"[p, z] == "integerMultiplicationOfPair"[q, z]],
						Function[{Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "quotientSoundness"["integerMultiplicationRespectsLeft"[p, q, s, e]]],
						y
					]
				],
				x
			]],
			TypeSpecifier[{Integers, Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerSubtraction",
		Typed[Function[{Typed[x, Integers], Typed[y, Integers]}, "integerAddition"[x, "integerNegation"[y]]], TypeSpecifier[{Integers, Integers} -> Integers]]
	],

	(* x <= y when y is x plus a natural number; x < y when it is x plus one more *)
	TypeTheoryDefinition[
		"integerLessEqual",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, Exists[{Typed[n, NonNegativeIntegers]}, y == "integerAddition"[x, "integerOfNatural"[n]]]],
			TypeSpecifier[{Integers, Integers} -> TypeUniverse[0]]
		]
	],
	TypeTheoryDefinition[
		"integerLess",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, "integerLessEqual"["integerAddition"[x, "integerOfNatural"[1]], y]],
			TypeSpecifier[{Integers, Integers} -> TypeUniverse[0]]
		]
	],
	TypeTheoryDefinition["integerGreaterEqual", Typed[Function[{Typed[x, Integers], Typed[y, Integers]}, "integerLessEqual"[y, x]], TypeSpecifier[{Integers, Integers} -> TypeUniverse[0]]]],
	TypeTheoryDefinition["integerGreater", Typed[Function[{Typed[x, Integers], Typed[y, Integers]}, "integerLess"[y, x]], TypeSpecifier[{Integers, Integers} -> TypeUniverse[0]]]],

	(* the laws of a commutative ring: by induction on each integer, then the relation of the two pairs *)
	integerTheorem[
		"integerAdditionCommutativity",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, x + y == y + x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		"integerAdditionAssociativity",
		ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x + y) + z == x + (y + z)],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		"integerAdditionZero",
		ForAll[{Typed[x, Integers]}, x + 0 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	(* x + -x is read as x - x, so the negation is written out *)
	integerTheorem[
		"integerAdditionNegation",
		ForAll[{Typed[x, Integers]}, x + "integerNegation"[x] == 0],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		"integerMultiplicationCommutativity",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		"integerMultiplicationAssociativity",
		ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x y) z == x (y z)],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		"integerMultiplicationOne",
		ForAll[{Typed[x, Integers]}, x * 1 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		"integerDistributivity",
		ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x (y + z) == x y + x z],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Ring"]
		}
	],

	(* a difference is a sum with the negation, by computation *)
	integerTheorem[
		"integerSubtractionNegation",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, x - y == x + "integerNegation"[y]],
		{TypeTheoryTactic["Introduce", x, y], TypeTheoryTactic["Reflexivity"]}
	],

	(* the natural numbers keep their sums and products among the integers; the coercion is written out,
	   since Typed[m + n, Integers] would add the integers of m and n *)
	integerTheorem[
		"integerOfNaturalAddition",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "integerOfNatural"[m + n] == "integerOfNatural"[m] + "integerOfNatural"[n]],
		{TypeTheoryTactic["Introduce", m, n], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],
	integerTheorem[
		"integerOfNaturalMultiplication",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "integerOfNatural"[m n] == "integerOfNatural"[m] "integerOfNatural"[n]],
		{TypeTheoryTactic["Introduce", m, n], TypeTheoryTactic["Apply", "quotientSoundness"], TypeTheoryTactic["Ring"]}
	],

	(* The laws "Ring" normalizes integer polynomials by, beside those of a commutative ring: zero and one
	   on the left, distributivity on the right, negation as the product with -1, and the sums of literals
	   of opposite signs, which are two pairs and so not equal by computation, as literals of the same sign
	   are. A power by a natural number is a product, with the laws of powers, and the integers of the
	   natural numbers keep powers. *)
	integerTheorem["integerAdditionZeroLeft", ForAll[{Typed[x, Integers]}, 0 + x == x], {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}],
	integerTheorem["integerMultiplicationZeroLeft", ForAll[{Typed[x, Integers]}, 0 x == 0], {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}],
	integerTheorem["integerMultiplicationZeroRight", ForAll[{Typed[x, Integers]}, x 0 == 0], {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}],
	integerTheorem["integerMultiplicationOneLeft", ForAll[{Typed[x, Integers]}, 1 x == x], {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}],
	integerTheorem[
		"integerDistributivityRight",
		ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x + y) z == x z + y z],
		{TypeTheoryTactic["Introduce", x, y, z], TypeTheoryTactic["Ring"]}
	],
	integerTheorem[
		"integerNegationProduct",
		ForAll[{Typed[x, Integers]}, "integerNegation"[x] == "integerMultiplication"["integerNegation"[1], x]],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}
	],
	integerTheorem[
		"integerLiteralDifferenceNonnegative",
		ForAll[
			{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"integerOfNatural"[m + k] + "integerNegation"["integerOfNatural"[m]] == "integerOfNatural"[k]
		],
		{TypeTheoryTactic["Introduce", m, k], TypeTheoryTactic["Ring"]}
	],
	integerTheorem[
		"integerLiteralDifferenceNegative",
		ForAll[
			{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"integerOfNatural"[m] + "integerNegation"["integerOfNatural"[m + k]] == "integerNegation"["integerOfNatural"[k]]
		],
		{TypeTheoryTactic["Introduce", m, k], TypeTheoryTactic["Ring"]}
	],
	(* x^0 is 1 and x^(n + 1) is x^n x *)
	TypeTheoryDefinition[
		"integerPower",
		Typed[
			Function[{Typed[x, Integers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[k, NonNegativeIntegers]}, Integers],
				"integerOfNatural"[1],
				Function[{Typed[k, NonNegativeIntegers], Typed[p, Integers]}, "integerMultiplication"[p, x]],
				n
			]],
			TypeSpecifier[{Integers, NonNegativeIntegers} -> Integers]
		]
	],
	integerTheorem["integerPowerZero", ForAll[{Typed[x, Integers]}, "integerPower"[x, 0] == 1], {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Reflexivity"]}],
	integerTheorem[
		"integerPowerSuccessor",
		ForAll[{Typed[x, Integers], Typed[n, NonNegativeIntegers]}, "integerPower"[x, n + 1] == "integerPower"[x, n] x],
		{TypeTheoryTactic["Introduce", x, n], TypeTheoryTactic["Reflexivity"]}
	],
	integerTheorem[
		"integerPowerOne",
		ForAll[{Typed[x, Integers]}, "integerPower"[x, 1] == x],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Exact", "integerMultiplicationOneLeft"[x]]}
	],
	TypeTheoryTheorem[
		"integerPowerAddition",
		ForAll[
			{Typed[x, Integers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
			"integerPower"[x, a + b] == "integerPower"[x, a] "integerPower"[x, b]
		],
		Function[{Typed[x, Integers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[c, NonNegativeIntegers]}, "integerPower"[x, a + c] == "integerPower"[x, a] "integerPower"[x, c]],
			"equalitySymmetry"["integerMultiplicationOne"["integerPower"[x, a]]],
			Function[
				{Typed[c, NonNegativeIntegers], Typed[ih, "integerPower"[x, a + c] == "integerPower"[x, a] "integerPower"[x, c]]},
				"equalityTransitivity"[
					"equalityCongruence"[Function[{Typed[w, Integers]}, w x], ih],
					"integerMultiplicationAssociativity"["integerPower"[x, a], "integerPower"[x, c], x]
				]
			],
			b
		]]
	],
	TypeTheoryTheorem[
		"integerOfNaturalPower",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "integerOfNatural"[m^n] == "integerPower"["integerOfNatural"[m], n]],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[c, NonNegativeIntegers]}, "integerOfNatural"[m^c] == "integerPower"["integerOfNatural"[m], c]],
			"equalityReflexivity"["integerOfNatural"[1]],
			Function[
				{Typed[c, NonNegativeIntegers], Typed[ih, "integerOfNatural"[m^c] == "integerPower"["integerOfNatural"[m], c]]},
				"equalityTransitivity"[
					"integerOfNaturalMultiplication"[m^c, m],
					"equalityCongruence"[Function[{Typed[w, Integers]}, w "integerOfNatural"[m]], ih]
				]
			],
			n
		]]
	],

	(* x is x plus 0 *)
	integerTheorem[
		"integerLessEqualReflexivity",
		ForAll[{Typed[x, Integers]}, x <= x],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Exact", "existsIntroduction"[0, "equalitySymmetry"["integerAdditionZero"[x]]]]}
	],

	(* Deciding equations: the Boolean "integerEqual" lifts the comparison of a + d and c + b from pairs,
	   which takes the same value on equivalent equations, and it is "true" exactly where the integers are
	   equal; "integerEqualityDecidable" is the instance it gives, as "naturalNumberEqualityDecidable" is. *)
	TypeTheoryTheorem[
		"equalSelf",
		ForAll[{Typed[n, NonNegativeIntegers]}, "equal"[n, n] == "true"],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, "equal"[k, k] == "true"],
			"equalityReflexivity"["true"],
			Function[{Typed[k, NonNegativeIntegers], Typed[ih, "equal"[k, k] == "true"]}, ih],
			n
		]]
	],
	TypeTheoryTheorem[
		"equalOfEquivalent",
		ForAll[
			{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
			Implies[Equivalent[a == b, c == d], "equal"[a, b] == "equal"[c, d]]
		],
		Function[
			{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[h, Equivalent[a == b, c == d]]},
			InductiveRecursor[Booleans][
				Function[{Typed[x, Booleans]}, Implies["equal"[a, b] == x, "equal"[a, b] == "equal"[c, d]]],
				Function[{Typed[e, "equal"[a, b] == "false"]}, InductiveRecursor[Booleans][
					Function[{Typed[y, Booleans]}, Implies["equal"[c, d] == y, "equal"[a, b] == "equal"[c, d]]],
					Function[{Typed[f, "equal"[c, d] == "false"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
					Function[{Typed[f, "equal"[c, d] == "true"]}, "falseElimination"["equalFalse"[a, b, e]["equivalentBackward"[h]["equalTrue"[c, d, f]]]]],
					"equal"[c, d]
				]["equalityReflexivity"["equal"[c, d]]]],
				Function[{Typed[e, "equal"[a, b] == "true"]}, InductiveRecursor[Booleans][
					Function[{Typed[y, Booleans]}, Implies["equal"[c, d] == y, "equal"[a, b] == "equal"[c, d]]],
					Function[{Typed[f, "equal"[c, d] == "false"]}, "falseElimination"["equalFalse"[c, d, f]["equivalentForward"[h]["equalTrue"[a, b, e]]]]],
					Function[{Typed[f, "equal"[c, d] == "true"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
					"equal"[c, d]
				]["equalityReflexivity"["equal"[c, d]]]],
				"equal"[a, b]
			]["equalityReflexivity"["equal"[a, b]]]
		]
	],
	integerTheorem[
		"integerEqualRespectsRight",
		ForAll[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[q, s], Equivalent[p[[1]] + q[[2]] == q[[1]] + p[[2]], p[[1]] + s[[2]] == s[[1]] + p[[2]]]]
		],
		{
			TypeTheoryTactic["Introduce", p, q, s, h],
			TypeTheoryTactic["Constructor"],
			TypeTheoryTactic["Introduce", k], TypeTheoryTactic["LinearArithmetic"],
			TypeTheoryTactic["Introduce", k], TypeTheoryTactic["LinearArithmetic"]
		}
	],
	integerTheorem[
		"integerEqualRespectsLeft",
		ForAll[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[p, q], Equivalent[p[[1]] + s[[2]] == s[[1]] + p[[2]], q[[1]] + s[[2]] == s[[1]] + q[[2]]]]
		],
		{
			TypeTheoryTactic["Introduce", p, q, s, h],
			TypeTheoryTactic["Constructor"],
			TypeTheoryTactic["Introduce", k], TypeTheoryTactic["LinearArithmetic"],
			TypeTheoryTactic["Introduce", k], TypeTheoryTactic["LinearArithmetic"]
		}
	],
	TypeTheoryDefinition[
		"integerEqualOfPair",
		Typed[
			Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "equal"[p[[1]] + q[[2]], q[[1]] + p[[2]]]],
				Function[{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[q, s]]},
					"equalOfEquivalent"[p[[1]] + q[[2]], q[[1]] + p[[2]], p[[1]] + s[[2]], s[[1]] + p[[2]], "integerEqualRespectsRight"[p, q, s, e]]
				],
				y
			]],
			TypeSpecifier[{CartesianProductType[NonNegativeIntegers, NonNegativeIntegers], Integers} -> Booleans]
		]
	],
	TypeTheoryDefinition[
		"integerEqual",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "integerEqualOfPair"[p, y]],
				Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					Construct[
						QuotientInduction,
						CartesianProductType[NonNegativeIntegers, NonNegativeIntegers],
						"integerRelation",
						Function[{Typed[z, Integers]}, "integerEqualOfPair"[p, z] == "integerEqualOfPair"[q, z]],
						Function[{Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
							"equalOfEquivalent"[p[[1]] + s[[2]], s[[1]] + p[[2]], q[[1]] + s[[2]], s[[1]] + q[[2]], "integerEqualRespectsLeft"[p, q, s, e]]
						],
						y
					]
				],
				x
			]],
			TypeSpecifier[{Integers, Integers} -> Booleans]
		]
	],
	integerTheorem[
		"integerEqualTrue",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies["integerEqual"[x, y] == "true", x == y]],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q, h],
			TypeTheoryTactic["Apply", "quotientSoundness"],
			TypeTheoryTactic["Exact", "equalTrue"[p[[1]] + q[[2]], q[[1]] + p[[2]], h]]
		}
	],
	integerTheorem[
		"integerEqualSelf",
		ForAll[{Typed[x, Integers]}, "integerEqual"[x, x] == "true"],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Exact", "equalSelf"[p[[1]] + p[[2]]]]
		}
	],
	TypeTheoryTheorem[
		"integerEqualFalse",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies["integerEqual"[x, y] == "false", Not[x == y]]],
		Function[{Typed[x, Integers], Typed[y, Integers], Typed[e, "integerEqual"[x, y] == "false"], Typed[k, x == y]},
			"falseNotTrue"["equalityTransitivity"[
				"equalitySymmetry"[e],
				"equalityTransitivity"["equalityCongruence"[Function[{Typed[z, Integers]}, "integerEqual"[x, z]], "equalitySymmetry"[k]], "integerEqualSelf"[x]]
			]]
		]
	],
	TypeTheoryDefinition[
		"integerEqualityDecidable",
		Function[{Typed[x, Integers], Typed[y, Integers]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["integerEqual"[x, y] == b, Decidable[x == y]]],
			Function[{Typed[e, "integerEqual"[x, y] == "false"]}, "decidableFalse"["integerEqualFalse"[x, y, e]]],
			Function[{Typed[e, "integerEqual"[x, y] == "true"]}, "decidableTrue"["integerEqualTrue"[x, y, e]]],
			"integerEqual"[x, y]
		]["equalityReflexivity"["integerEqual"[x, y]]]],
		"Instance" -> True
	],

	(* Order: a square is at least 0, since for the pair (a, b) of an integer, a a + b b is a b + b a plus
	   (a - b)^2 or (b - a)^2, whichever of a and b is larger. Sums and natural multiples of what is at
	   least 0 are at least 0, and a positive multiple is at least 0 only where the integer is, since the
	   classes of pairs whose second is larger are negative. So x <= y follows from (d + 1) (y - x) == s
	   where 0 <= s, which "SumOfSquares" proves of a sum of squares. *)
	TypeTheoryTheorem[
		"lessEqualWitness",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies[m <= n, Exists[{Typed[k, NonNegativeIntegers]}, n == m + k]]],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[h, m <= n]},
			InductiveRecursor[LessEqual][
				Function[{Typed[j, NonNegativeIntegers], Typed[g, m <= j]}, Exists[{Typed[k, NonNegativeIntegers]}, j == m + k]],
				"existsIntroduction"[0, "equalitySymmetry"["additionZeroRight"[m]]],
				Function[{Typed[j, NonNegativeIntegers], Typed[g, m <= j], Typed[ih, Exists[{Typed[k, NonNegativeIntegers]}, j == m + k]]},
					InductiveRecursor[Exists][
						Function[{Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, j == m + k]]}, Exists[{Typed[k, NonNegativeIntegers]}, j + 1 == m + k]],
						Function[{Typed[k, NonNegativeIntegers], Typed[e, j == m + k]},
							"existsIntroduction"[k + 1, "equalityTransitivity"["equalityCongruence"["successor", e], "equalitySymmetry"["additionSuccessorRight"[m, k]]]]
						],
						ih
					]
				],
				h
			]
		]
	],
	integerTheorem[
		"squareIdentity",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, a a + (a + k) (a + k) == k k + (a (a + k) + (a + k) a)],
		{TypeTheoryTactic["Introduce", a, k], TypeTheoryTactic["Ring"]}
	],
	integerTheorem[
		"squareIdentitySwapped",
		ForAll[{Typed[b, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, (b + 1 + k) (b + 1 + k) + b b == (k + 1) (k + 1) + ((b + 1 + k) b + b (b + 1 + k))],
		{TypeTheoryTactic["Introduce", b, k], TypeTheoryTactic["Ring"]}
	],
	TypeTheoryTheorem[
		"squareOfPairNonnegative",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Exists[{Typed[n, NonNegativeIntegers]}, a a + b b == n + (a b + b a)]],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
			InductiveRecursor[Or][
				Function[{Typed[o, Or[a <= b, b < a]]}, Exists[{Typed[n, NonNegativeIntegers]}, a a + b b == n + (a b + b a)]],
				Function[{Typed[h, a <= b]}, InductiveRecursor[Exists][
					Function[{Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, b == a + k]]}, Exists[{Typed[n, NonNegativeIntegers]}, a a + b b == n + (a b + b a)]],
					Function[{Typed[k, NonNegativeIntegers], Typed[e, b == a + k]}, "existsIntroduction"[k k, Construct[
						"equalitySubstitution",
						NonNegativeIntegers,
						Function[{Typed[c, NonNegativeIntegers]}, a a + c c == k k + (a c + c a)],
						a + k,
						b,
						"equalitySymmetry"[e],
						"squareIdentity"[a, k]
					]]],
					"lessEqualWitness"[a, b, h]
				]],
				Function[{Typed[h, b < a]}, InductiveRecursor[Exists][
					Function[{Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, a == b + 1 + k]]}, Exists[{Typed[n, NonNegativeIntegers]}, a a + b b == n + (a b + b a)]],
					Function[{Typed[k, NonNegativeIntegers], Typed[e, a == b + 1 + k]}, "existsIntroduction"[(k + 1) (k + 1), Construct[
						"equalitySubstitution",
						NonNegativeIntegers,
						Function[{Typed[c, NonNegativeIntegers]}, c c + b b == (k + 1) (k + 1) + (c b + b c)],
						b + 1 + k,
						a,
						"equalitySymmetry"[e],
						"squareIdentitySwapped"[b, k]
					]]],
					"lessEqualWitness"[b + 1, a, h]
				]],
				"lessEqualTotality"[a, b]
			]
		]
	],
	integerTheorem[
		"squareRelation",
		ForAll[
			{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Implies[a a + b b == n + (a b + b a), (a a + b b) + (0 + 0) == (0 + n) + (a b + b a)]
		],
		{TypeTheoryTactic["Introduce", a, b, n, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	TypeTheoryTheorem[
		"integerSquareNonnegative",
		ForAll[{Typed[z, Integers]}, 0 <= z z],
		Function[{Typed[z, Integers]}, Construct[
			QuotientInduction,
			CartesianProductType[NonNegativeIntegers, NonNegativeIntegers],
			"integerRelation",
			Function[{Typed[w, Integers]}, 0 <= w w],
			Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, InductiveRecursor[Exists][
				Function[
					{Typed[o, Exists[{Typed[n, NonNegativeIntegers]}, p[[1]] p[[1]] + p[[2]] p[[2]] == n + (p[[1]] p[[2]] + p[[2]] p[[1]])]]},
					0 <= "integerOfPair"[p] "integerOfPair"[p]
				],
				Function[{Typed[n, NonNegativeIntegers], Typed[e, p[[1]] p[[1]] + p[[2]] p[[2]] == n + (p[[1]] p[[2]] + p[[2]] p[[1]])]},
					"existsIntroduction"[n, "quotientSoundness"["squareRelation"[p[[1]], p[[2]], n, e]]]
				],
				"squareOfPairNonnegative"[p[[1]], p[[2]]]
			]],
			z
		]]
	],
	integerTheorem[
		"nonnegativeSum",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, (0 + "integerOfNatural"[m]) + (0 + "integerOfNatural"[n]) == 0 + "integerOfNatural"[m + n]],
		{TypeTheoryTactic["Introduce", m, n], TypeTheoryTactic["Ring"]}
	],
	TypeTheoryTheorem[
		"integerNonnegativeAddition",
		ForAll[{TypedImplicit[x, Integers], TypedImplicit[y, Integers]}, Implies[0 <= x, Implies[0 <= y, 0 <= x + y]]],
		Function[{TypedImplicit[x, Integers], TypedImplicit[y, Integers], Typed[hx, 0 <= x], Typed[hy, 0 <= y]},
			InductiveRecursor[Exists][
				Function[{Typed[o, 0 <= x]}, 0 <= x + y],
				Function[{Typed[m, NonNegativeIntegers], Typed[ex, x == 0 + "integerOfNatural"[m]]}, InductiveRecursor[Exists][
					Function[{Typed[o, 0 <= y]}, 0 <= x + y],
					Function[{Typed[n, NonNegativeIntegers], Typed[ey, y == 0 + "integerOfNatural"[n]]}, "existsIntroduction"[m + n, "equalityTransitivity"[
						"equalityCongruence"[Function[{Typed[w, Integers]}, w + y], ex],
						"equalityTransitivity"["equalityCongruence"[Function[{Typed[w, Integers]}, (0 + "integerOfNatural"[m]) + w], ey], "nonnegativeSum"[m, n]]
					]]],
					hy
				]],
				hx
			]
		]
	],
	integerTheorem[
		"nonnegativeScale",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, "integerOfNatural"[k] (0 + "integerOfNatural"[m]) == 0 + "integerOfNatural"[k m]],
		{TypeTheoryTactic["Introduce", k, m], TypeTheoryTactic["Ring"]}
	],
	TypeTheoryTheorem[
		"integerNonnegativeScaling",
		ForAll[{Typed[k, NonNegativeIntegers], TypedImplicit[x, Integers]}, Implies[0 <= x, 0 <= "integerOfNatural"[k] x]],
		Function[{Typed[k, NonNegativeIntegers], TypedImplicit[x, Integers], Typed[hx, 0 <= x]},
			InductiveRecursor[Exists][
				Function[{Typed[o, 0 <= x]}, 0 <= "integerOfNatural"[k] x],
				Function[{Typed[m, NonNegativeIntegers], Typed[ex, x == 0 + "integerOfNatural"[m]]}, "existsIntroduction"[k m, "equalityTransitivity"[
					"equalityCongruence"[Function[{Typed[w, Integers]}, "integerOfNatural"[k] w], ex],
					"nonnegativeScale"[k, m]
				]]],
				hx
			]
		]
	],
	(* equal classes have related pairs: "integerEqual" of the two is "true" *)
	TypeTheoryTheorem[
		"integerExact",
		ForAll[
			{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[r, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerOfPair"[q] == "integerOfPair"[r], "integerRelation"[q, r]]
		],
		Function[
			{
				Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]],
				Typed[r, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]],
				Typed[e, "integerOfPair"[q] == "integerOfPair"[r]]
			},
			"equalTrue"[q[[1]] + r[[2]], r[[1]] + q[[2]], "equalityTransitivity"[
				"equalityCongruence"[Function[{Typed[w, Integers]}, "integerEqual"["integerOfPair"[q], w]], "equalitySymmetry"[e]],
				"integerEqualSelf"["integerOfPair"[q]]
			]]
		]
	],
	integerTheorem[
		"cancellationWitness",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[j, NonNegativeIntegers]}, Implies[a == b + j, a + (0 + 0) == (0 + j) + b]],
		{TypeTheoryTactic["Introduce", a, b, j, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	integerTheorem[
		"cancellationContradiction",
		ForAll[
			{Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[j, NonNegativeIntegers]},
			Implies[((d + 1) a + 0 (a + 1 + j)) + (0 + 0) == (0 + k) + ((d + 1) (a + 1 + j) + 0 a), False]
		],
		{TypeTheoryTactic["Introduce", d, k, a, j, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	(* the class of (a, b) with (d + 1) (a, b) the class of (k, 0): a >= b, or else (d + 1) b > (d + 1) a + k *)
	TypeTheoryTheorem[
		"integerNonnegativeCancellation",
		ForAll[{Typed[d, NonNegativeIntegers], Typed[x, Integers]}, Implies[0 <= "integerOfNatural"[d + 1] x, 0 <= x]],
		Function[{Typed[d, NonNegativeIntegers], Typed[x, Integers], Typed[h, 0 <= "integerOfNatural"[d + 1] x]},
			Construct[
				QuotientInduction,
				CartesianProductType[NonNegativeIntegers, NonNegativeIntegers],
				"integerRelation",
				Function[{Typed[w, Integers]}, Implies[0 <= "integerOfNatural"[d + 1] w, 0 <= w]],
				Function[
					{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[g, 0 <= "integerOfNatural"[d + 1] "integerOfPair"[p]]},
					InductiveRecursor[Exists][
						Function[{Typed[o, 0 <= "integerOfNatural"[d + 1] "integerOfPair"[p]]}, 0 <= "integerOfPair"[p]],
						Function[{Typed[k, NonNegativeIntegers], Typed[e, "integerOfNatural"[d + 1] "integerOfPair"[p] == 0 + "integerOfNatural"[k]]},
							With[{related = "integerExact"["pair"[(d + 1) p[[1]] + 0 p[[2]], (d + 1) p[[2]] + 0 p[[1]]], "pair"[0 + k, 0 + 0], e]},
								InductiveRecursor[Or][
									Function[{Typed[t, Or[p[[2]] <= p[[1]], p[[1]] < p[[2]]]]}, 0 <= "integerOfPair"[p]],
									Function[{Typed[le, p[[2]] <= p[[1]]]}, InductiveRecursor[Exists][
										Function[{Typed[o, Exists[{Typed[j, NonNegativeIntegers]}, p[[1]] == p[[2]] + j]]}, 0 <= "integerOfPair"[p]],
										Function[{Typed[j, NonNegativeIntegers], Typed[ej, p[[1]] == p[[2]] + j]},
											"existsIntroduction"[j, "quotientSoundness"["cancellationWitness"[p[[1]], p[[2]], j, ej]]]
										],
										"lessEqualWitness"[p[[2]], p[[1]], le]
									]],
									Function[{Typed[lt, p[[1]] < p[[2]]]}, InductiveRecursor[Exists][
										Function[{Typed[o, Exists[{Typed[j, NonNegativeIntegers]}, p[[2]] == p[[1]] + 1 + j]]}, 0 <= "integerOfPair"[p]],
										Function[{Typed[j, NonNegativeIntegers], Typed[ej, p[[2]] == p[[1]] + 1 + j]},
											"falseElimination"["cancellationContradiction"[d, k, p[[1]], j, Construct[
												"equalitySubstitution",
												NonNegativeIntegers,
												Function[{Typed[c, NonNegativeIntegers]}, ((d + 1) p[[1]] + 0 c) + (0 + 0) == (0 + k) + ((d + 1) c + 0 p[[1]])],
												p[[2]],
												p[[1]] + 1 + j,
												ej,
												related
											]]]
										],
										"lessEqualWitness"[p[[1]] + 1, p[[2]], lt]
									]],
									"lessEqualTotality"[p[[2]], p[[1]]]
								]
							]
						],
						g
					]
				],
				x
			][h]
		]
	],
	integerTheorem[
		"subtractionAddition",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, y == (y - x) + x],
		{TypeTheoryTactic["Introduce", x, y], TypeTheoryTactic["Ring"]}
	],
	integerTheorem[
		"additionNatural",
		ForAll[{Typed[x, Integers], Typed[n, NonNegativeIntegers]}, (0 + "integerOfNatural"[n]) + x == x + "integerOfNatural"[n]],
		{TypeTheoryTactic["Introduce", x, n], TypeTheoryTactic["Ring"]}
	],
	TypeTheoryTheorem[
		"integerLessEqualOfDifference",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[0 <= y - x, x <= y]],
		Function[{Typed[x, Integers], Typed[y, Integers], Typed[h, 0 <= y - x]},
			InductiveRecursor[Exists][
				Function[{Typed[o, 0 <= y - x]}, x <= y],
				Function[{Typed[n, NonNegativeIntegers], Typed[e, y - x == 0 + "integerOfNatural"[n]]}, "existsIntroduction"[n, "equalityTransitivity"[
					"subtractionAddition"[x, y],
					"equalityTransitivity"["equalityCongruence"[Function[{Typed[w, Integers]}, w + x], e], "additionNatural"[x, n]]
				]]],
				h
			]
		]
	],
	TypeTheoryTheorem[
		"integerLessEqualOfMultiple",
		ForAll[
			{Typed[d, NonNegativeIntegers], TypedImplicit[x, Integers], TypedImplicit[y, Integers], Typed[s, Integers]},
			Implies["integerOfNatural"[d + 1] (y - x) == s, Implies[0 <= s, x <= y]]
		],
		Function[
			{
				Typed[d, NonNegativeIntegers],
				TypedImplicit[x, Integers],
				TypedImplicit[y, Integers],
				Typed[s, Integers],
				Typed[e, "integerOfNatural"[d + 1] (y - x) == s],
				Typed[h, 0 <= s]
			},
			"integerLessEqualOfDifference"[x, y, "integerNonnegativeCancellation"[d, y - x, Construct[
				"equalitySubstitution",
				Integers,
				Function[{Typed[w, Integers]}, 0 <= w],
				s,
				"integerOfNatural"[d + 1] (y - x),
				"equalitySymmetry"[e],
				h
			]]]
		]
	],
	(* m <= n from the class of (n, 0) being that of (m + k, 0) *)
	integerTheorem[
		"naturalOfRelation",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[n + (0 + 0) == (m + k) + 0, n == m + k]],
		{TypeTheoryTactic["Introduce", m, n, k, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	TypeTheoryTheorem[
		"integerOfNaturalLessEqual",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies["integerOfNatural"[m] <= "integerOfNatural"[n], m <= n]],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[h, "integerOfNatural"[m] <= "integerOfNatural"[n]]},
			InductiveRecursor[Exists][
				Function[{Typed[o, "integerOfNatural"[m] <= "integerOfNatural"[n]]}, m <= n],
				Function[{Typed[k, NonNegativeIntegers], Typed[e, "integerOfNatural"[n] == "integerOfNatural"[m] + "integerOfNatural"[k]]}, Construct[
					"equalitySubstitution",
					NonNegativeIntegers,
					Function[{Typed[c, NonNegativeIntegers]}, m <= c],
					m + k,
					n,
					"equalitySymmetry"["naturalOfRelation"[m, n, k, "integerExact"["pair"[n, 0], "pair"[m + k, 0 + 0], e]]],
					"lessEqualAddition"[m, k]
				]],
				h
			]
		]
	],
	(* The order decided, as "integerEqual" decides equality: "integerLessEqualQ", the Boolean that x <= y, read on a
	   representing pair of each by lessEqual of natural numbers, respects the relation on both sides, is true exactly
	   where x <= y, and makes the instance "integerLessEqualDecidable", by which "Decide" decides an order of integers;
	   a machine integer's range is such an order (Machine) *)
	TypeTheoryTheorem[
		"lessEqualOfEquivalent",
		ForAll[
			{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
			Implies[Equivalent[a <= b, c <= d], "lessEqual"[a, b] == "lessEqual"[c, d]]
		],
		Function[
			{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[h, Equivalent[a <= b, c <= d]]},
			InductiveRecursor[Booleans][
				Function[{Typed[x, Booleans]}, Implies["lessEqual"[a, b] == x, "lessEqual"[a, b] == "lessEqual"[c, d]]],
				Function[{Typed[e, "lessEqual"[a, b] == "false"]}, InductiveRecursor[Booleans][
					Function[{Typed[y, Booleans]}, Implies["lessEqual"[c, d] == y, "lessEqual"[a, b] == "lessEqual"[c, d]]],
					Function[{Typed[f, "lessEqual"[c, d] == "false"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
					Function[{Typed[f, "lessEqual"[c, d] == "true"]}, "falseElimination"["lessEqualFalse"[a, b, e]["equivalentBackward"[h]["lessEqualTrue"[c, d, f]]]]],
					"lessEqual"[c, d]
				]["equalityReflexivity"["lessEqual"[c, d]]]],
				Function[{Typed[e, "lessEqual"[a, b] == "true"]}, InductiveRecursor[Booleans][
					Function[{Typed[y, Booleans]}, Implies["lessEqual"[c, d] == y, "lessEqual"[a, b] == "lessEqual"[c, d]]],
					Function[{Typed[f, "lessEqual"[c, d] == "false"]}, "falseElimination"["lessEqualFalse"[c, d, f]["equivalentForward"[h]["lessEqualTrue"[a, b, e]]]]],
					Function[{Typed[f, "lessEqual"[c, d] == "true"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
					"lessEqual"[c, d]
				]["equalityReflexivity"["lessEqual"[c, d]]]],
				"lessEqual"[a, b]
			]["equalityReflexivity"["lessEqual"[a, b]]]
		]
	],
	integerTheorem[
		"integerLessEqualRespectsRight",
		ForAll[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[q, s], Equivalent[p[[1]] + q[[2]] <= q[[1]] + p[[2]], p[[1]] + s[[2]] <= s[[1]] + p[[2]]]]
		],
		{"Introduce"[p, q, s, h], "Constructor", "Introduce"[k], "LinearArithmetic", "Introduce"[k], "LinearArithmetic"}
	],
	integerTheorem[
		"integerLessEqualRespectsLeft",
		ForAll[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[p, q], Equivalent[p[[1]] + s[[2]] <= s[[1]] + p[[2]], q[[1]] + s[[2]] <= s[[1]] + q[[2]]]]
		],
		{"Introduce"[p, q, s, h], "Constructor", "Introduce"[k], "LinearArithmetic", "Introduce"[k], "LinearArithmetic"}
	],
	TypeTheoryDefinition[
		"integerLessEqualQOfPair",
		Typed[
			Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "lessEqual"[p[[1]] + q[[2]], q[[1]] + p[[2]]]],
				Function[{Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[q, s]]},
					"lessEqualOfEquivalent"[p[[1]] + q[[2]], q[[1]] + p[[2]], p[[1]] + s[[2]], s[[1]] + p[[2]], "integerLessEqualRespectsRight"[p, q, s, e]]
				],
				y
			]],
			TypeSpecifier[{CartesianProductType[NonNegativeIntegers, NonNegativeIntegers], Integers} -> Booleans]
		]
	],
	TypeTheoryDefinition[
		"integerLessEqualQ",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "integerLessEqualQOfPair"[p, y]],
				Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					Construct[QuotientInduction, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers], "integerRelation",
						Function[{Typed[z, Integers]}, "integerLessEqualQOfPair"[p, z] == "integerLessEqualQOfPair"[q, z]],
						Function[{Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
							"lessEqualOfEquivalent"[p[[1]] + s[[2]], s[[1]] + p[[2]], q[[1]] + s[[2]], s[[1]] + q[[2]], "integerLessEqualRespectsLeft"[p, q, s, e]]
						],
						y
					]
				],
				x
			]],
			TypeSpecifier[{Integers, Integers} -> Booleans]
		]
	],
	TypeTheoryTheorem[
		"lessEqualComplete",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies[m <= n, "lessEqual"[m, n] == "true"]],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[h, m <= n]},
			InductiveRecursor[Booleans][
				Function[{Typed[b, Booleans]}, Implies["lessEqual"[m, n] == b, "lessEqual"[m, n] == "true"]],
				Function[{Typed[e, "lessEqual"[m, n] == "false"]}, "falseElimination"["lessEqualFalse"[m, n, e][h]]],
				Function[{Typed[e, "lessEqual"[m, n] == "true"]}, e],
				"lessEqual"[m, n]
			]["equalityReflexivity"["lessEqual"[m, n]]]
		]
	],
	integerTheorem[
		"orderWitnessRelation",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			Implies[c + b == (a + d) + k, c + b == (a + k) + d]
		],
		{"Introduce"[a, b, c, d, k, h], "LinearArithmetic"}
	],
	integerTheorem[
		"pairOrderSelfAddition",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, a + b <= (a + n) + b],
		{"Introduce"[a, b, n], "LinearArithmetic"}
	],
	integerTheorem[
		"integerLessEqualQTrue",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies["integerLessEqualQ"[x, y] == "true", "integerLessEqual"[x, y]]],
		{
			"Introduce"[x, y], "Induction"[x], "Introduce"[p], "Induction"[y], "Introduce"[q, h],
			"Exact"[InductiveRecursor[Exists][
				Function[{Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, q[[1]] + p[[2]] == (p[[1]] + q[[2]]) + k]]},
					"integerLessEqual"[QuotientIntroduction["integerRelation", p], QuotientIntroduction["integerRelation", q]]
				],
				Function[{Typed[k, NonNegativeIntegers], Typed[e, q[[1]] + p[[2]] == (p[[1]] + q[[2]]) + k]},
					"existsIntroduction"[k, "quotientSoundness"["orderWitnessRelation"[p[[1]], p[[2]], q[[1]], q[[2]], k, e]]]
				],
				"lessEqualWitness"[p[[1]] + q[[2]], q[[1]] + p[[2]], "lessEqualTrue"[p[[1]] + q[[2]], q[[1]] + p[[2]], h]]
			]]
		}
	],
	integerTheorem[
		"integerLessEqualQSelfAddition",
		ForAll[{Typed[x, Integers], Typed[n, NonNegativeIntegers]}, "integerLessEqualQ"[x, "integerAddition"[x, "integerOfNatural"[n]]] == "true"],
		{
			"Introduce"[x, n], "Induction"[x], "Introduce"[p],
			"Exact"["lessEqualComplete"[p[[1]] + p[[2]], (p[[1]] + n) + p[[2]], "pairOrderSelfAddition"[p[[1]], p[[2]], n]]]
		}
	],
	TypeTheoryTheorem[
		"integerLessEqualQFalse",
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies["integerLessEqualQ"[x, y] == "false", Not["integerLessEqual"[x, y]]]],
		Function[{Typed[x, Integers], Typed[y, Integers], Typed[e, "integerLessEqualQ"[x, y] == "false"], Typed[le, "integerLessEqual"[x, y]]},
			InductiveRecursor[Exists][
				Function[{Typed[w, "integerLessEqual"[x, y]]}, False],
				Function[{Typed[n, NonNegativeIntegers], Typed[h, y == "integerAddition"[x, "integerOfNatural"[n]]]},
					"falseNotTrue"["equalityTransitivity"[
						"equalitySymmetry"[e],
						"equalityTransitivity"["equalityCongruence"[Function[{Typed[z, Integers]}, "integerLessEqualQ"[x, z]], h], "integerLessEqualQSelfAddition"[x, n]]
					]]
				],
				le
			]
		]
	],
	TypeTheoryDefinition[
		"integerLessEqualDecidable",
		Function[{Typed[x, Integers], Typed[y, Integers]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["integerLessEqualQ"[x, y] == b, Decidable["integerLessEqual"[x, y]]]],
			Function[{Typed[e, "integerLessEqualQ"[x, y] == "false"]}, "decidableFalse"["integerLessEqualQFalse"[x, y, e]]],
			Function[{Typed[e, "integerLessEqualQ"[x, y] == "true"]}, "decidableTrue"["integerLessEqualQTrue"[x, y, e]]],
			"integerLessEqualQ"[x, y]
		]["equalityReflexivity"["integerLessEqualQ"[x, y]]]],
		"Instance" -> True
	],
	(* the remainder and the quotient of natural numbers, by recursion on the dividend with the divisor s fixed: the
	   remainder counts up to s and back to zero, and the quotient counts each return, so that n == s Quotient[n, s] +
	   Mod[n, s]; with s zero, the remainder is n and the quotient 0. They are the role
	   equations of "Remainder" and "Quotient" themselves, so the registration is checked, and they compute on literals *)
	TypeTheoryDefinition[Mod, Typed[
		Function[{Typed[t, NonNegativeIntegers], Typed[s, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, NonNegativeIntegers],
			0,
			Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]},
				InductiveRecursor[Booleans][Function[{Typed[c, Booleans]}, NonNegativeIntegers], "successor"[r], 0, "equal"["successor"[r], s]]
			],
			t
		]],
		TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
	]],
	TypeTheoryDefinition[Quotient, Typed[
		Function[{Typed[t, NonNegativeIntegers], Typed[s, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, NonNegativeIntegers],
			0,
			Function[{Typed[k, NonNegativeIntegers], Typed[q, NonNegativeIntegers]},
				InductiveRecursor[Booleans][Function[{Typed[c, Booleans]}, NonNegativeIntegers], q, "successor"[q], "equal"["successor"[Mod[k, s]], s]]
			],
			t
		]],
		TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
	]],
	TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Remainder" -> Mod, "Quotient" -> Quotient|>],

	(* The quotient of integers, rounded down, as Quotient of the Wolfram Language, and the remainder, of the divisor's
	   sign, as Mod. An integer's normal pair, (a - b, b - a) of a representing pair (a, b) in the natural numbers'
	   subtraction, which stops at 0, is the same for every pair of the class: a - b == c - d where a + d == c + b, since
	   a - b == (a + d) - (b + d), and so it is lifted once; the quotient is then a function of normal pairs, by the
	   signs: x / n of a positive n is Quotient[p, n] where x is p >= 0 and -(Quotient[q - 1, n] + 1) where x is -q < 0,
	   and x / -n is -x / n. A 0 divisor gives 0, and the remainder x; by any other, they are what Quotient and Mod compute,
	   rounding down. *)
	TypeTheoryTheorem["subtractionCancellation",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Subtract[a + k, b + k] == Subtract[a, b]],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[j, NonNegativeIntegers]}, Subtract[a + j, b + j] == Subtract[a, b]],
			"equalityReflexivity"[Subtract[a, b]],
			Function[{Typed[j, NonNegativeIntegers], Typed[h, Subtract[a + j, b + j] == Subtract[a, b]]}, "equalityTransitivity"["subtractionSuccessor"[a + j, b + j], h]],
			k
		]]
	],
	integerTheorem["subtractionOfRelation",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers]}, Implies[a + d == c + b, Subtract[a, b] == Subtract[c, d]]],
		{"Introduce"[a, b, c, d, h], "Rewrite"["subtractionCancellation"[a, b, d], "RightToLeft"], "Rewrite"[h], "Rewrite"["additionCommutativity"[b, d]], "Exact"["subtractionCancellation"[c, d, b]]}
	],
	integerTheorem["subtractionOfRelationReversed",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers]}, Implies[a + d == c + b, Subtract[b, a] == Subtract[d, c]]],
		{"Introduce"[a, b, c, d, h], "Apply"["subtractionOfRelation"], "LinearArithmetic"}
	],
	integerTheorem["integerNormalPairRespects",
		ForAll[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[p, q], "pair"[Subtract[p[[1]], p[[2]]], Subtract[p[[2]], p[[1]]]] == "pair"[Subtract[q[[1]], q[[2]]], Subtract[q[[2]], q[[1]]]]]
		],
		{"Introduce"[p, q, e], "Rewrite"["subtractionOfRelation"[p[[1]], p[[2]], q[[1]], q[[2]], e]], "Rewrite"["subtractionOfRelationReversed"[p[[1]], p[[2]], q[[1]], q[[2]], e]]}
	],
	TypeTheoryDefinition["integerNormalPair", Typed[
		Function[{Typed[x, Integers]}, QuotientLift[
			Function[{Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]}, "pair"[Subtract[p[[1]], p[[2]]], Subtract[p[[2]], p[[1]]]]],
			"integerNormalPairRespects",
			x
		]],
		Integers -> CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]
	]],
	TypeTheoryDefinition["integerQuotientOfParts", Typed[
		Function[{Typed[p, NonNegativeIntegers], Typed[q, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[j, NonNegativeIntegers]}, Integers],
			"integerOfNatural"[Quotient[p, n]],
			Function[{Typed[j, NonNegativeIntegers], Typed[r, Integers]}, "integerNegation"["integerOfNatural"[Quotient[j, n] + 1]]],
			q
		]],
		NonNegativeIntegers -> NonNegativeIntegers -> NonNegativeIntegers -> Integers
	]],
	TypeTheoryDefinition["integerQuotient", Typed[
		Function[{Typed[x, Integers], Typed[y, Integers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[j, NonNegativeIntegers]}, Integers],
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[j, NonNegativeIntegers]}, Integers],
				"integerOfNatural"[0],
				Function[{Typed[d, NonNegativeIntegers], Typed[r, Integers]}, "integerQuotientOfParts"["integerNormalPair"[x][[2]], "integerNormalPair"[x][[1]], d + 1]],
				"integerNormalPair"[y][[2]]
			],
			Function[{Typed[c, NonNegativeIntegers], Typed[r, Integers]}, "integerQuotientOfParts"["integerNormalPair"[x][[1]], "integerNormalPair"[x][[2]], c + 1]],
			"integerNormalPair"[y][[1]]
		]],
		Integers -> Integers -> Integers
	]],
	TypeTheoryDefinition["integerMod", Typed[
		Function[{Typed[x, Integers], Typed[y, Integers]}, "integerSubtraction"[x, "integerMultiplication"[y, "integerQuotient"[x, y]]]],
		Integers -> Integers -> Integers
	]],
	(* a quotient is at most its dividend, by induction on the dividend, each step adding 0 or 1; and the integers' quotient
	   of natural numbers is theirs, where the normal pair's 0 - p, which stops at 0, is 0 by "subtractionZeroLeft" *)
	TypeTheoryTheorem["quotientLessEqual",
		ForAll[{Typed[p, NonNegativeIntegers], Typed[s, NonNegativeIntegers]}, Quotient[p, s] <= p],
		Function[{Typed[p, NonNegativeIntegers], Typed[s, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[j, NonNegativeIntegers]}, Quotient[j, s] <= j],
			Typed["lessEqualReflexivity", 0 <= 0],
			Function[{Typed[j, NonNegativeIntegers], Typed[h, Quotient[j, s] <= j]}, InductiveRecursor[Booleans][
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[c, Booleans]}, NonNegativeIntegers], Quotient[j, s], "successor"[Quotient[j, s]], b] <= j + 1],
				"lessEqualStep"[h],
				"lessEqualSuccessor"[h],
				"equal"["successor"[Mod[j, s]], s]
			]],
			p
		]]
	],
	TypeTheoryTheorem["integerQuotientOfNatural",
		ForAll[{Typed[p, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, "integerQuotient"["integerOfNatural"[p], "integerOfNatural"[k + 1]] == "integerOfNatural"[Quotient[p, k + 1]]],
		Function[{Typed[p, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"equalityCongruence"[Function[{Typed[q, NonNegativeIntegers]}, "integerQuotientOfParts"[p, q, k + 1]], "subtractionZeroLeft"[p]]
		]
	]
}
