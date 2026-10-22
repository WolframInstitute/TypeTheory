(* ::Package:: *)

(*
The integers: TypeTheoryEnvironment["Integers"] is the prelude with them, built and checked the first time
it is asked for. An integer is a class of pairs (a, b) of natural numbers, standing for a - b, by the
relation that relates (a, b) and (c, d) when a + d == c + b: a quotient type, the way many textbooks build
the integers, where Lean's Int is an inductive type.

	Integers                      QuotientType["integerRelation"], shown as ℤ
	"integerOfNatural"[n]         the class of (n, 0), a coercion: a natural number where an integer is expected
	-x, x + y, x - y, x * y       "integerNegation", "integerAddition", "integerSubtraction" and "integerMultiplication"
	x <= y, x < y, x >= y, x > y  "integerLessEqual" and the others: y is x plus a natural number, at least 1 for <

An operation lifts a function on pairs with QuotientLift, given a proof that the function respects the
relation; a binary one lifts in one argument, then in the other. The proofs that the functions respect
the relation and the laws of a commutative ring are proved by the library's own tactics: "Induction" on a
class gives the class of a pair, QuotientSoundness reduces an equation of classes to the relation of the
pairs, and "LinearArithmetic", "PolynomialReduce" and "Ring" prove that equation of natural numbers. The
kernel checks every proof as it checks any other.

Elaboration reads +, *, -, the comparisons, -x and negative literals as the integers' where the arguments
or the expected type are integers, and as the natural numbers' otherwise.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[IntegerAdditionCommutativity]
PackageExported[IntegerAdditionAssociativity]
PackageExported[IntegerAdditionZero]
PackageExported[IntegerAdditionNegation]
PackageExported[IntegerMultiplicationCommutativity]
PackageExported[IntegerMultiplicationAssociativity]
PackageExported[IntegerMultiplicationOne]
PackageExported[IntegerDistributivity]
PackageExported[IntegerSubtractionNegation]
PackageExported[IntegerOfNaturalAddition]
PackageExported[IntegerOfNaturalMultiplication]
PackageExported[IntegerLessEqualReflexivity]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[integersEnvironment]


(* ::Section:: *)
(*Usage Messages*)


IntegerAdditionCommutativity::usage = "IntegerAdditionCommutativity[x, y] proves x + y == y + x for integers x and y. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerAdditionAssociativity::usage = "IntegerAdditionAssociativity[x, y, z] proves (x + y) + z == x + (y + z) for integers. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerAdditionZero::usage = "IntegerAdditionZero[x] proves x + 0 == x for an integer x. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerAdditionNegation::usage = "IntegerAdditionNegation[x] proves x + -x == 0 for an integer x. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerMultiplicationCommutativity::usage = "IntegerMultiplicationCommutativity[x, y] proves x y == y x for integers x and y. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerMultiplicationAssociativity::usage = "IntegerMultiplicationAssociativity[x, y, z] proves (x y) z == x (y z) for integers. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerMultiplicationOne::usage = "IntegerMultiplicationOne[x] proves x * 1 == x for an integer x. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerDistributivity::usage = "IntegerDistributivity[x, y, z] proves x (y + z) == x y + x z for integers. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerSubtractionNegation::usage = "IntegerSubtractionNegation[x, y] proves x - y == x + -y for integers, which holds by computation. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerOfNaturalAddition::usage = "IntegerOfNaturalAddition[m, n] proves that the integer of m + n is the sum of the integers of the natural numbers m and n. \
It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerOfNaturalMultiplication::usage = "IntegerOfNaturalMultiplication[m, n] proves that the integer of m n is the product of the integers of the natural numbers m and n. \
It is a theorem of TypeTheoryEnvironment[\"Integers\"]."
IntegerLessEqualReflexivity::usage = "IntegerLessEqualReflexivity[x] proves x <= x for an integer x. It is a theorem of TypeTheoryEnvironment[\"Integers\"]."

integersEnvironment::usage = "integersEnvironment[] gives the prelude with the integers, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations in order, each theorem proved by its tactics in the environment so far *)
integersEnvironment[] := integersEnvironment[] = withoutStoreTracking[withStoreCleanup[Fold[addIntegerDeclaration, preludeEnvironment[], $integerDeclarations]]]

SetAttributes[integerTheorem, HoldAll]

addIntegerDeclaration[failure_Failure, _] := failure
addIntegerDeclaration[environment_, integerTheorem[name_, statement_, tactics_List]] :=
	TypeTheoryEnvironment[environment, {TypeTheoryTheorem[name, TypeTheoryProof[statement, environment, tactics]]}]
addIntegerDeclaration[environment_, declaration_] := TypeTheoryEnvironment[environment, {declaration}]

$integerDeclarations = {
	(* pairs (a, b) and (c, d) are related when a + d == c + b *)
	TypeTheoryDefinition[
		"integerRelation",
		Function[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]},
			p[[1]] + q[[2]] == q[[1]] + p[[2]]
		]
	],
	TypeTheoryDefinition[Integers, Typed[QuotientType["integerRelation"], TypeUniverse[1]]],
	TypeTheoryDefinition[
		"integerOfPair",
		Typed[
			Function[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, QuotientIntroduction["integerRelation", p]],
			TypeSpecifier[{CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerOfNatural",
		Typed[Function[{Typed[n, NonNegativeIntegers]}, "integerOfPair"[Pair[n, 0]]], TypeSpecifier[{NonNegativeIntegers} -> Integers]],
		"Coercion" -> True
	],

	(* swapping a pair, adding two and multiplying two respect the relation *)
	integerTheorem[
		"integerNegationRespects",
		ForAll[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[p, q], "integerRelation"[Pair[p[[2]], p[[1]]], Pair[q[[2]], q[[1]]]]]
		],
		{TypeTheoryTactic["Introduce", p, q, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	integerTheorem[
		"integerAdditionRespectsLeft",
		ForAll[
			{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[p, q], "integerRelation"[Pair[p[[1]] + s[[1]], p[[2]] + s[[2]]], Pair[q[[1]] + s[[1]], q[[2]] + s[[2]]]]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	integerTheorem[
		"integerAdditionRespectsRight",
		ForAll[
			{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies["integerRelation"[q, s], "integerRelation"[Pair[p[[1]] + q[[1]], p[[2]] + q[[2]]], Pair[p[[1]] + s[[1]], p[[2]] + s[[2]]]]]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["LinearArithmetic"]}
	],
	integerTheorem[
		"integerMultiplicationRespectsLeft",
		ForAll[
			{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies[
				"integerRelation"[p, q],
				"integerRelation"[
					Pair[p[[1]] s[[1]] + p[[2]] s[[2]], p[[1]] s[[2]] + p[[2]] s[[1]]],
					Pair[q[[1]] s[[1]] + q[[2]] s[[2]], q[[1]] s[[2]] + q[[2]] s[[1]]]
				]
			]
		],
		{TypeTheoryTactic["Introduce", p, q, s, h], TypeTheoryTactic["PolynomialReduce"]}
	],
	integerTheorem[
		"integerMultiplicationRespectsRight",
		ForAll[
			{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]},
			Implies[
				"integerRelation"[q, s],
				"integerRelation"[
					Pair[p[[1]] q[[1]] + p[[2]] q[[2]], p[[1]] q[[2]] + p[[2]] q[[1]]],
					Pair[p[[1]] s[[1]] + p[[2]] s[[2]], p[[1]] s[[2]] + p[[2]] s[[1]]]
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
				Function[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, "integerOfPair"[Pair[p[[2]], p[[1]]]]],
				Function[
					{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					QuotientSoundness["integerNegationRespects"[p, q, e]]
				],
				x
			]],
			TypeSpecifier[{Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerAdditionOfPair",
		Typed[
			Function[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, "integerOfPair"[Pair[p[[1]] + q[[1]], p[[2]] + q[[2]]]]],
				Function[
					{Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[q, s]]},
					QuotientSoundness["integerAdditionRespectsRight"[p, q, s, e]]
				],
				y
			]],
			TypeSpecifier[{CartesianProduct[NonNegativeIntegers, NonNegativeIntegers], Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerAddition",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, "integerAdditionOfPair"[p, y]],
				Function[
					{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					Construct[
						QuotientInduction,
						CartesianProduct[NonNegativeIntegers, NonNegativeIntegers],
						"integerRelation",
						Function[{Typed[z, Integers]}, "integerAdditionOfPair"[p, z] == "integerAdditionOfPair"[q, z]],
						Function[{Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, QuotientSoundness["integerAdditionRespectsLeft"[p, q, s, e]]],
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
			Function[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, "integerOfPair"[Pair[p[[1]] q[[1]] + p[[2]] q[[2]], p[[1]] q[[2]] + p[[2]] q[[1]]]]],
				Function[
					{Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[q, s]]},
					QuotientSoundness["integerMultiplicationRespectsRight"[p, q, s, e]]
				],
				y
			]],
			TypeSpecifier[{CartesianProduct[NonNegativeIntegers, NonNegativeIntegers], Integers} -> Integers]
		]
	],
	TypeTheoryDefinition[
		"integerMultiplication",
		Typed[
			Function[{Typed[x, Integers], Typed[y, Integers]}, QuotientLift[
				Function[{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, "integerMultiplicationOfPair"[p, y]],
				Function[
					{Typed[p, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[q, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]], Typed[e, "integerRelation"[p, q]]},
					Construct[
						QuotientInduction,
						CartesianProduct[NonNegativeIntegers, NonNegativeIntegers],
						"integerRelation",
						Function[{Typed[z, Integers]}, "integerMultiplicationOfPair"[p, z] == "integerMultiplicationOfPair"[q, z]],
						Function[{Typed[s, CartesianProduct[NonNegativeIntegers, NonNegativeIntegers]]}, QuotientSoundness["integerMultiplicationRespectsLeft"[p, q, s, e]]],
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
		IntegerAdditionCommutativity,
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, x + y == y + x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		IntegerAdditionAssociativity,
		ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x + y) + z == x + (y + z)],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		IntegerAdditionZero,
		ForAll[{Typed[x, Integers]}, x + 0 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	(* x + -x is read as x - x, so the negation is written out *)
	integerTheorem[
		IntegerAdditionNegation,
		ForAll[{Typed[x, Integers]}, x + "integerNegation"[x] == 0],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		IntegerMultiplicationCommutativity,
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x],
		{
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		IntegerMultiplicationAssociativity,
		ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x y) z == x (y z)],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		IntegerMultiplicationOne,
		ForAll[{Typed[x, Integers]}, x * 1 == x],
		{
			TypeTheoryTactic["Introduce", x],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],
	integerTheorem[
		IntegerDistributivity,
		ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x (y + z) == x y + x z],
		{
			TypeTheoryTactic["Introduce", x, y, z],
			TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
			TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
			TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
			TypeTheoryTactic["Apply", QuotientSoundness],
			TypeTheoryTactic["Ring"]
		}
	],

	(* a difference is a sum with the negation, by computation *)
	integerTheorem[
		IntegerSubtractionNegation,
		ForAll[{Typed[x, Integers], Typed[y, Integers]}, x - y == x + "integerNegation"[y]],
		{TypeTheoryTactic["Introduce", x, y], TypeTheoryTactic["Reflexivity"]}
	],

	(* the natural numbers keep their sums and products among the integers; the coercion is written out,
	   since Typed[m + n, Integers] would add the integers of m and n *)
	integerTheorem[
		IntegerOfNaturalAddition,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "integerOfNatural"[m + n] == "integerOfNatural"[m] + "integerOfNatural"[n]],
		{TypeTheoryTactic["Introduce", m, n], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],
	integerTheorem[
		IntegerOfNaturalMultiplication,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "integerOfNatural"[m n] == "integerOfNatural"[m] "integerOfNatural"[n]],
		{TypeTheoryTactic["Introduce", m, n], TypeTheoryTactic["Apply", QuotientSoundness], TypeTheoryTactic["Ring"]}
	],

	(* x is x plus 0 *)
	integerTheorem[
		IntegerLessEqualReflexivity,
		ForAll[{Typed[x, Integers]}, x <= x],
		{TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Exact", ExistsIntroduction[0, EqualitySymmetry[IntegerAdditionZero[x]]]]}
	]
}
