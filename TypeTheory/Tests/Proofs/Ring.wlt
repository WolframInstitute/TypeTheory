(* ::Package:: *)

(* Tests for Proofs/Ring.wl: the tactic "Ring" proves equations of natural numbers that hold in every
   commutative semiring, with proofs from the prelude's laws that the kernel checks again when they are
   declared, and refuses the equations that do not. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

(* the variables introduced, then "Ring" *)
SetAttributes[ringProof, HoldFirst]
ringProof[statement_, variables_List] := With[{introduce = TypeTheoryTactic @@ Prepend[variables, "Introduce"]},
	TypeTheoryProof[statement, prelude, {introduce, TypeTheoryTactic["Ring"]}]
]


VerificationTest[
	With[
		{
			square = ringProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, (a + b)^2 == a^2 + 2 a b + b^2], {a, b}],
			cube = ringProof[ForAll[{Typed[x, NonNegativeIntegers]}, (x + 1)^3 == x^3 + 3 x^2 + 3 x + 1], {x}],
			brahmagupta = ringProof[
				ForAll[
					{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
					(a^2 + b^2) (c^2 + d^2) + 2 a b c d == (a c + b d)^2 + (a d)^2 + (b c)^2
				],
				{a, b, c, d}
			]
		},
		{
			square["Goals"],
			cube["Goals"],
			brahmagupta["Goals"],
			MatchQ[
				TypeTheoryCheck[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[Square, square], TypeTheoryTheorem[Cube, cube], TypeTheoryTheorem[Brahmagupta, brahmagupta]}]],
				_Success
			]
		}
	],
	{{}, {}, {}, True},
	TestID -> "Ring-proves-polynomial-identities-that-the-kernel-checks"
]

VerificationTest[
	{
		ringProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, a b + b == b (a + 1)], {a, b}]["Goals"],
		ringProof[ForAll[{Typed[n, NonNegativeIntegers]}, "successor"[n] * 2 == 2 n + 2], {n}]["Goals"],
		TypeTheoryProof[2^10 + 3 * 4 == 1036, prelude, {TypeTheoryTactic["Ring"]}]["Goals"],
		ringProof[ForAll[{Typed[a, NonNegativeIntegers]}, a^0 + 0 a + a 1 == a + 1], {a}]["Goals"]
	},
	{{}, {}, {}, {}},
	TestID -> "Ring-handles-successors-literals-and-the-units"
]

VerificationTest[
	ringProof[
		ForAll[{Typed[l, {NonNegativeIntegers}], Typed[m, {NonNegativeIntegers}]}, (Length[l] + Length[m])^2 == Length[m]^2 + 2 Length[l] Length[m] + Length[l]^2],
		{l, m}
	]["Goals"],
	{},
	TestID -> "Ring-treats-other-terms-as-atoms"
]

VerificationTest[
	First /@ {
		ringProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, (a + b)^2 == a^2 + b^2], {a, b}],
		ringProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, (a - b) + b == a], {a, b}],
		TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers]}, a <= a + 1], prelude, {TypeTheoryTactic["Introduce", a], TypeTheoryTactic["Ring"]}]
	},
	{"NotRingEquation", "NotRingEquation", "EquationExpected"},
	TestID -> "Ring-refuses-what-does-not-hold-in-every-commutative-semiring"
]

VerificationTest[
	With[
		{
			product = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[z, NonNegativeIntegers]}, Implies[y == z, x y + 3 == x z + 3]], prelude, {
				TypeTheoryTactic["Introduce", x, y, z, h],
				TypeTheoryTactic["PolynomialReduce"]
			}],
			system = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x + y == 10, Implies[x == 2 y + 1, x y == 21]]], prelude, {
				TypeTheoryTactic["Introduce", x, y, h, k],
				TypeTheoryTactic["PolynomialReduce"]
			}]
		},
		{
			product["Goals"],
			system["Goals"],
			MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[ProductOfEquals, product], TypeTheoryTheorem[SolvedSystem, system]}]], _Success]
		}
	],
	{{}, {}, True},
	TestID -> "PolynomialReduce-combines-the-hypotheses-into-the-goal"
]

VerificationTest[
	First @ TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x == y, x == y + 1]], prelude, {
		TypeTheoryTactic["Introduce", x, y, h],
		TypeTheoryTactic["PolynomialReduce"]
	}],
	"NoCombination",
	TestID -> "PolynomialReduce-fails-where-no-combination-gives-the-goal"
]

VerificationTest[
	With[
		{
			bound = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[2 x + 3 y <= 12, Implies[4 <= x, y <= 1]]], prelude, {
				TypeTheoryTactic["Introduce", x, y, h, k],
				TypeTheoryTactic["LinearArithmetic"]
			}],
			equation = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x <= y, Implies[y <= x, x == y]]], prelude, {
				TypeTheoryTactic["Introduce", x, y, h, k],
				TypeTheoryTactic["LinearArithmetic"]
			}],
			contradiction = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x < y, Implies[y < x + 1, False]]], prelude, {
				TypeTheoryTactic["Introduce", x, y, h, k],
				TypeTheoryTactic["LinearArithmetic"]
			}],
			nonnegative = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[z, NonNegativeIntegers]}, Implies[x + 2 y <= z, x <= z]], prelude, {
				TypeTheoryTactic["Introduce", x, y, z, h],
				TypeTheoryTactic["LinearArithmetic"]
			}]
		},
		{
			bound["Goals"],
			equation["Goals"],
			contradiction["Goals"],
			nonnegative["Goals"],
			MatchQ[
				TypeTheoryCheck[TypeTheoryEnvironment[prelude, {
					TypeTheoryTheorem[Bound, bound],
					TypeTheoryTheorem[EquationFromBounds, equation],
					TypeTheoryTheorem[NoNumberBetween, contradiction],
					TypeTheoryTheorem[DroppedTerm, nonnegative]
				}]],
				_Success
			]
		}
	],
	{{}, {}, {}, {}, True},
	TestID -> "LinearArithmetic-combines-inequalities-with-multipliers-the-kernel-checks"
]

VerificationTest[
	First /@ {
		TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x <= y, y <= x]], prelude, {
			TypeTheoryTactic["Introduce", x, y, h],
			TypeTheoryTactic["LinearArithmetic"]
		}],
		TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers]}, x <= x x + 1], prelude, {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["LinearArithmetic"]}]
	},
	{"NoLinearCombination", "NoLinearCombination"},
	TestID -> "LinearArithmetic-fails-where-the-goal-does-not-follow-linearly"
]

(* In the rationals "Ring" builds the normal forms of rationals from the rationals' own laws: an identity in four
   variables, which by the classes of pairs is one of twelve natural numbers, is proved at once; a term that is no sum
   or product is an atom, as an inverse is; numbers of opposite signs add; the rational of an integer's sum is the sum
   of the rationals. The kernel checks each proof when it is declared. An equation that holds by the arithmetic of
   fractions is left to the classes of pairs, and one that does not hold is refused. *)
VerificationTest[
	Module[{rationals = TypeTheoryEnvironment["Rationals"], prove, proofs},
		prove[statement_, variables_Integer : 4] := TypeTheoryProof[statement, rationals, Append[ConstantArray[TypeTheoryTactic["Introduce"], variables], TypeTheoryTactic["Ring"]]];
		proofs = {
			prove[TypeTheoryTerm[ForAll[{Typed[a, Rationals], Typed[b, Rationals], Typed[c, Rationals], Typed[d, Rationals]}, (a + b) (c + d) == a c + a d + b c + b d], rationals]],
			prove[TypeTheoryTerm[ForAll[{Typed[a, Rationals], Typed[b, Rationals], Typed[c, Rationals], Typed[d, Rationals]}, (a - b)^3 + c - c == a^3 - 3 a^2 b + 3 a b^2 - b^3 + 0 d], rationals]],
			prove[TypeTheoryTerm[ForAll[{Typed[a, Rationals], Typed[b, Rationals], Typed[c, Rationals], Typed[d, Rationals]}, "rationalInverse"[a] + b + 2 c - 5 c == b - 3 c + "rationalInverse"[a] + 0 d], rationals]],
			prove[TypeTheoryTerm[ForAll[{Typed[m, Integers], Typed[n, Integers], Typed[c, Rationals], Typed[d, Rationals]}, "rationalOfInteger"[m n - m] + c == "rationalOfInteger"[m] ("rationalOfInteger"[n] - 1) + c + 0 d], rationals]],
			prove[TypeTheoryTerm[ForAll[{Typed[a, Rationals]}, Typed[1/2, Rationals] a + Typed[1/2, Rationals] a == a], rationals], 1],
			prove[TypeTheoryTerm[ForAll[{Typed[a, Rationals], Typed[b, Rationals], Typed[c, Rationals], Typed[d, Rationals]}, 2 a + b + c + d == 3 a + b + c + d], rationals]]
		};
		{
			Map[Function[proof, If[FailureQ[proof], proof["Tag"], proof["Goals"]]], proofs],
			MatchQ[
				TypeTheoryCheck[TypeTheoryEnvironment[rationals, MapIndexed[Function[{proof, index}, TypeTheoryTheorem @@ {"ringOfRationals" <> ToString[First[index]], proof}], Take[proofs, 5]]]],
				_Success
			]
		}
	],
	{{{}, {}, {}, {}, {}, "NotRingEquation"}, True},
	TimeConstraint -> 300,
	TestID -> "Ring-proves-equations-of-rationals-from-the-rationals-laws"
]

(* An equation of rationals written with the operations of the rings and variables alone, which the normal forms do not
   prove, is refused at once: the classes of pairs of its four variables, twelve natural numbers, took 2.4 GB to refuse
   it. One with a constant whose definition is a fraction is still left to the classes, which prove it. *)
VerificationTest[
	Module[{rationals = TypeTheoryEnvironment["Rationals"], extended},
		extended = TypeTheoryEnvironment[rationals, {TypeTheoryDefinition["half", Typed[1/2, Rationals]]}];
		{
			MemoryConstrained[
				TypeTheoryProof[
					TypeTheoryTerm[ForAll[{Typed[a, Rationals], Typed[b, Rationals], Typed[c, Rationals], Typed[d, Rationals]}, 2 a + b + c + d == 3 a + b + c + d], rationals],
					rationals,
					Append[ConstantArray[TypeTheoryTactic["Introduce"], 4], TypeTheoryTactic["Ring"]]
				]["Tag"],
				200000000,
				"more than 200 MB"
			],
			TypeTheoryProof[TypeTheoryTerm[ForAll[{Typed[a, Rationals]}, "half" a + "half" a == a], extended], extended, {TypeTheoryTactic["Introduce"], TypeTheoryTactic["Ring"]}]["Goals"],
			TypeTheoryProof[
				TypeTheoryTerm[ForAll[{Typed[a, Rationals]}, Typed[1/2, Rationals] a + Typed[1/3, Rationals] a == a], rationals],
				rationals,
				{TypeTheoryTactic["Introduce"], TypeTheoryTactic["Ring"]}
			]["Tag"]
		}
	],
	{"NotRingEquation", {}, "NotRingEquation"},
	TestID -> "Ring-refuses-an-equation-of-rationals-without-a-fraction-at-once"
]

