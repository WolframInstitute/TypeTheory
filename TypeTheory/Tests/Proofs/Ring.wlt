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
		ringProof[ForAll[{Typed[n, NonNegativeIntegers]}, NaturalNumberSuccessor[n] * 2 == 2 n + 2], {n}]["Goals"],
		TypeTheoryProof[2^10 + 3 * 4 == 1036, prelude, {TypeTheoryTactic["Ring"]}]["Goals"],
		ringProof[ForAll[{Typed[a, NonNegativeIntegers]}, a^0 + 0 a + a 1 == a + 1], {a}]["Goals"]
	},
	{{}, {}, {}, {}},
	TestID -> "Ring-handles-successors-literals-and-the-units"
]

VerificationTest[
	ringProof[
		ForAll[{Typed[l, Lists[NonNegativeIntegers]], Typed[m, Lists[NonNegativeIntegers]]}, (Length[l] + Length[m])^2 == Length[m]^2 + 2 Length[l] Length[m] + Length[l]^2],
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
