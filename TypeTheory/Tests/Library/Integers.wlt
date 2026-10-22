(* ::Package:: *)

(* Tests for Library/Integers.wl: the integers as a quotient of pairs of natural numbers, their operations
   lifted from pairs, the laws of a commutative ring proved by the tactics, the arithmetic notation read as
   the integers' where the types say so, and "Induction" on a class. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

integers = TypeTheoryEnvironment["Integers"]


VerificationTest[
	{
		MatchQ[TypeTheoryCheck[integers], _Success],
		Information[integers, "Axioms"],
		Function[name, MatchQ[integers[name], TypeTheoryTheorem[__]]] /@ {
			IntegerAdditionCommutativity, IntegerAdditionAssociativity, IntegerAdditionZero, IntegerAdditionNegation,
			IntegerMultiplicationCommutativity, IntegerMultiplicationAssociativity, IntegerMultiplicationOne, IntegerDistributivity,
			IntegerSubtractionNegation, IntegerOfNaturalAddition, IntegerOfNaturalMultiplication, IntegerLessEqualReflexivity,
			IntegerSquareNonnegative, IntegerNonnegativeAddition, IntegerNonnegativeScaling, IntegerNonnegativeCancellation,
			IntegerLessEqualOfDifference, IntegerLessEqualOfMultiple, IntegerOfNaturalLessEqual
		}
	},
	{True, {PropositionalExtensionality, QuotientSoundness, Choice}, ConstantArray[True, 19]},
	TestID -> "The-integers-and-their-laws-check"
]

VerificationTest[
	{
		TypeOf[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[y, Integers]}, x y + x - y], integers]],
		TypeOf[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[n, NonNegativeIntegers]}, n + x], integers]],
		TypeOf[TypeTheoryTerm[Function[{Typed[x, Integers]}, -x <= 3], integers]],
		TypeOf[TypeTheoryTerm[2 + 3, integers]],
		TypeOf[TypeTheoryTerm[Typed[2 + 3, Integers], integers]]
	},
	{
		TypeTheoryTerm[TypeSpecifier[{Integers} -> TypeSpecifier[{Integers} -> Integers]], integers],
		TypeTheoryTerm[TypeSpecifier[{Integers} -> TypeSpecifier[{NonNegativeIntegers} -> Integers]], integers],
		TypeTheoryTerm[TypeSpecifier[{Integers} -> TypeUniverse[0]], integers],
		TypeTheoryTerm[NonNegativeIntegers, integers],
		TypeTheoryTerm[Integers, integers]
	},
	TestID -> "Arithmetic-is-the-integers'-where-the-types-say-so"
]

(* the classes of (2, 5) and (0, 3) are equal by the soundness of quotients, 2 + 3 and 0 + 5 being 5, but
   they are two representatives, not equal by computation *)
VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[QuotientSoundness[EqualityReflexivity[5]], integers], TypeTheoryTerm[Typed[2 - 5, Integers] == -3, integers]], _Success],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[2 - 5, Integers], integers], TypeTheoryTerm[Typed[-3, Integers], integers]]
	},
	{True, False},
	TestID -> "Integer-equations-hold-by-the-soundness-of-quotients"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + y) - y == x], integers, {
		TypeTheoryTactic["Introduce", x, y],
		TypeTheoryTactic["Rewrite", IntegerSubtractionNegation],
		TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity],
		TypeTheoryTactic["Rewrite", IntegerAdditionNegation],
		TypeTheoryTactic["Rewrite", IntegerAdditionZero]
	}]["Goals"],
	{},
	TestID -> "The-laws-rewrite-integer-terms"
]

(* a new law, proved the way the library proves its own *)
VerificationTest[
	With[
		{
			proof = TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x (y z) == y (x z)], integers, {
				TypeTheoryTactic["Introduce", x, y, z],
				TypeTheoryTactic["Induction", x], TypeTheoryTactic["Introduce", p],
				TypeTheoryTactic["Induction", y], TypeTheoryTactic["Introduce", q],
				TypeTheoryTactic["Induction", z], TypeTheoryTactic["Introduce", s],
				TypeTheoryTactic["Apply", QuotientSoundness],
				TypeTheoryTactic["Ring"]
			}]
		},
		{proof["Goals"], MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[integers, {TypeTheoryTheorem[IntegerLeftCommutativity, proof]}]], _Success]}
	],
	{{}, True},
	TestID -> "Induction-on-classes-proves-laws-of-the-integers"
]

VerificationTest[
	{
		Length[TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x == y, y == x]], integers, {
			TypeTheoryTactic["Introduce", x, y, h], TypeTheoryTactic["Induction", x]
		}]["Goals"]],
		First @ TypeTheoryProof[ForAll[{Typed[x, Integers]}, TypeUniverse[0]], integers, {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Induction", x]}]
	},
	{1, "QuotientEliminationIntoData"},
	TestID -> "Induction-on-a-class-proves-propositions-only"
]

(* equations of integers are decidable, by the Boolean comparison of the pairs *)
VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[2 - 5, Integers] == -3], integers]],
		WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[2 - 5, Integers] == 3], integers]],
		TypeTheoryProof[Typed[7 * (-3) + 21, Integers] == 0, integers, {TypeTheoryTactic["Decide"]}]["Goals"],
		MatchQ[integers[IntegerEqualityDecidable], TypeTheoryDefinition[__]]
	},
	{TypeTheoryTerm["true", integers], TypeTheoryTerm["false", integers], {}, True},
	TestID -> "Equations-of-integers-are-decided-by-computation"
]

(* "Ring" over the integers: induction on each class, the soundness of quotients, "Ring" on the pairs *)
VerificationTest[
	{
		TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y) (x + y) == x x - y y], integers, {TypeTheoryTactic["Introduce", x, y], TypeTheoryTactic["Ring"]}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[x, Integers]}, x + (-x) == 0], integers, {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[n, Naturals]}, 2 (x + n) - n == 2 x + n], integers, {TypeTheoryTactic["Introduce", x, n], TypeTheoryTactic["Ring"]}]["Goals"],
		First @ TypeTheoryProof[ForAll[{Typed[x, Integers]}, x - x == 1], integers, {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}]
	},
	{{}, {}, {}, "NotRingEquation"},
	TestID -> "Ring-proves-the-identities-of-commutative-rings-over-the-integers"
]

(* a hypothesis that mentions an integer variable is not generalized into the goal of its classes *)
VerificationTest[
	TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x <= y, (x + y) (x - y) == x x - y y]], integers, {
		TypeTheoryTactic["Introduce", x, y, h],
		TypeTheoryTactic["Ring"]
	}]["Goals"],
	{},
	TestID -> "Ring-over-the-integers-leaves-other-hypotheses-aside"
]

VerificationTest[
	With[
		{
			scaled = TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers], Typed[c, Integers]}, Implies[a == b, a c - 3 == b c - 3]], integers, {
				TypeTheoryTactic["Introduce", a, b, c, h],
				TypeTheoryTactic["PolynomialReduce"]
			}],
			crossed = TypeTheoryProof[
				ForAll[{Typed[a, Integers], Typed[b, Integers], Typed[c, Integers], Typed[d, Integers]}, Implies[a d == c b, Implies[c == -a, a (b + d) == 0]]],
				integers,
				{TypeTheoryTactic["Introduce", a, b, c, d, h, k], TypeTheoryTactic["PolynomialReduce"]}
			]
		},
		{
			scaled["Goals"],
			crossed["Goals"],
			MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[integers, {TypeTheoryTheorem[ScaledEquation, scaled], TypeTheoryTheorem[CrossedEquation, crossed]}]], _Success],
			First @ TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers]}, Implies[a == b, a == b + 1]], integers, {
				TypeTheoryTactic["Introduce", a, b, h],
				TypeTheoryTactic["PolynomialReduce"]
			}]
		}
	],
	{{}, {}, True, "NoCombination"},
	TestID -> "PolynomialReduce-combines-equations-of-integers"
]

(* the order: squares and their sums are at least 0, a positive multiple is at least 0 only where the
   integer is, and an inequality of integers of natural numbers is one of the natural numbers *)
VerificationTest[
	{
		TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 0 <= 3 (x x) + y y], integers, {
			TypeTheoryTactic["Introduce", x, y],
			TypeTheoryTactic["Exact", IntegerNonnegativeAddition[IntegerNonnegativeScaling[3, IntegerSquareNonnegative[x]], IntegerSquareNonnegative[y]]]
		}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[0 <= 2 (y - x), x <= y]], integers, {
			TypeTheoryTactic["Introduce", x, y, h],
			TypeTheoryTactic["Exact", IntegerLessEqualOfDifference[x, y, IntegerNonnegativeCancellation[1, y - x, h]]]
		}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies[Typed[m, Integers] <= n, m <= n]], integers, {
			TypeTheoryTactic["Introduce", m, n, h],
			TypeTheoryTactic["Exact", IntegerOfNaturalLessEqual[m, n, h]]
		}]["Goals"]
	},
	{{}, {}, {}},
	TestID -> "Squares-are-at-least-zero-and-give-inequalities"
]

(* x^n of an integer and a natural number is the integers' power, and shows as x^n *)
VerificationTest[
	{
		TypeOf[TypeTheoryTerm[Function[{Typed[x, Integers]}, x^2 + 3 x^3], integers]],
		TypeOf[TypeTheoryTerm[2^3, integers]],
		WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[(-2)^3, Integers] == -8], integers]],
		MatchQ[TypeTheoryTerm[Function[{Typed[x, Integers]}, x^2 + 3 x^3], integers], TypeTheoryTerm[Function[{Typed[y_, Integers]}, y_^2 + 3 y_^3], _]]
	},
	{
		TypeTheoryTerm[TypeSpecifier[{Integers} -> Integers], integers],
		TypeTheoryTerm[NonNegativeIntegers, integers],
		TypeTheoryTerm["true", integers],
		True
	},
	TestID -> "Powers-of-integers"
]

(* "Ring" normalizes integer polynomials with the integers' laws: literals of opposite signs, cancelling
   monomials, powers, the integers of natural numbers and atoms that are no variables, with no induction
   on classes *)
VerificationTest[
	{
		TypeTheoryProof[ForAll[{Typed[x, Integers]}, 3 x - 5 x + 2 - 7 == -2 x - 5], integers, {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y)^2 == x^2 - 2 x y + y^2], integers, {TypeTheoryTactic["Introduce", x, y], TypeTheoryTactic["Ring"]}]["Goals"],
		TypeTheoryProof[
			ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[x, Integers]}, (a + b)^2 - x == Typed[a^2, Integers] + 2 a b + b^2 - x],
			integers,
			{TypeTheoryTactic["Introduce", a, b, x], TypeTheoryTactic["Ring"]}
		]["Goals"],
		TypeTheoryProof[
			ForAll[{Typed[f, TypeSpecifier[{Integers} -> Integers]], Typed[x, Integers]}, (f[x] + 1)^2 == f[x]^2 + 2 f[x] + 1],
			integers,
			{TypeTheoryTactic["Introduce", f, x], TypeTheoryTactic["Ring"]}
		]["Goals"],
		FreeQ[
			TypeTheoryProof[ForAll[{Typed[x, Integers]}, (x + 1)^5 == x^5 + 5 x^4 + 10 x^3 + 10 x^2 + 5 x + 1], integers, {TypeTheoryTactic["Introduce", x], TypeTheoryTactic["Ring"]}]["Term"],
			QuotientInduction
		]
	},
	{{}, {}, {}, {}, True},
	TestID -> "Ring-normalizes-integer-polynomials-with-the-integers'-laws"
]
