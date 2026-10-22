(* ::Package:: *)

(* Tests for Proofs/SumsOfSquares.wl and the tactic "SumOfSquares": certificates d f == c1 g1^2 + ...
   that Wolfram finds for polynomials with integer coefficients, none for those that are not sums of
   squares, and inequalities of integers and of natural numbers proved with them, which the kernel checks
   again when they are declared. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

integers = TypeTheoryEnvironment["Integers"]

certificate = WolframInstitute`TypeTheory`PackageScope`sumOfSquaresCertificate

(* a certificate is d and pairs {c, g}, with d f the sum of the c g^2, d and each c positive integers *)
certificateQ[f_, {scale_Integer?Positive, squares_List}] := And[
	AllTrue[squares, Function[square, MatchQ[square, {_Integer?Positive, _}]]],
	Expand[scale f - Total[Function[square, First[square] Last[square]^2] /@ squares]] === 0
]
certificateQ[_, _] := False

(* the variables introduced, then "SumOfSquares" *)
SetAttributes[sumOfSquaresProof, HoldFirst]
sumOfSquaresProof[statement_, variables_List] := With[{introduce = TypeTheoryTactic @@ Prepend[variables, "Introduce"]},
	TypeTheoryProof[statement, integers, {introduce, TypeTheoryTactic["SumOfSquares"]}]
]


(* the Gram matrix is unique for the first three and free for the quartics, which SemidefiniteOptimization
   settles; x^2 - 1 is negative at 0, the cubic is negative somewhere, and Motzkin's polynomial is at
   least 0 but no sum of squares *)
VerificationTest[
	{
		Function[f, certificateQ[f, certificate[f, Variables[f]]]] /@ {
			x^2 - 2 x y + y^2,
			x^2 + y^2 + z^2 - x y - y z - z x,
			(a^2 + b^2) (c^2 + d^2) - (a c + b d)^2,
			x^4 - 4 x + 3,
			w^4 + x^4 + y^4 + z^4 - 4 w x y z
		},
		certificate[5, {}],
		certificate[0, {x}],
		Function[f, certificate[f, Variables[f]]] /@ {x^2 - 1, x^3 + y^3 + z^3 - 3 x y z, x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1}
	},
	{{True, True, True, True, True}, {1, {{5, 1}}}, {1, {}}, {None, None, None}},
	TestID -> "Certificates-are-found-for-sums-of-squares-only"
]

VerificationTest[
	{
		sumOfSquaresProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 2 x y <= x x + y y], {x, y}]["Goals"],
		sumOfSquaresProof[ForAll[{Typed[x, Integers]}, 0 <= x x - 2 x + 1], {x}]["Goals"],
		sumOfSquaresProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, x y + y z + z x <= x x + y y + z z], {x, y, z}]["Goals"],
		sumOfSquaresProof[ForAll[{Typed[x, Integers]}, 4 x <= x^4 + 3], {x}]["Goals"],
		sumOfSquaresProof[ForAll[{Typed[a, Integers], Typed[b, Integers], Typed[c, Integers], Typed[d, Integers]}, (a c + b d)^2 <= (a^2 + b^2) (c^2 + d^2)], {a, b, c, d}]["Goals"]
	},
	{{}, {}, {}, {}, {}},
	TestID -> "SumOfSquares-proves-inequalities-of-integers"
]

(* x >= y and x < y unfold to inequalities x <= y; one of natural numbers is that of their integers;
   a hypothesis is no obstacle *)
VerificationTest[
	{
		sumOfSquaresProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x x + y y >= 2 x y], {x, y}]["Goals"],
		sumOfSquaresProof[ForAll[{Typed[x, Integers]}, 0 < x x + 1], {x}]["Goals"],
		sumOfSquaresProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, 2 a b <= a^2 + b^2], {a, b}]["Goals"],
		sumOfSquaresProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x <= y, 2 x y <= x x + y y]], {x, y, h}]["Goals"]
	},
	{{}, {}, {}, {}},
	TestID -> "SumOfSquares-unfolds-the-comparisons-and-takes-natural-numbers"
]

VerificationTest[
	MatchQ[
		TypeTheoryEnvironment[integers, {
			TypeTheoryTheorem["twiceProductAtMostSquares", sumOfSquaresProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 2 x y <= x x + y y], {x, y}]]
		}],
		_TypeTheoryEnvironment
	],
	True,
	TestID -> "A-proof-by-SumOfSquares-is-declared"
]

VerificationTest[
	{
		First @ sumOfSquaresProof[ForAll[{Typed[x, Integers]}, x x <= 2], {x}],
		First @ sumOfSquaresProof[ForAll[{Typed[x, Integers]}, x x == x x], {x}],
		First @ TypeTheoryProof[
			ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, 2 a b <= a^2 + b^2],
			TypeTheoryEnvironment["Prelude"],
			{TypeTheoryTactic["Introduce", a, b], TypeTheoryTactic["SumOfSquares"]}
		]
	},
	{"NoSumOfSquares", "InequalityExpected", "SumOfSquaresUnavailable"},
	TestID -> "SumOfSquares-fails-where-it-cannot-prove"
]
