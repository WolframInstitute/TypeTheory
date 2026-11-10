(* ::Package:: *)

(*
The machine reals: the environment of the rationals with the machine integers and the 64-bit reals of the compiler's
typed entries, built and checked the first time it is asked for. TypeTheoryEnvironment["Machine"] stays on the integers;
this environment is the rationals with the declarations of "Machine" and the reals on top, for a function whose typed
code has a real anywhere.

A machine real is a rational that binary64 represents, m 2^e with |m| < 2^53 and -1074 <= e <= 971, a subtype of the
rationals: it has an exact value, x["rational"], and the order and the equality of machine reals are those of their
values. NaN and the infinities are no values: a typed entry leaves before it holds one. The sign of zero is not kept:
-0. is 0, which nothing these operations compute tells apart.

	"Real64"                         Subtype["real64Representable"]; "MachineReal" is the compiler's other name
	"real64Result"[q]                the machine real nearest the rational q, ties to even, "left", and the leave
	                                 Failure["NotFinite", <||>] where that is past the largest, "right": an axiom
	"real64Plus", "real64Subtract"   the result of the exact sum and difference of two values
	"real64Times"                    the result of the exact product, leaving with Failure["Underflow", <||>] where
	                                 the product is not 0 and its result is below 2^-1022, as the compiler's code does
	"real64Reciprocal"               the result of 1/y, with the leaves of a product, and Failure["NotFinite", <||>] by 0:
	                                 x / y is x times it, two roundings, as the Wolfram Language divides machine reals
	"real64OfInteger"                the result of an integer: an integer in an operation with a real is made one first
	"real64Floor", "real64Ceiling", "real64Round", "real64IntegerPart"
	                                 the machine integer of the whole number, Round half to even, leaving with
	                                 Failure["IntegerOverflow", <||>] from 9*10^18 on, where the compiler's code leaves
	"real64Sqrt"                     the square root, leaving with Failure["Domain", <||>] below 0: an axiom above 0
	"real64EqualQ"                   Equal of two values as the Wolfram Language takes machine reals: the same, or apart
	                                 by no more than 2^-46 of the larger

Three constants are axioms with an "Implementation", which the Wolfram Language computes and the kernel never does:
"real64Result", the rounding; "rationalFloor", the whole number below a rational; and "real64SqrtResult". Everything else
is a definition, by a Boolean order of the rationals, "rationalNonNegativeQ", which this library adds: a rational is at
least 0 where the numerator of a pair of it is, which does not depend on the pair. A theorem about real code has the
axioms it uses in its closure. The rounding is to be defined, and its two properties proved, in a later stage; until
then a test of real code tests the reading of the code, its order, its leaves and its control flow, not the arithmetic.

A value that the Wolfram Language computes comes back as a term the kernel checks: "real64RepresentableOfWitness" takes
the m and the two exponents, 2^a above and 2^b below, with five Boolean checks that the kernel computes.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[machineRealsEnvironment]
PackageScoped[real64ResultValue]
PackageScoped[real64SqrtValue]
PackageScoped[real64ValueTerm]


(* ::Section:: *)
(*Usage Messages*)


machineRealsEnvironment::usage = "machineRealsEnvironment[] gives the environment of the rationals with the machine integers and the 64-bit reals of the compiler's typed entries, built and checked the first time it is asked for."
real64ResultValue::usage = "real64ResultValue[q] gives the term of the machine real nearest the rational q, ties to even, or of the leave where that is past the largest: the implementation of \"real64Result\"."
real64SqrtValue::usage = "real64SqrtValue[q] gives the term of the machine real nearest the square root of the rational q, which is at least 0: the implementation of \"real64SqrtResult\"."
real64ValueTerm::usage = "real64ValueTerm[q] gives HoldComplete of the term of the machine real that is the rational q, with the witness that binary64 represents it, or None where it does not."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations of the machine integers on the rationals, then the reals' *)
machineRealsEnvironment[] := machineRealsEnvironment[] = withoutStoreTracking[
	libraryEnvironment["MachineReals", rationalsEnvironment[], withStoreCleanup[Fold[addMachineDeclaration, rationalsEnvironment[], Join[$machineDeclarations, $machineRealDeclarations]]]]
]

(* The implementations. The nearest machine real to a rational, exactly: the exponent e with 2^52 <= |q| / 2^e < 2^53,
   no lower than -1074, where the subnormal reals are, and the whole number nearest q / 2^e, which Round takes to the even
   one of two. A value from 2^1024 on is no machine real. *)
nearestReal64[0] := 0
nearestReal64[q_] := With[{exponent = Max[Floor[Log2[Abs[q]]] - 52, -1074]}, Round[q / 2^exponent] 2^exponent]

real64ResultValue[q_?NumericQ] := With[{nearest = nearestReal64[q]},
	If[ Abs[nearest] < 2^1024,
		real64ValueTerm[nearest],
		HoldComplete[Typed["right"[Failure["NotFinite", <||>]], "Real64" | Failure]]
	]
]

(* no square root of a machine real is half way between two, so 60 digits of it round as the root itself does *)
real64SqrtValue[q_?NumericQ] := real64ResultValue[If[IntegerQ[Sqrt[q]] || Head[Sqrt[q]] === Rational, Sqrt[q], Rationalize[N[Sqrt[q], 60], 0]]]

(* the term of a machine real: its rational with the witness, the odd m and the exponents of 2 above and below *)
real64ValueTerm[0] := HoldComplete[Typed["left"["subtype"[Typed[0, Rationals], "real64RepresentableOfWitness"[Typed[0, Rationals], 0, 0, 0,
	"equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"]]]], "Real64" | Failure]]
real64ValueTerm[q_] := With[{exponent = IntegerExponent[Numerator[q], 2] - IntegerExponent[Denominator[q], 2]},
	With[{m = q / 2^exponent, above = Max[exponent, 0], below = Max[-exponent, 0]},
		If[ IntegerQ[m] && Abs[m] < 2^53 && above <= 971 && below <= 1074,
			HoldComplete[Typed["left"["subtype"[Typed[q, Rationals], "real64RepresentableOfWitness"[Typed[q, Rationals], m, above, below,
				"equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"]]]], "Real64" | Failure]],
			None
		]
	]
]

$machineRealDeclarations = With[
	{
		pairs = CartesianProductType[Integers, NonNegativeIntegers],
		(* the bounds written as literals: |m| < 2^53, the smallest normal real 2^-1022, the bound of a whole number, and
		   the tolerance of Equal, 2^-46 *)
		mantissa = 9007199254740991,
		normal = 1 / 44942328371557897693232629769725618340449424473557664318357520289433168951375240783177119330601884005280028469967848339414697442203604155623211857659868531094441973356216371319075554900311523529863270738021251442209537670585615720368478277635206809290837627671146574559986811484619929076208839082406056034304,
		whole = 9000000000000000000,
		tolerance = 1 / 70368744177664
	},
	{
		(* a Boolean of the integers' order does not depend on which of two equivalent conditions it decides *)
		TypeTheoryTheorem["integerLessEqualQOfEquivalent",
			ForAll[{Typed[a, Integers], Typed[b, Integers], Typed[c, Integers], Typed[d, Integers]}, Implies[Equivalent[a <= b, c <= d], "integerLessEqualQ"[a, b] == "integerLessEqualQ"[c, d]]],
			Function[{Typed[a, Integers], Typed[b, Integers], Typed[c, Integers], Typed[d, Integers], Typed[h, Equivalent[a <= b, c <= d]]},
				InductiveRecursor[Booleans][
					Function[{Typed[x, Booleans]}, Implies["integerLessEqualQ"[a, b] == x, "integerLessEqualQ"[a, b] == "integerLessEqualQ"[c, d]]],
					Function[{Typed[e, "integerLessEqualQ"[a, b] == "false"]}, InductiveRecursor[Booleans][
						Function[{Typed[y, Booleans]}, Implies["integerLessEqualQ"[c, d] == y, "integerLessEqualQ"[a, b] == "integerLessEqualQ"[c, d]]],
						Function[{Typed[f, "integerLessEqualQ"[c, d] == "false"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
						Function[{Typed[f, "integerLessEqualQ"[c, d] == "true"]},
							"falseElimination"["integerLessEqualQFalse"[a, b, e][h[["backward"]]["integerLessEqualQTrue"[c, d, f]]]]
						],
						"integerLessEqualQ"[c, d]
					]["equalityReflexivity"["integerLessEqualQ"[c, d]]]],
					Function[{Typed[e, "integerLessEqualQ"[a, b] == "true"]}, InductiveRecursor[Booleans][
						Function[{Typed[y, Booleans]}, Implies["integerLessEqualQ"[c, d] == y, "integerLessEqualQ"[a, b] == "integerLessEqualQ"[c, d]]],
						Function[{Typed[f, "integerLessEqualQ"[c, d] == "false"]},
							"falseElimination"["integerLessEqualQFalse"[c, d, f][h[["forward"]]["integerLessEqualQTrue"[a, b, e]]]]
						],
						Function[{Typed[f, "integerLessEqualQ"[c, d] == "true"]}, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
						"integerLessEqualQ"[c, d]
					]["equalityReflexivity"["integerLessEqualQ"[c, d]]]],
					"integerLessEqualQ"[a, b]
				]["equalityReflexivity"["integerLessEqualQ"[a, b]]]
			]
		],
		(* of two pairs of one rational, a (d + 1) == c (b + 1), the numerators are at least 0 together: a positive factor
		   keeps the sign and cancels *)
		machineTheorem["nonnegativeOfScaledEquation",
			ForAll[{Typed[a, Integers], Typed[c, Integers], Typed[b, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
				Implies[a "integerOfNatural"[d + 1] == c "integerOfNatural"[b + 1], Implies[0 <= a, 0 <= c]]],
			{"Introduce"[a, c, b, d, h, ha], "Apply"["integerNonnegativeCancellation"[b]],
				"Rewrite"["integerMultiplicationCommutativity"["integerOfNatural"[b + 1], c]], "Rewrite"[h, "RightToLeft"],
				"Rewrite"["integerMultiplicationCommutativity"[a, "integerOfNatural"[d + 1]]], "Exact"["integerNonnegativeScaling"[d + 1, ha]]}
		],
		TypeTheoryTheorem["rationalNonNegativeRespects",
			ForAll[{Typed[p, pairs], Typed[q, pairs]}, Implies["rationalRelation"[p, q], Equivalent[0 <= p[[1]], 0 <= q[[1]]]]],
			Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]},
				"equivalentIntroduction"[
					"nonnegativeOfScaledEquation"[p[[1]], q[[1]], p[[2]], q[[2]], e],
					"nonnegativeOfScaledEquation"[q[[1]], p[[1]], q[[2]], p[[2]], "equalitySymmetry"[e]]
				]
			]
		],
		(* the Boolean order of the rationals: x is at least 0 where the numerator of a pair of it is, x <= y where y - x
		   is at least 0, and x < y where y <= x is false *)
		TypeTheoryDefinition["rationalNonNegativeQ", Typed[
			Function[{Typed[x, Rationals]}, QuotientLift[
				Function[{Typed[p, pairs]}, "integerLessEqualQ"[0, p[[1]]]],
				Function[{Typed[p, pairs], Typed[q, pairs], Typed[e, "rationalRelation"[p, q]]}, "integerLessEqualQOfEquivalent"[0, p[[1]], 0, q[[1]], "rationalNonNegativeRespects"[p, q, e]]],
				x
			]],
			Rationals -> Booleans
		]],
		TypeTheoryDefinition["rationalLessEqualQ", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalNonNegativeQ"[y - x]], Rationals -> Rationals -> Booleans]],
		TypeTheoryDefinition["rationalLessQ", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "not"["rationalLessEqualQ"[y, x]]], Rationals -> Rationals -> Booleans]],
		TypeTheoryDefinition["rationalAbsolute", Typed[Function[{Typed[x, Rationals]}, "machineIf"["rationalNonNegativeQ"[x], x, -x]], Rationals -> Rationals]],

		(* the rationals that binary64 represents: m 2^a / 2^b with |m| < 2^53, a <= 971 and b <= 1074. The variable of
		   the predicate names the element of the subtype: x["rational"] is the value of a machine real x *)
		TypeTheoryDefinition["real64Representable", Typed[
			Typed[rational, Rationals] |-> Exists[{Typed[m, Integers]}, Exists[{Typed[a, NonNegativeIntegers]}, Exists[{Typed[b, NonNegativeIntegers]},
				And[
					rational "rationalOfInteger"["integerOfNatural"[2^b]] == "rationalOfInteger"[m "integerOfNatural"[2^a]],
					And[Typed[-mantissa, Integers] <= m, And[m <= Typed[mantissa, Integers], And[a <= 971, b <= 1074]]]
				]
			]]],
			Rationals -> TypeUniverse[0]
		]],
		TypeTheoryDefinition["Real64", Subtype["real64Representable"]],
		TypeTheoryDefinition["MachineReal", "Real64"],
		(* a rational with its m and exponents is a machine real where five Booleans compute to true *)
		TypeTheoryTheorem["real64RepresentableOfWitness",
			ForAll[{Typed[q, Rationals], Typed[m, Integers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
				Implies["rationalEqual"[q "rationalOfInteger"["integerOfNatural"[2^b]], "rationalOfInteger"[m "integerOfNatural"[2^a]]] == "true",
				Implies["integerLessEqualQ"[Typed[-mantissa, Integers], m] == "true",
				Implies["integerLessEqualQ"[m, Typed[mantissa, Integers]] == "true",
				Implies["lessEqual"[a, 971] == "true",
				Implies["lessEqual"[b, 1074] == "true",
					Exists[{Typed[m1, Integers]}, Exists[{Typed[a1, NonNegativeIntegers]}, Exists[{Typed[b1, NonNegativeIntegers]},
						And[
							q "rationalOfInteger"["integerOfNatural"[2^b1]] == "rationalOfInteger"[m1 "integerOfNatural"[2^a1]],
							And[Typed[-mantissa, Integers] <= m1, And[m1 <= Typed[mantissa, Integers], And[a1 <= 971, b1 <= 1074]]]
						]
					]]]
				]]]]]
			],
			Function[
				{
					Typed[q, Rationals], Typed[m, Integers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers],
					Typed[e1, "rationalEqual"[q "rationalOfInteger"["integerOfNatural"[2^b]], "rationalOfInteger"[m "integerOfNatural"[2^a]]] == "true"],
					Typed[e2, "integerLessEqualQ"[Typed[-mantissa, Integers], m] == "true"],
					Typed[e3, "integerLessEqualQ"[m, Typed[mantissa, Integers]] == "true"],
					Typed[e4, "lessEqual"[a, 971] == "true"],
					Typed[e5, "lessEqual"[b, 1074] == "true"]
				},
				"existsIntroduction"[m, "existsIntroduction"[a, "existsIntroduction"[b,
					"andIntroduction"[
						"rationalEqualTrue"[q "rationalOfInteger"["integerOfNatural"[2^b]], "rationalOfInteger"[m "integerOfNatural"[2^a]], e1],
						"andIntroduction"["integerLessEqualQTrue"[Typed[-mantissa, Integers], m, e2],
							"andIntroduction"["integerLessEqualQTrue"[m, Typed[mantissa, Integers], e3], "andIntroduction"["lessEqualTrue"[a, 971, e4], "lessEqualTrue"[b, 1074, e5]]]]
					]
				]]]
			]
		],

		(* the axioms, each computed by the Wolfram Language: the rounding, the whole number below a rational, and the
		   square root of a rational that is at least 0 *)
		TypeTheoryAxiom["real64Result", Rationals -> ("Real64" | Failure), "Implementation" -> real64ResultValue],
		TypeTheoryAxiom["rationalFloor", Rationals -> Integers, "Implementation" -> Floor],
		TypeTheoryAxiom["real64SqrtResult", Rationals -> ("Real64" | Failure), "Implementation" -> real64SqrtValue],

		(* the operations on the values of machine reals, as the compiler's table of typed operations has them *)
		TypeTheoryDefinition["real64Plus", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Result"[x + y]], Rationals -> Rationals -> ("Real64" | Failure)]],
		TypeTheoryDefinition["real64Subtract", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Result"[x - y]], Rationals -> Rationals -> ("Real64" | Failure)]],
		(* the result of an exact value that is to be a normal real: the leave where the value is not 0 and its result
		   is below 2^-1022, judged on the result, as the compiler's code judges it *)
		TypeTheoryDefinition["real64Normal", Typed[
			Function[{Typed[q, Rationals]}, "confirmBind"["real64Result"[q], Function[{Typed[r, "Real64"]},
				"machineIf"["rationalEqual"[q, 0],
					Typed["left"[r], "Real64" | Failure],
					"machineIf"["rationalLessQ"["rationalAbsolute"[r[["rational"]]], Typed[normal, Rationals]],
						Typed["right"[Failure["Underflow", <||>]], "Real64" | Failure],
						Typed["left"[r], "Real64" | Failure]
					]
				]
			]]],
			Rationals -> ("Real64" | Failure)
		]],
		TypeTheoryDefinition["real64Times", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Normal"[x y]], Rationals -> Rationals -> ("Real64" | Failure)]],
		TypeTheoryDefinition["real64Reciprocal", Typed[
			Function[{Typed[y, Rationals]}, "machineIf"["rationalEqual"[y, 0], Typed["right"[Failure["NotFinite", <||>]], "Real64" | Failure], "real64Normal"["rationalInverse"[y]]]],
			Rationals -> ("Real64" | Failure)
		]],
		TypeTheoryDefinition["real64OfInteger", Typed[Function[{Typed[n, Integers]}, "real64Result"["rationalOfInteger"[n]]], Integers -> ("Real64" | Failure)]],
		TypeTheoryDefinition["real64Abs", Typed[Function[{Typed[x, Rationals]}, "real64Result"["rationalAbsolute"[x]]], Rationals -> ("Real64" | Failure)]],
		TypeTheoryDefinition["real64Minus", Typed[Function[{Typed[x, Rationals]}, "real64Result"[-x]], Rationals -> ("Real64" | Failure)]],
		TypeTheoryDefinition["real64Sqrt", Typed[
			Function[{Typed[x, Rationals]}, "machineIf"["rationalNonNegativeQ"[x], "real64SqrtResult"[x], Typed["right"[Failure["Domain", <||>]], "Real64" | Failure]]],
			Rationals -> ("Real64" | Failure)
		]],
		(* the machine integer of a whole number of a real below 9*10^18 in size, from where the compiler's code leaves *)
		TypeTheoryDefinition["real64Whole", Typed[
			Function[{Typed[x, Rationals], Typed[z, Integers]}, "machineIf"["rationalLessQ"["rationalAbsolute"[x], Typed[whole, Rationals]],
				"machineResult"[z],
				Typed["right"[Failure["IntegerOverflow", <||>]], "Integer64" | Failure]
			]],
			Rationals -> Integers -> ("Integer64" | Failure)
		]],
		TypeTheoryDefinition["real64Floor", Typed[Function[{Typed[x, Rationals]}, "real64Whole"[x, "rationalFloor"[x]]], Rationals -> ("Integer64" | Failure)]],
		TypeTheoryDefinition["real64Ceiling", Typed[Function[{Typed[x, Rationals]}, "real64Whole"[x, -"rationalFloor"[-x]]], Rationals -> ("Integer64" | Failure)]],
		TypeTheoryDefinition["real64IntegerPart", Typed[
			Function[{Typed[x, Rationals]}, "real64Whole"[x, "machineIf"["rationalNonNegativeQ"[x], "rationalFloor"[x], -"rationalFloor"[-x]]]],
			Rationals -> ("Integer64" | Failure)
		]],
		(* half to even: the whole number below x + 1/2, and the one before it where x + 1/2 is that number and it is odd *)
		TypeTheoryDefinition["rationalRound", Typed[
			Function[{Typed[x, Rationals]}, Function[{Typed[f, Integers]},
				"machineIf"["rationalEqual"["rationalOfInteger"[f], x + Typed[1/2, Rationals]],
					"machineIf"["integerEqual"[Mod[f, 2], 0], f, f - 1],
					f
				]
			]["rationalFloor"[x + Typed[1/2, Rationals]]]],
			Rationals -> Integers
		]],
		TypeTheoryDefinition["real64Round", Typed[Function[{Typed[x, Rationals]}, "real64Whole"[x, "rationalRound"[x]]], Rationals -> ("Integer64" | Failure)]],
		(* Equal of two machine reals: within 2^-46 of the larger in size *)
		TypeTheoryDefinition["real64EqualQ", Typed[
			Function[{Typed[x, Rationals], Typed[y, Rationals]}, "rationalLessEqualQ"[
				"rationalAbsolute"[x - y],
				Typed[tolerance, Rationals] "machineIf"["rationalLessEqualQ"["rationalAbsolute"[x], "rationalAbsolute"[y]], "rationalAbsolute"[y], "rationalAbsolute"[x]]
			]],
			Rationals -> Rationals -> Booleans
		]]
	}
]
