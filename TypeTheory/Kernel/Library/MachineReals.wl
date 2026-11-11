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
"real64Result", the rounding; "rationalFloor", the whole number below a rational; and "real64SqrtResult". A fourth axiom
is a proposition, "real64ResultNearest", the specification of the rounding: from 2^1024 - 2^970 on the leave, and below
it a machine real that none is nearer than, an even multiple of the distance to another that is as near. Everything else
is a definition, by a Boolean order of the rationals, "rationalNonNegativeQ", which this library adds: a rational is at
least 0 where the numerator of a pair of it is, which does not depend on the pair. A theorem about real code has the
axioms it uses in its closure: "real64PlusCommutativity" and "real64TimesCommutativity" rest on the rounding as a
function alone.

	"real64NearestQ"[q, m, a, b]     the Boolean that the kernel computes for literals: m 2^a / 2^b is a machine real in
	                                 its form of the largest m, |m| >= 2^52 or the exponent the lowest, and q is within
	                                 half the distance to each neighbour of it, at exactly half only where m is even

The implementation of the rounding computes by integers: the exponent from the lengths in bits of the numerator and the
denominator, and the whole number nearest by a quotient with its remainder against a half. It is trusted for nothing:
"real64NearestQ" refuses a value that is not the nearest, whatever computed it (docs/notes/MachineReals.md).

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
PackageScoped[nearestReal64]
PackageScoped[real64CanonicalForm]
PackageScoped[real64Neighbours]


(* ::Section:: *)
(*Usage Messages*)


machineRealsEnvironment::usage = "machineRealsEnvironment[] gives the environment of the rationals with the machine integers and the 64-bit reals of the compiler's typed entries, built and checked the first time it is asked for."
real64ResultValue::usage = "real64ResultValue[q] gives the term of the machine real nearest the rational q, ties to even, or of the leave where that is past the largest: the implementation of \"real64Result\"."
real64SqrtValue::usage = "real64SqrtValue[q] gives the term of the machine real nearest the square root of the rational q, which is at least 0: the implementation of \"real64SqrtResult\"."
real64ValueTerm::usage = "real64ValueTerm[q] gives HoldComplete of the term of the machine real that is the rational q, with the witness that binary64 represents it, or None where it does not."
nearestReal64::usage = "nearestReal64[q] gives the rational m 2^e, with |m| <= 2^53 and e at least -1074, nearest the rational q, ties to the even m, by integer arithmetic; it is 2^1024 or more where q is 2^1024 - 2^970 or more."
real64CanonicalForm::usage = "real64CanonicalForm[r] gives {m, a, b} for the machine real r as the rational m 2^a / 2^b with the largest m: |m| at least 2^52, or a 0 and b 1074."
real64Neighbours::usage = "real64Neighbours[r] gives the two rationals m 2^e next to the machine real r, the one toward 0 first, or for 0 the one below first; the one above the largest real is 2^1024."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations of the machine integers on the rationals, then the reals' *)
machineRealsEnvironment[] := machineRealsEnvironment[] = withoutStoreTracking[
	libraryEnvironment["MachineReals", rationalsEnvironment[], withStoreCleanup[Fold[addMachineDeclaration, rationalsEnvironment[], Join[$machineDeclarations, $machineRealDeclarations]]]]
]

(* The implementations. The nearest machine real to a rational, by integers: the exponent e with 2^52 <= |q| / 2^e < 2^53,
   no lower than -1074, where the subnormal reals are, and the whole number nearest |q| / 2^e, the even one of two. A
   value from 2^1024 on is no machine real. *)
nearestReal64[0] := 0
nearestReal64[q_] := With[{exponent = Max[binaryExponent[Abs[q]] - 52, -1074]}, Sign[q] nearestWholeNumber[Abs[q] / 2^exponent] 2^exponent]

(* the e with 2^e <= q < 2^(e + 1) for a positive rational q, from the lengths in bits of its numerator and denominator *)
binaryExponent[q_] := With[{estimate = BitLength[Numerator[q]] - BitLength[Denominator[q]]}, If[q < 2^estimate, estimate - 1, estimate]]

(* the whole number nearest a positive rational, the even one of two as near: the quotient of the numerator by the
   denominator, and one more where twice the remainder is past the denominator, or is the denominator and the quotient
   is odd *)
nearestWholeNumber[q_] := With[{division = QuotientRemainder[Numerator[q], Denominator[q]]},
	Which[
		2 Last[division] > Denominator[q], First[division] + 1,
		2 Last[division] < Denominator[q], First[division],
		True, First[division] + Mod[First[division], 2]
	]
]

(* a machine real as m 2^a / 2^b with the largest m, which "real64NearestQ" asks for; 0 is 0 at the lowest exponent *)
real64CanonicalForm[0] := {0, 0, 1074}
real64CanonicalForm[r_] := With[{exponent = Max[binaryExponent[Abs[r]] - 52, -1074]}, {r / 2^exponent, Max[exponent, 0], Max[-exponent, 0]}]

(* the machine reals next to one: toward 0, half the spacing away below a power of 2, and away from 0 *)
real64Neighbours[0] := {-2^-1074, 2^-1074}
real64Neighbours[r_] := With[{exponent = Max[binaryExponent[Abs[r]] - 52, -1074]},
	With[{m = Abs[r] / 2^exponent},
		{Sign[r] If[m == 2^52 && exponent > -1074, (2^53 - 1) 2^(exponent - 1), (m - 1) 2^exponent], Sign[r] (m + 1) 2^exponent}
	]
]

real64ResultValue[q_?NumericQ] := With[{nearest = nearestReal64[q]},
	If[ Abs[nearest] < 2^1024,
		real64ValueTerm[nearest],
		HoldComplete[Typed["right"[Failure["NotFinite", <||>]], "Real64" | Failure]]
	]
]

(* no square root of a machine real is half way between two, so 60 digits of it round as the root itself does *)
real64SqrtValue[q_?NumericQ] := real64ResultValue[If[IntegerQ[Sqrt[q]] || Head[Sqrt[q]] === Rational, Sqrt[q], Rationalize[N[Sqrt[q], 60], 0]]]

(* the term of a machine real: its rational with the witness, the m and the exponents of 2 above and below. The m is
   odd, but for a real past 2^971 times an odd number, whose m takes the factors of 2 past 2^971 *)
real64ValueTerm[0] := HoldComplete[Typed["left"["subtype"[Typed[0, Rationals], "real64RepresentableOfWitness"[Typed[0, Rationals], 0, 0, 0,
	"equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"]]]], "Real64" | Failure]]
real64ValueTerm[q_] := With[{exponent = Min[IntegerExponent[Numerator[q], 2] - IntegerExponent[Denominator[q], 2], 971]},
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
		(* the least significand of a normal real, 2^52, and the middle of the largest real and 2^1024, 2^1024 - 2^970 *)
		power = 4503599627370496,
		bound = 2^1024 - 2^970,
		(* the largest power of 2 a machine real is a multiple of, 2^971 *)
		top = 2^971,
		tolerance = 1 / 70368744177664
	},
	{
		(* the absolute value, by the Boolean order of the rationals (Rationals.wl) *)
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
		(* The specification of the rounding, an axiom that is a proposition. From the bound on, the leave. Below it, a
		   machine real r that no machine real is nearer to q than; and where another, s, is as near, r is an even
		   multiple of their distance: two machine reals as near to q as each other are neighbours, and neighbours are
		   consecutive multiples of their distance, so "even" needs no significand, which m 2^e does not have uniquely.
		   Such a function exists and is the only one (docs/notes/MachineReals.md): IEEE 754's roundTiesToEven with
		   the leave for its infinities. *)
		TypeTheoryAxiom["real64ResultNearest",
			ForAll[{Typed[q, Rationals]},
				And[
					Implies[Typed[bound, Rationals] <= "rationalAbsolute"[q], "real64Result"[q] == Typed["right"[Failure["NotFinite", <||>]], "Real64" | Failure]],
					Implies["rationalAbsolute"[q] < Typed[bound, Rationals],
						Exists[{Typed[r, "Real64"]},
							And[
								"real64Result"[q] == Typed["left"[r], "Real64" | Failure],
								And[
									ForAll[{Typed[s, "Real64"]}, "rationalAbsolute"[q - r[["rational"]]] <= "rationalAbsolute"[q - s[["rational"]]]],
									ForAll[{Typed[s, "Real64"]},
										Implies[s[["rational"]] != r[["rational"]],
											Implies["rationalAbsolute"[q - s[["rational"]]] == "rationalAbsolute"[q - r[["rational"]]],
												Exists[{Typed[n, Integers]}, r[["rational"]] == 2 "rationalOfInteger"[n] (s[["rational"]] - r[["rational"]])]
											]
										]
									]
								]
							]
						]
					]
				]
			]
		],
		(* The Boolean of a value and its nearness, which the kernel computes for literals. The value is m 2^a / 2^b in
		   its form of the largest m: in the range of a machine real, and |m| at least 2^52 or the exponent the lowest,
		   a 0 and b 1074. With everything times 2^b, the spacing above |r| is u = 2^a, and d is how far q is past r away
		   from 0, (q 2^b - m 2^a) by the sign of m. An even m takes q up to half the spacing on each side, u / 2 away
		   from 0 and toward 0, where the spacing is u / 2 below a power of 2 that is not at the lowest exponent, u / 4;
		   an odd m takes q strictly within half, as the tie goes to its even neighbour. The largest real is odd, so
		   the bound 2^1024 - 2^970 is refused. *)
		TypeTheoryDefinition["real64NearestQ", Typed[
			Function[{Typed[q, Rationals], Typed[m, Integers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
				Function[{Typed[lowest, Booleans], Typed[d, Rationals], Typed[u, Rationals]},
					"and"[
						"and"["integerLessEqualQ"[Typed[-mantissa, Integers], m], "and"["integerLessEqualQ"[m, Typed[mantissa, Integers]], "and"["lessEqual"[a, 971], "lessEqual"[b, 1074]]]],
						"and"[
							"or"["or"["integerLessEqualQ"[Typed[power, Integers], m], "integerLessEqualQ"[m, Typed[-power, Integers]]], lowest],
							"machineIf"["integerEqual"[Mod[m, 2], 0],
								"and"[
									"rationalLessEqualQ"[2 d, u],
									"machineIf"["and"["or"["integerEqual"[m, Typed[power, Integers]], "integerEqual"[m, Typed[-power, Integers]]], "not"[lowest]],
										"rationalLessEqualQ"[-(4 d), u],
										"rationalLessEqualQ"[-(2 d), u]
									]
								],
								"and"["rationalLessQ"[2 d, u], "rationalLessQ"[-(2 d), u]]
							]
						]
					]
				][
					"and"["equal"[a, 0], "equal"[b, 1074]],
					Function[{Typed[difference, Rationals]}, "machineIf"["integerLessEqualQ"[0, m], difference, -difference]][
						q "rationalOfInteger"["integerOfNatural"[2^b]] - "rationalOfInteger"[m "integerOfNatural"[2^a]]
					],
					"rationalOfInteger"["integerOfNatural"[2^a]]
				]
			],
			Rationals -> Integers -> NonNegativeIntegers -> NonNegativeIntegers -> Booleans
		]],

		(* the operations on the values of machine reals, as the compiler's table of typed operations has them *)
		TypeTheoryDefinition["real64Plus", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Result"[x + y]], Rationals -> Rationals -> ("Real64" | Failure)]],
		TypeTheoryDefinition["real64Subtract", Typed[Function[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Result"[x - y]], Rationals -> Rationals -> ("Real64" | Failure)]],
		(* the sum of machine reals does not depend on their order, as the sum of their values does not *)
		TypeTheoryTheorem["real64PlusCommutativity",
			ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Plus"[x, y] == "real64Plus"[y, x]],
			Function[{Typed[x, Rationals], Typed[y, Rationals]}, "equalityCongruence"["real64Result", "rationalAdditionCommutativity"[x, y]]]
		],
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
		TypeTheoryTheorem["real64TimesCommutativity",
			ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Times"[x, y] == "real64Times"[y, x]],
			Function[{Typed[x, Rationals], Typed[y, Rationals]}, "equalityCongruence"["real64Normal", "rationalMultiplicationCommutativity"[x, y]]]
		],
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
		]],

		(* The order through the absolute value, equality of machine reals by their values, and three properties of the
		   rounding from its specification: a machine real is its own result, the rounding is monotone, and a result is within
		   half the distance of two machine reals that enclose the rational *)
		machineTheorem["rationalAbsoluteOfNonNegativeQ", ForAll[{Typed[x, Rationals]}, Implies["rationalNonNegativeQ"[x] == "true", "rationalAbsolute"[x] == x]],
			{"Introduce"[x, e], "Exact"["equalityCongruence"[Function[{Typed[b, Booleans]}, "machineIf"[b, x, -x]], e]]}],
		machineTheorem["rationalAbsoluteOfNegativeQ", ForAll[{Typed[x, Rationals]}, Implies["rationalNonNegativeQ"[x] == "false", "rationalAbsolute"[x] == -x]],
			{"Introduce"[x, e], "Exact"["equalityCongruence"[Function[{Typed[b, Booleans]}, "machineIf"[b, x, -x]], e]]}],
		machineTheorem["rationalAbsoluteNonnegative", ForAll[{Typed[x, Rationals]}, 0 <= "rationalAbsolute"[x]],
			{"Introduce"[x], "Cases"["booleanCases"["rationalNonNegativeQ"[x]]],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNonNegativeQ"[x, e]], "Exact"["rationalNonNegativeQTrue"[x, e]],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNegativeQ"[x, e]], "Exact"["rationalNonNegativeQTrue"[-x, "rationalNonNegativeQNegation"[x, e]]]}],
		machineTheorem["rationalLessEqualAbsolute", ForAll[{Typed[x, Rationals]}, x <= "rationalAbsolute"[x]],
			{"Introduce"[x], "Cases"["booleanCases"["rationalNonNegativeQ"[x]]],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNonNegativeQ"[x, e]], "Exact"["rationalLessEqualReflexivity"[x]],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNegativeQ"[x, e]],
				"Exact"["rationalLessEqualTransitivity"[x, 0, -x,
					"rationalNonpositiveOfNegation"[x, "rationalNonNegativeQTrue"[-x, "rationalNonNegativeQNegation"[x, e]]],
					"rationalNonNegativeQTrue"[-x, "rationalNonNegativeQNegation"[x, e]]]]}],
		machineTheorem["rationalNegationLessEqualAbsolute", ForAll[{Typed[x, Rationals]}, -x <= "rationalAbsolute"[x]],
			{"Introduce"[x], "Cases"["booleanCases"["rationalNonNegativeQ"[x]]],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNonNegativeQ"[x, e]],
				"Exact"["rationalLessEqualTransitivity"[-x, 0, x, "rationalNegationNonpositive"[x, "rationalNonNegativeQTrue"[x, e]], "rationalNonNegativeQTrue"[x, e]]],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNegativeQ"[x, e]], "Exact"["rationalLessEqualReflexivity"[-x]]}],
		machineTheorem["rationalAbsoluteLessEqual", ForAll[{Typed[x, Rationals], Typed[b, Rationals]}, Implies[x <= b, Implies[-x <= b, "rationalAbsolute"[x] <= b]]],
			{"Introduce"[x, b, h1, h2], "Cases"["booleanCases"["rationalNonNegativeQ"[x]]],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNonNegativeQ"[x, e]], "Exact"[h1],
				"Introduce"[e], "Rewrite"["rationalAbsoluteOfNegativeQ"[x, e]], "Exact"[h2]}],
		machineTheorem["rationalAbsoluteBounds", ForAll[{Typed[x, Rationals], Typed[b, Rationals]}, Implies["rationalAbsolute"[x] <= b, And[x <= b, -x <= b]]],
			{"Introduce"[x, b, h], "Exact"["andIntroduction"[
				"rationalLessEqualTransitivity"[x, "rationalAbsolute"[x], b, "rationalLessEqualAbsolute"[x], h],
				"rationalLessEqualTransitivity"[-x, "rationalAbsolute"[x], b, "rationalNegationLessEqualAbsolute"[x], h]]]}],
		machineTheorem["rationalAbsoluteOfNonnegative", ForAll[{Typed[x, Rationals]}, Implies[0 <= x, "rationalAbsolute"[x] == x]],
			{"Introduce"[x, h], "Exact"["rationalAbsoluteOfNonNegativeQ"[x, "rationalNonNegativeQComplete"[x, h]]]}],
		machineTheorem["rationalAbsoluteOfNonpositive", ForAll[{Typed[x, Rationals]}, Implies[0 <= -x, "rationalAbsolute"[x] == -x]],
			{"Introduce"[x, h], "Apply"["rationalLessEqualAntisymmetry"],
				"Exact"["rationalAbsoluteLessEqual"[x, -x, "rationalLessEqualTransitivity"[x, 0, -x, "rationalNonpositiveOfNegation"[x, h], h], "rationalLessEqualReflexivity"[-x]]],
				"Exact"["rationalNegationLessEqualAbsolute"[x]]}],
		machineTheorem["rationalHalfSpacingOfNearest",
			ForAll[{Typed[q, Rationals], Typed[r, Rationals], Typed[s, Rationals], Typed[t, Rationals]},
				Implies["rationalAbsolute"[q - r] <= "rationalAbsolute"[q - s], Implies["rationalAbsolute"[q - r] <= "rationalAbsolute"[q - t],
					Implies[s <= q, Implies[q <= t, "rationalAbsolute"[q - r] + "rationalAbsolute"[q - r] <= t - s]]]]],
			{"Introduce"[q, r, s, t, h1, h2, hs, ht], "Rewrite"["rationalSpacingSum"[q, s, t]], "Apply"["rationalLessEqualSum"],
				"Rewrite"["rationalAbsoluteOfNonnegative"[q - s, "rationalDifferenceOfLessEqual"[s, q, hs]], "RightToLeft"], "Exact"[h1],
				"Rewrite"["rationalAbsoluteOfNonpositive"[q - t, "rationalNegatedDifferenceOfLessEqual"[q, t, ht]], "RightToLeft"], "Exact"[h2]}],
		machineTheorem["rationalZeroOfAbsolute", ForAll[{Typed[x, Rationals]}, Implies["rationalAbsolute"[x] <= 0, x == 0]],
			{"Introduce"[x, h], "Apply"["rationalLessEqualAntisymmetry"],
				"Exact"["rationalLessEqualTransitivity"[x, "rationalAbsolute"[x], 0, "rationalLessEqualAbsolute"[x], h]],
				"Exact"["rationalNonnegativeOfNegation"[x, "rationalLessEqualTransitivity"[-x, "rationalAbsolute"[x], 0, "rationalNegationLessEqualAbsolute"[x], h]]]}],
		machineTheorem["rationalNearestOfSelf", ForAll[{Typed[q, Rationals], Typed[r, Rationals]}, Implies["rationalAbsolute"[q - r] <= "rationalAbsolute"[q - q], r == q]],
			{"Introduce"[q, r, h], "Rewrite"["rationalSelfDifference"[q], "At" -> h], "Apply"["rationalEqualOfDifference"], "Exact"["rationalZeroOfAbsolute"[q - r, h]]}],
		machineTheorem["subtypeEquality",
			ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[P, TypeSpecifier[{A} -> TypeUniverse[0]]], Typed[a, A], Typed[b, A], Typed[h, P[a]], Typed[k, P[b]]}, Implies[a == b, "subtype"[a, h] == "subtype"[b, k]]],
			{"Introduce"[A, P, a, b, h, k, e], "Induction"[e], "Introduce"[k2], "Reflexivity"}],
		machineTheorem["subtypeExtensionality",
			ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[P, TypeSpecifier[{A} -> TypeUniverse[0]]], Typed[x, Subtype[P]], Typed[y, Subtype[P]]}, Implies[x[["element"]] == y[["element"]], x == y]],
			{"Introduce"[A, P, x, y], "Cases"[x], "Introduce"[a, h], "Cases"[y], "Introduce"[b, k, e], "Exact"["subtypeEquality"[a, b, h, k, e]]}],
		machineTheorem["real64Extensionality", ForAll[{Typed[x, "Real64"], Typed[y, "Real64"]}, Implies[x[["rational"]] == y[["rational"]], x == y]],
			{"Introduce"[x, y, e], "Exact"["subtypeExtensionality"[x, y, e]]}],
		machineTheorem["rationalNearerOfLeft", ForAll[{Typed[q, Rationals], Typed[a, Rationals], Typed[b, Rationals]},
				Implies[a <= b, Implies["rationalAbsolute"[q - b] <= "rationalAbsolute"[q - a], Or[a + b <= q + q, b <= a]]]],
			{"Introduce"[q, a, b, hab, h], "Cases"["rationalLessEqualTotality"[q, a]],
				(* q <= a <= b: both distances are the negated differences, and b <= a *)
				"Introduce"[hq], "Apply"["orIntroductionRight"],
				"Rewrite"["rationalAbsoluteOfNonpositive"[q - b, "rationalNegatedDifferenceOfLessEqual"[q, b, "rationalLessEqualTransitivity"[q, a, b, hq, hab]]], "At" -> h],
				"Rewrite"["rationalAbsoluteOfNonpositive"[q - a, "rationalNegatedDifferenceOfLessEqual"[q, a, hq]], "At" -> h],
				"Apply"["rationalLessEqualOfEqualDifference"[-(q - b), -(q - a)]], "Ring", "Exact"[h],
				(* a <= q: the distance to a is q - a, and b - q is at most the distance to b *)
				"Introduce"[hq], "Apply"["orIntroductionLeft"],
				"Rewrite"["rationalAbsoluteOfNonnegative"[q - a, "rationalDifferenceOfLessEqual"[a, q, hq]], "At" -> h],
				"Apply"["rationalLessEqualOfEqualDifference"[-(q - b), q - a]], "Ring",
				"Exact"["rationalLessEqualTransitivity"[-(q - b), "rationalAbsolute"[q - b], q - a, "rationalNegationLessEqualAbsolute"[q - b], h]]}],
		machineTheorem["real64LeftInjective",
			ForAll[{Typed[a, "Real64"], Typed[b, "Real64"]}, Implies[Typed["left"[a], "Real64" | Failure] == Typed["left"[b], "Real64" | Failure], a == b]],
			{"Introduce"[a, b, e], "Exact"["equalityCongruence"[
				Function[{Typed[z, "Real64" | Failure]}, InductiveRecursor[DisjointUnionType][
					Function[{Typed[w, "Real64" | Failure]}, "Real64"], Function[{Typed[u, "Real64"]}, u], Function[{Typed[v, Failure]}, a], z]],
				e]]}],
		machineTheorem["real64ResultNearestOf",
			ForAll[{Typed[q, Rationals], Typed[r, "Real64"]},
				Implies["rationalAbsolute"[q] < Typed[bound, Rationals], Implies["real64Result"[q] == Typed["left"[r], "Real64" | Failure],
					ForAll[{Typed[u, "Real64"]}, "rationalAbsolute"[q - r[["rational"]]] <= "rationalAbsolute"[q - u[["rational"]]]]]]],
			{"Introduce"[q, r, hb, e, u], "Cases"["andEliminationRight"["real64ResultNearest"[q]][hb]], "Introduce"[r1, c],
				"Rewrite"["real64LeftInjective"[r, r1, "equalityTransitivity"["equalitySymmetry"[e], "andEliminationLeft"[c]]]],
				"Exact"["andEliminationLeft"["andEliminationRight"[c]][u]]}],
		machineTheorem["real64ResultHalfSpacing",
			ForAll[{Typed[q, Rationals], Typed[r, "Real64"], Typed[s, "Real64"], Typed[t, "Real64"]},
				Implies["rationalAbsolute"[q] < Typed[bound, Rationals], Implies["real64Result"[q] == Typed["left"[r], "Real64" | Failure],
					Implies[s[["rational"]] <= q, Implies[q <= t[["rational"]],
						"rationalAbsolute"[q - r[["rational"]]] + "rationalAbsolute"[q - r[["rational"]]] <= t[["rational"]] - s[["rational"]]]]]]],
			{"Introduce"[q, r, s, t, hb, e, hs, ht],
				"Exact"["rationalHalfSpacingOfNearest"[q, r[["rational"]], s[["rational"]], t[["rational"]], "real64ResultNearestOf"[q, r, hb, e, s], "real64ResultNearestOf"[q, r, hb, e, t], hs, ht]]}],
		machineTheorem["real64ResultOfRepresentable",
			ForAll[{Typed[x, "Real64"]}, Implies["rationalAbsolute"[x[["rational"]]] < Typed[bound, Rationals], "real64Result"[x[["rational"]]] == Typed["left"[x], "Real64" | Failure]]],
			{"Introduce"[x, hb], "Cases"["andEliminationRight"["real64ResultNearest"[x[["rational"]]]][hb]], "Introduce"[r, c],
				"Rewrite"["andEliminationLeft"[c]],
				"Rewrite"["real64Extensionality"[r, x, "rationalNearestOfSelf"[x[["rational"]], r[["rational"]], "andEliminationLeft"["andEliminationRight"[c]][x]]]]}],
		(* the mirror of the lemma before: at least as near to the lower one, q is at most the middle *)
		machineTheorem["rationalNearerOfRight", ForAll[{Typed[q, Rationals], Typed[a, Rationals], Typed[b, Rationals]},
				Implies[a <= b, Implies["rationalAbsolute"[q - a] <= "rationalAbsolute"[q - b], Or[q + q <= a + b, b <= a]]]],
			{"Introduce"[q, a, b, hab, h], "Cases"["rationalLessEqualTotality"[b, q]],
				"Introduce"[hq], "Apply"["orIntroductionRight"],
				"Rewrite"["rationalAbsoluteOfNonnegative"[q - a, "rationalDifferenceOfLessEqual"[a, q, "rationalLessEqualTransitivity"[a, b, q, hab, hq]]], "At" -> h],
				"Rewrite"["rationalAbsoluteOfNonnegative"[q - b, "rationalDifferenceOfLessEqual"[b, q, hq]], "At" -> h],
				"Apply"["rationalLessEqualOfEqualDifference"[q - a, q - b]], "Ring", "Exact"[h],
				"Introduce"[hq], "Apply"["orIntroductionLeft"],
				"Rewrite"["rationalAbsoluteOfNonpositive"[q - b, "rationalNegatedDifferenceOfLessEqual"[q, b, hq]], "At" -> h],
				"Apply"["rationalLessEqualOfEqualDifference"[q - a, -(q - b)]], "Ring",
				"Exact"["rationalLessEqualTransitivity"[q - a, "rationalAbsolute"[q - a], -(q - b), "rationalLessEqualAbsolute"[q - a], h]]}],
		machineTheorem["rationalNearestMonotone", ForAll[{Typed[p, Rationals], Typed[q, Rationals], Typed[a, Rationals], Typed[b, Rationals]},
				Implies[p <= q, Implies["rationalAbsolute"[p - b] <= "rationalAbsolute"[p - a], Implies["rationalAbsolute"[q - a] <= "rationalAbsolute"[q - b], Implies[a <= b, Or[b <= a, p == q]]]]]],
			{"Introduce"[p, q, a, b, hpq, n1, n2, hab],
				"Cases"["rationalNearerOfLeft"[p, a, b, hab, n1]],
				"Introduce"[h1], "Cases"["rationalNearerOfRight"[q, a, b, hab, n2]],
				"Introduce"[h2], "Apply"["orIntroductionRight"], "Apply"["rationalLessEqualAntisymmetry"], "Exact"[hpq],
				"Exact"["rationalDoubleLessEqual"[q, p, "rationalLessEqualTransitivity"[q + q, a + b, p + p, h2, h1]]],
				"Introduce"[h2], "Exact"["orIntroductionLeft"[h2]],
				"Introduce"[h1], "Exact"["orIntroductionLeft"[h1]]}],
		machineTheorem["real64ResultMonotone",
			ForAll[{Typed[p, Rationals], Typed[q, Rationals], Typed[r, "Real64"], Typed[s, "Real64"]},
				Implies["rationalAbsolute"[p] < Typed[bound, Rationals], Implies["rationalAbsolute"[q] < Typed[bound, Rationals], Implies[p <= q,
					Implies["real64Result"[p] == Typed["left"[r], "Real64" | Failure], Implies["real64Result"[q] == Typed["left"[s], "Real64" | Failure],
						r[["rational"]] <= s[["rational"]]]]]]]],
			{"Introduce"[p, q, r, s, hp, hq, hpq, ep, eq],
				"Cases"["rationalLessEqualTotality"[r[["rational"]], s[["rational"]]]],
				"Introduce"[h], "Exact"[h],
				"Introduce"[h], "Cases"["rationalNearestMonotone"[p, q, s[["rational"]], r[["rational"]], hpq,
					"real64ResultNearestOf"[p, r, hp, ep, s], "real64ResultNearestOf"[q, s, hq, eq, r], h]],
				"Introduce"[g], "Exact"[g],
				"Introduce"[g],
				"Rewrite"["real64LeftInjective"[r, s, "equalityTransitivity"["equalitySymmetry"[ep], "equalityTransitivity"["equalityCongruence"[Function[{Typed[z, Rationals]}, "real64Result"[z]], g], eq]]]],
				"Exact"["rationalLessEqualReflexivity"[s[["rational"]]]]}],
		machineTheorem["rationalScaledBound",
			ForAll[{Typed[q, Rationals], Typed[c, Rationals], Typed[u, Rationals], Typed[v, Rationals], Typed[t, Rationals], Typed[w, Rationals]},
				Implies[q c == u v, Implies[1 <= c, Implies[0 <= v, Implies[v <= t, Implies[u <= w, Implies[-w <= u, Implies[0 <= w, "rationalAbsolute"[q] <= w t]]]]]]]],
			{"Introduce"[q, c, u, v, t, w, e, hc, hv, hvt, huw, hwu, hw], "Apply"["rationalAbsoluteLessEqual"],
				"Exact"["rationalScaledUpperBound"[q, c, u, v, t, w, e, hc, hv, hvt, huw, hw]],
				"Apply"["rationalScaledUpperBound"[-q, c, -u, v, t, w, "rationalNegatedScaled"[q, c, u, v, e], hc, hv, hvt]],
				"Rewrite"["rationalNegationNegation"[w], "RightToLeft"], "Exact"["rationalLessEqualNegation"[-w, u, hwu]],
				"Exact"[hw]}],
		(* the witness of a machine real bounds its value: q 2^b == m 2^a with |m| <= 2^53 - 1 and a <= 971 *)
		machineTheorem["real64RepresentableBound",
			ForAll[{Typed[q, Rationals], Typed[m, Integers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
				Implies[q "rationalOfInteger"["integerOfNatural"[2^b]] == "rationalOfInteger"[m "integerOfNatural"[2^a]],
					Implies[Typed[-mantissa, Integers] <= m, Implies[m <= Typed[mantissa, Integers], Implies[a <= 971,
						"rationalAbsolute"[q] <= Typed[mantissa, Rationals] Typed[top, Rationals]]]]]],
			{"Introduce"[q, m, a, b, e, h1, h2, ha],
				"Apply"["rationalScaledBound"[q, "rationalOfInteger"["integerOfNatural"[2^b]], "rationalOfInteger"[m], "rationalOfInteger"["integerOfNatural"[2^a]], Typed[top, Rationals], Typed[mantissa, Rationals]]],
				(* q 2^b == m 2^a, the rational of the product being the product of the rationals *)
				"Exact"["equalityTransitivity"[e, "rationalOfIntegerMultiplication"[m, "integerOfNatural"[2^a]]]],
				(* 1 <= 2^b *)
				"Exact"["rationalOfIntegerMonotone"["integerOfNatural"[1], "integerOfNatural"[2^b], "integerOfNaturalMonotone"[1, 2^b, "powerOfTwoPositive"[b]]]],
				(* 0 <= 2^a *)
				"Exact"["rationalOfIntegerMonotone"["integerOfNatural"[0], "integerOfNatural"[2^a], "integerOfNaturalMonotone"[0, 2^a, "lessEqualZero"[2^a]]]],
				(* 2^a <= 2^971 *)
				"Exact"["rationalOfIntegerMonotone"["integerOfNatural"[2^a], "integerOfNatural"[2^971], "integerOfNaturalMonotone"[2^a, 2^971, "powerOfTwoMonotone"[a, 971, ha]]]],
				(* m <= 2^53 - 1 and -(2^53 - 1) <= m *)
				"Exact"["rationalOfIntegerMonotone"[m, Typed[mantissa, Integers], h2]],
				"Exact"["rationalOfIntegerMonotone"[Typed[-mantissa, Integers], m, h1]],
				"Decide"}],
		machineTheorem["real64BelowBound", ForAll[{Typed[x, "Real64"]}, "rationalAbsolute"[x[["rational"]]] < Typed[bound, Rationals]],
			{"Introduce"[x], "Cases"[x], "Introduce"[q, w], "Cases"[w], "Introduce"[m, w2], "Cases"[w2], "Introduce"[a, w3], "Cases"[w3], "Introduce"[b, c],
				"Change"["rationalAbsolute"[q] < Typed[bound, Rationals]],
				"Apply"["rationalLessOfLessEqualLess"["rationalAbsolute"[q], Typed[mantissa, Rationals] Typed[top, Rationals], Typed[bound, Rationals]]],
				"Exact"["real64RepresentableBound"[q, m, a, b, "andEliminationLeft"[c], "andEliminationLeft"["andEliminationRight"[c]],
					"andEliminationLeft"["andEliminationRight"["andEliminationRight"[c]]], "andEliminationLeft"["andEliminationRight"["andEliminationRight"["andEliminationRight"[c]]]]]],
				"Decide"}],
		machineTheorem["real64ResultOfReal64", ForAll[{Typed[x, "Real64"]}, "real64Result"[x[["rational"]]] == Typed["left"[x], "Real64" | Failure]],
			{"Introduce"[x], "Exact"["real64ResultOfRepresentable"[x, "real64BelowBound"[x]]]}]
	}
]
