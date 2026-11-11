(* ::Package:: *)

(* Tests for Library/MachineReals.wl: the 64-bit reals of the compiler's typed entries, the rationals that binary64
   represents, in the environment of the rationals with the machine integers. The rounding, the whole number below a
   rational and the square root are axioms that the Wolfram Language computes, with NormalForm's "Implementations"; the
   rest are definitions. Each operation gives the Wolfram Language's own machine real, to the last bit, and leaves
   where compiled code declines.
   Run with: TestReport["TypeTheory/Tests/Library/MachineReals.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

reals = TypeTheoryEnvironment["MachineReals"]

(* the exact rational of a machine real, and the value of a term with the implementations computed *)
realExact[x_] := SetPrecision[x, Infinity]
SetAttributes[realValue, HoldFirst]
realValue[term_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm[term, reals], "Implementations" -> True]]

(* the environment by its name, over the rationals, with the machine integers; its axioms past the rationals' are the
   three the Wolfram Language computes and the specification of the rounding, a proposition that nothing computes; a
   name that is none is refused as before *)
VerificationTest[
	{
		Head[reals],
		Length[Information[reals, "Constants"]] - Length[Information[TypeTheoryEnvironment["Rationals"], "Constants"]],
		Complement[Information[reals, "Axioms"], Information[TypeTheoryEnvironment["Rationals"], "Axioms"]],
		Map[Function[name, Information[TypeTheoryTerm @@ {name, reals}, "Implementation"] =!= None], {"real64Result", "rationalFloor", "real64SqrtResult", "real64ResultNearest"}],
		DefinitionallyEqualQ[TypeTheoryTerm["MachineReal", reals], TypeTheoryTerm["Real64", reals]],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["machinePlus", reals]], TypeTheoryTerm[Integers -> Integers -> ("Integer64" | Failure), reals]],
		TypeTheoryEnvironment["MachineReal"]["Tag"]
	},
	{TypeTheoryEnvironment, 80, {"rationalFloor", "real64Result", "real64ResultNearest", "real64SqrtResult"}, {True, True, True, False}, True, True, "UnknownEnvironment"},
	TestID -> "The-machine-reals-are-over-the-rationals-with-three-computed-axioms"
]

(* the Boolean order of the rationals, which the rationals bring, computes here as it does there *)
VerificationTest[
	TypeTheoryExpression[NormalForm[TypeTheoryTerm[
		{
			"rationalLessEqualQ"[Typed[1/3, Rationals], 1/2], "rationalLessEqualQ"[Typed[1/2, Rationals], 1/3], "rationalLessEqualQ"[Typed[-1/2, Rationals], -1/3],
			"rationalLessEqualQ"[Typed[1/2, Rationals], 1/2], "rationalLessQ"[Typed[1/2, Rationals], 1/2], "rationalLessQ"[Typed[-7, Rationals], 1/1000000],
			"rationalNonNegativeQ"[Typed[0, Rationals]], "rationalNonNegativeQ"[Typed[-1/1000000, Rationals]]
		},
		reals
	]]],
	{True, False, True, True, False, True, True, False},
	TestID -> "The-rationals-have-a-Boolean-order"
]

(* A machine real is a term the kernel checks: the rational with the witness that binary64 represents it, five Booleans
   it computes. The smallest and the largest reals are ones; a rational that binary64 does not represent has no such
   term, and a forged witness, 1/3 with the m of another number, is refused *)
VerificationTest[
	{
		Map[
			Function[x, Replace[WolframInstitute`TypeTheory`PackageScope`real64ValueTerm[realExact[x]], HoldComplete[term_] :> Head[TypeTheoryType[TypeTheoryTerm[term, reals]]]]],
			{0., 2.5, 0.1, -3.75, 5.*^-324, 1.7976931348623157*^308}
		],
		WolframInstitute`TypeTheory`PackageScope`real64ValueTerm[1/3],
		FailureQ[TypeTheoryType[TypeTheoryTerm[
			"subtype"[Typed[1/3, Rationals], "real64RepresentableOfWitness"[Typed[1/3, Rationals], 1, 0, 2,
				"equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"], "equalityReflexivity"["true"]]],
			reals
		]]]
	},
	{ConstantArray[TypeTheoryTerm, 6], None, True},
	TestID -> "A-machine-real-is-a-rational-with-a-witness-the-kernel-checks"
]

(* each operation gives the machine real the Wolfram Language computes, exactly: a sum, a product, a difference, a
   reciprocal, a quotient as x times the rounded 1/y, a square root, and an integer made a real *)
VerificationTest[
	With[{a = realExact[0.1], b = realExact[0.2], c = realExact[1.5]},
		{
			realValue["real64Plus"[Typed[a, Rationals], b]] === realExact[0.1 + 0.2],
			realValue["real64Times"[Typed[a, Rationals], b]] === realExact[0.1 * 0.2],
			realValue["real64Subtract"[Typed[c, Rationals], b]] === realExact[1.5 - 0.2],
			realValue["real64Reciprocal"[Typed[b, Rationals]]] === realExact[1 / 0.2],
			realValue["confirmBind"["real64Reciprocal"[Typed[b, Rationals]], Function[{Typed[r, "Real64"]}, "real64Times"[Typed[c, Rationals], r[["rational"]]]]]] === realExact[1.5 / 0.2],
			realValue["real64Sqrt"[Typed[b, Rationals]]] === realExact[Sqrt[0.2]],
			realValue["real64OfInteger"[9007199254740993]] === realExact[N[9007199254740993]],
			realValue["real64Abs"[Typed[-a, Rationals]]] === realExact[0.1]
		}
	],
	ConstantArray[True, 8],
	TimeConstraint -> 120,
	TestID -> "Each-real-operation-gives-the-Wolfram-Languages-machine-real"
]

(* the leaves, where compiled code declines: a sum past the largest real, a product whose result is below 2^-1022, a
   division by 0., a square root below 0., and a whole number from 9*10^18 on *)
VerificationTest[
	With[{big = realExact[1.7*^308], small = realExact[1.*^-200]},
		{
			realValue["real64Plus"[Typed[big, Rationals], big]],
			realValue["real64Times"[Typed[small, Rationals], small]],
			realValue["real64Reciprocal"[Typed[0, Rationals]]],
			realValue["real64Sqrt"[Typed[-1, Rationals]]],
			realValue["real64Round"[Typed[9000000000000000000, Rationals]]]
		}
	],
	{Failure["NotFinite", <||>], Failure["Underflow", <||>], Failure["NotFinite", <||>], Failure["Domain", <||>], Failure["IntegerOverflow", <||>]},
	TimeConstraint -> 120,
	TestID -> "A-real-operation-leaves-where-compiled-code-declines"
]

(* the whole numbers of a real, Round half to even, and Equal within 2^-46 of the larger *)
VerificationTest[
	{
		Map[Function[q, realValue["real64Round"[Typed[q, Rationals]]]], {5/2, 7/2, -5/2, -7/2, 12/5}],
		{realValue["real64Floor"[Typed[-5/2, Rationals]]], realValue["real64Ceiling"[Typed[-5/2, Rationals]]], realValue["real64IntegerPart"[Typed[-5/2, Rationals]]], realValue["real64IntegerPart"[Typed[5/2, Rationals]]]},
		TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			{"real64EqualQ"[Typed[1, Rationals], 1 + 1/140737488355328], "real64EqualQ"[Typed[1, Rationals], 1 + 1/35184372088832], "real64EqualQ"[Typed[0, Rationals], 0]},
			reals
		]]]
	},
	{{Round[2.5], Round[3.5], Round[-2.5], Round[-3.5], Round[2.4]}, {Floor[-2.5], Ceiling[-2.5], IntegerPart[-2.5], IntegerPart[2.5]}, {1. == 1. + 2.^-47, 1. == 1. + 2.^-45, True}},
	TimeConstraint -> 120,
	TestID -> "Whole-numbers-of-a-real-and-Equal-within-its-tolerance"
]

(* A value that an implementation computed is no proof. The Wolfram Language computes 0.1 + 0.2, but the kernel does not
   compute the axiom, so the sum and its value are not equal by computation: DefinitionallyEqualQ says no, reflexivity
   is refused as the proof of their equation, and the tactic leaves the goal open *)
VerificationTest[
	With[{a = realExact[0.1], b = realExact[0.2]},
		Replace[WolframInstitute`TypeTheory`PackageScope`real64ValueTerm[realExact[0.1 + 0.2]], HoldComplete[sum_] :> {
			realValue["real64Plus"[Typed[a, Rationals], b]] === realExact[0.1 + 0.2],
			DefinitionallyEqualQ[TypeTheoryTerm["real64Plus"[Typed[a, Rationals], b], reals], TypeTheoryTerm[sum, reals]],
			FailureQ[TypeTheoryCheck[
				TypeTheoryTerm["equalityReflexivity"["real64Plus"[Typed[a, Rationals], b]], reals],
				TypeTheoryTerm["real64Plus"[Typed[a, Rationals], b] == sum, reals]
			]],
			Replace[TypeTheoryProof[TypeTheoryTerm["real64Plus"[Typed[a, Rationals], b] == sum, reals], {"Reflexivity"}], {proof_TypeTheoryProof :> proof["Goals"] =!= {}, _ :> True}]
		}]
	],
	{True, False, True, True},
	TimeConstraint -> 120,
	TestID -> "A-value-an-implementation-computed-is-no-proof"
]

(* the largest reals are 2^971 times an m that is even: the witness takes the factors of 2 past 2^971 into m *)
VerificationTest[
	Map[
		Function[x, Replace[WolframInstitute`TypeTheory`PackageScope`real64ValueTerm[realExact[x]], {HoldComplete[term_] :> Head[TypeTheoryType[TypeTheoryTerm[term, reals]]], other_ :> other}]],
		{1.7*^308, 1.*^308, 8.98846567431158*^307}
	],
	{TypeTheoryTerm, TypeTheoryTerm, TypeTheoryTerm},
	TestID -> "A-real-past-2-to-the-971-has-its-witness"
]

(* a theorem about a real operation rests on the axiom it uses, and says so in its closure: the rounding, a constant
   that is assumed, beside the soundness of quotients, which the rationals rest on *)
VerificationTest[
	With[{environment = TypeTheoryEnvironment[reals, TypeTheoryTheorem["real64PlusIsTheResultOfTheSum",
			ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, "real64Plus"[x, y] == "real64Result"[x + y]],
			Function[{Typed[x, Rationals], Typed[y, Rationals]}, "equalityReflexivity"["real64Result"[x + y]]]
		]]},
		{Head[environment], TypeTheoryAxiomClosure[TypeTheoryTerm["real64PlusIsTheResultOfTheSum", environment]]}
	],
	{TypeTheoryEnvironment, <|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature"|>},
	TestID -> "A-real-theorem-names-the-axioms-it-rests-on"
]

(* The sum and the product of machine reals do not depend on the order of their arguments: theorems with content, which
   rest on the rounding as a function and not on its specification. The specification is an axiom, a proposition, and
   a theorem that uses it would say so. *)
VerificationTest[
	{
		Map[Function[name, TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, reals}]], {"real64PlusCommutativity", "real64TimesCommutativity"}],
		With[{statement = TypeTheoryType[TypeTheoryTerm["real64ResultNearest", reals]]}, TypeTheoryType[statement]],
		(* the first half of the specification, at 2^1024: a theorem that uses the axiom names it *)
		With[{bound = 2^1024 - 2^970, top = 2^1024},
			With[{environment = TypeTheoryEnvironment[reals, TypeTheoryTheorem["theLeaveFromTheBound",
					Implies[Typed[bound, Rationals] <= "rationalAbsolute"[Typed[top, Rationals]], "real64Result"[Typed[top, Rationals]] == Typed["right"[Failure["NotFinite", <||>]], "Real64" | Failure]],
					"andEliminationLeft"["real64ResultNearest"[Typed[top, Rationals]]]
				]]},
				{Head[environment], KeySort[TypeTheoryAxiomClosure[TypeTheoryTerm["theLeaveFromTheBound", environment]]]}
			]
		]
	},
	{
		{<|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature"|>, <|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature"|>},
		TypeTheoryTerm[TypeUniverse[0], _],
		{TypeTheoryEnvironment, <|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature", "real64ResultNearest" -> "Proposition"|>}
	},
	SameTest -> MatchQ,
	TestID -> "The-roundings-specification-is-an-axiom-and-sums-and-products-commute"
]

(* The kernel computes whether a machine real is the rounding of a rational: "real64NearestQ" of the rational and the
   real in its form of the largest m. On the ties and the bounds worked by hand, and on products, sums and ties that
   the machine rounds itself, the value that nearestReal64 computes by integers is the one expected, the check accepts
   it, and the check refuses the machine real next to it on each side; from 2^1024 - 2^970 on there is no value, and
   the check refuses the largest real. scripts/real64_nearest_grid.wl runs the whole grid, on any kernel. *)
VerificationTest[
	Module[{nearest, form, next, largest, bound, nearestQ, tie, rows, judge},
		nearest = WolframInstitute`TypeTheory`PackageScope`nearestReal64;
		form = WolframInstitute`TypeTheory`PackageScope`real64CanonicalForm;
		next = WolframInstitute`TypeTheory`PackageScope`real64Neighbours;
		largest = (2^53 - 1) 2^971;
		bound = 2^1024 - 2^970;
		nearestQ[q_, r_] := Replace[form[r], {m_, a_, b_} :> Replace[
			WeakHeadNormalForm[TypeTheoryTerm["real64NearestQ"[Typed[q, Rationals], Typed[m, Integers], a, b], reals]],
			{TypeTheoryTerm["true", ___] -> True, TypeTheoryTerm["false", ___] -> False}
		]];
		tie[m_, e_] := {(2 m + 1) 2^e, realExact[N[m] 2.^e + N[m + 1] 2.^e]};
		rows = Join[
			{
				{2^-1075, 0}, {3 2^-1075, 2 2^-1074}, {2^-1074, 2^-1074}, {2^53 - 1/2, 2^53}, {(2^53 - 1/2) 2^-1074, 2^-1021}, {2^53 + 1, 2^53}, {2^53 + 3, 2^53 + 4},
				{bound, "leave"}, {bound + 2^971, "leave"}, {bound - 2^971, (2^53 - 2) 2^971}, {bound - 1, largest}, {largest, largest}, {0, 0},
				{1/10, 3602879701896397/36028797018963968}
			},
			{
				{-2^-1075, 0}, {-3 2^-1075, -2 2^-1074}, {-(2^53 - 1/2), -2^53}, {-(2^53 + 1), -2^53}, {-bound, "leave"}, {-(bound - 1), -largest}
			},
			{
				{realExact[0.1] realExact[0.2], realExact[0.1 0.2]},
				{realExact[1.7*^300] realExact[1.9*^-200], realExact[1.7*^300 1.9*^-200]},
				{realExact[0.1] + realExact[0.2], realExact[0.1 + 0.2]},
				{1 / realExact[3.], realExact[1 / 3.]},
				tie[2^52 + 12345, 0], tie[2^52 + 12346, -700], tie[2^53 - 2, 300]
			},
			(* rationals whose numerator and denominator are past 2^64, the value by the check alone *)
			{{(3^70 + 2) / (5^40 + 1), None}, {-(7^50 + 4) / (11^30 + 6) / 2^900, None}}
		];
		judge[{q_, expected_}] := With[{value = If[Abs[q] >= bound, "leave", nearest[q]]},
			{
				expected === None || expected === value,
				If[value === "leave", nearestQ[q, Sign[q] largest] === False, nearestQ[q, value]],
				value === "leave" || AllTrue[Select[next[value], Function[r, Abs[r] < 2^1024]], Function[r, nearestQ[q, r] === False]]
			}
		];
		{Length[rows], DeleteDuplicates[Map[judge, rows]]}
	],
	{29, {{True, True, True}}},
	TimeConstraint -> 300,
	TestID -> "The-kernel-computes-whether-a-machine-real-is-the-rounding-of-a-rational"
]

(* Three properties of the rounding, proved from its specification: a machine real is its own result; the rounding is
   monotone; and a result is within half the distance of any two machine reals around the rational, twice its error
   being at most their difference. A machine real is below the bound of the rounding, which no axiom of the reals
   enters. The three rest on the specification, with the result it is of and the soundness of quotients. From the first
   a theorem of real arithmetic follows that no computation gives, x + 0. being x for every machine real x. *)
VerificationTest[
	With[{bound = 2^1024 - 2^970},
		{
			DefinitionallyEqualQ[
				TypeTheoryType[TypeTheoryTerm["real64ResultOfReal64", reals]],
				TypeTheoryTerm[ForAll[{Typed[x, "Real64"]}, "real64Result"[x[["rational"]]] == Typed["left"[x], "Real64" | Failure]], reals]
			],
			DefinitionallyEqualQ[
				TypeTheoryType[TypeTheoryTerm["real64BelowBound", reals]],
				TypeTheoryTerm[ForAll[{Typed[x, "Real64"]}, "rationalAbsolute"[x[["rational"]]] < Typed[bound, Rationals]], reals]
			],
			DefinitionallyEqualQ[
				TypeTheoryType[TypeTheoryTerm["real64ResultMonotone", reals]],
				TypeTheoryTerm[
					ForAll[
						{Typed[p, Rationals], Typed[q, Rationals], Typed[r, "Real64"], Typed[s, "Real64"]},
						Implies["rationalAbsolute"[p] < Typed[bound, Rationals], Implies["rationalAbsolute"[q] < Typed[bound, Rationals], Implies[p <= q,
							Implies["real64Result"[p] == Typed["left"[r], "Real64" | Failure], Implies["real64Result"[q] == Typed["left"[s], "Real64" | Failure],
								r[["rational"]] <= s[["rational"]]]]]]]
					],
					reals
				]
			],
			DefinitionallyEqualQ[
				TypeTheoryType[TypeTheoryTerm["real64ResultHalfSpacing", reals]],
				TypeTheoryTerm[
					ForAll[
						{Typed[q, Rationals], Typed[r, "Real64"], Typed[s, "Real64"], Typed[t, "Real64"]},
						Implies["rationalAbsolute"[q] < Typed[bound, Rationals], Implies["real64Result"[q] == Typed["left"[r], "Real64" | Failure],
							Implies[s[["rational"]] <= q, Implies[q <= t[["rational"]],
								"rationalAbsolute"[q - r[["rational"]]] + "rationalAbsolute"[q - r[["rational"]]] <= t[["rational"]] - s[["rational"]]]]]]
					],
					reals
				]
			],
			Function[name, KeySort[TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, reals}]]] /@ {"real64ResultOfReal64", "real64ResultMonotone", "real64ResultHalfSpacing", "real64BelowBound"},
			With[
				{
					plusZero = TypeTheoryProof[
						ForAll[{Typed[x, "Real64"]}, "real64Plus"[x[["rational"]], 0] == Typed["left"[x], "Real64" | Failure]],
						reals,
						{
							"Introduce"[x],
							"Change"["real64Result"[x[["rational"]] + 0] == Typed["left"[x], "Real64" | Failure]],
							"Rewrite"["rationalAdditionZero"[x[["rational"]]]],
							"Exact"["real64ResultOfReal64"[x]]
						}
					]
				},
				{plusZero["Goals"], KeySort[TypeTheoryAxiomClosure[TypeTheoryTerm["real64PlusZero", TypeTheoryEnvironment[reals, {TypeTheoryTheorem["real64PlusZero", plusZero]}]]]]}
			]
		}
	],
	With[{specified = <|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature", "real64ResultNearest" -> "Proposition"|>},
		{True, True, True, True, {specified, specified, specified, <|"quotientSoundness" -> "Proposition"|>}, {{}, specified}}
	],
	TimeConstraint -> 600,
	TestID -> "A-machine-real-is-its-own-rounding-which-is-monotone-and-within-half-the-spacing"
]
