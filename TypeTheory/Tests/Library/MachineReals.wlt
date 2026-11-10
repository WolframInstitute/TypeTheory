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
   three the Wolfram Language computes; a name that is none is refused as before *)
VerificationTest[
	{
		Head[reals],
		Length[Information[reals, "Constants"]] - Length[Information[TypeTheoryEnvironment["Rationals"], "Constants"]],
		Complement[Information[reals, "Axioms"], Information[TypeTheoryEnvironment["Rationals"], "Axioms"]],
		Map[Function[name, Information[TypeTheoryTerm @@ {name, reals}, "Implementation"] =!= None], {"real64Result", "rationalFloor", "real64SqrtResult"}],
		DefinitionallyEqualQ[TypeTheoryTerm["MachineReal", reals], TypeTheoryTerm["Real64", reals]],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["machinePlus", reals]], TypeTheoryTerm[Integers -> Integers -> ("Integer64" | Failure), reals]],
		TypeTheoryEnvironment["MachineReal"]["Tag"]
	},
	{TypeTheoryEnvironment, 55, {"rationalFloor", "real64Result", "real64SqrtResult"}, {True, True, True}, True, True, "UnknownEnvironment"},
	TestID -> "The-machine-reals-are-over-the-rationals-with-three-computed-axioms"
]

(* the Boolean order of the rationals, which this library adds, computes in the kernel *)
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
