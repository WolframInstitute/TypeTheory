(* ::Package:: *)

(*
The machine integers: TypeTheoryEnvironment["Machine"] is the environment of the integers with the 64-bit integers of
the compiler's typed entries, built and checked the first time it is asked for. A machine integer is an integer in
[-2^63, 2^63), a subtype of the integers, and an operation on machine integers gives the machine integer of the
integer it computes where that integer is in range, and a failure, Failure["IntegerOverflow", <||>], where it is
not: a typed entry of the compiler leaves its machine code for the generic code of the Wolfram Language where a
value is out of its type, and the failure is that leave.

	"Integer64"                      Subtype["integer64Range"], an integer with -2^63 <= integer < 2^63, as the
	                                 compiler and NumericArray name the type; n["integer"] is the integer of a
	                                 machine integer n, and n["proof"] the proof that it is in range
	"MachineInteger", "Boolean"      the compiler's other names: "Integer64" on a 64-bit machine, and the Booleans
	"machineResult"[x]               the machine integer of x where x is in range, "left", and the failure where it
	                                 is not, "right": Integer64 | Failure. It computes x first, so the value holds the
	                                 class of one pair of literals, not the expression that x was
	"machinePlus", "machineTimes"    the machine's sum and product of two integers: the machine result of the exact one
	"machineIf"[b, x, y]             the compiler's If of a Boolean test
	"machineQuotient", "machineMod"  the machine's quotient, rounded down, and remainder of two integers, leaving with
	                                 Failure["DivideByZero", <||>] by 0

The range is decided by the order of the integers, "integerLessEqualDecidable", so a machine result of literals
computes: "machineResult"[5] is the machine integer 5, and "machineResult"[2^63] the failure. Where an exact result is
in range it is the machine value, "machineResultInRange", and the natural numbers below 2^63 are machine integers,
"naturalInteger64Range": the first steps of the bridge from the machine's arithmetic to the mathematics, which
TypeTheoryFormalize[f, "Machine"] is to state of a compiled function.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[machineEnvironment]


(* ::Section:: *)
(*Usage Messages*)


machineEnvironment::usage = "machineEnvironment[] gives the environment of the integers with the 64-bit integers of the compiler's typed entries, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations in order, each theorem proved by its tactics in the environment so far *)
machineEnvironment[] := machineEnvironment[] = withoutStoreTracking[
	libraryEnvironment["Machine", integersEnvironment[], withStoreCleanup[Fold[addMachineDeclaration, integersEnvironment[], $machineDeclarations]]]
]

SetAttributes[machineTheorem, HoldAll]

addMachineDeclaration[failure_Failure, _] := failure
addMachineDeclaration[environment_, machineTheorem[name_, statement_, tactics_List]] :=
	TypeTheoryEnvironment[environment, {TypeTheoryTheorem[name, TypeTheoryProof[statement, environment, tactics]]}]
addMachineDeclaration[environment_, declaration_] := TypeTheoryEnvironment[environment, {declaration}]

(* the bounds written as literals, never as powers, which the integers would compute one factor at a time *)
$machineDeclarations = With[{lower = -9223372036854775808, upper = 9223372036854775808}, {
	TypeTheoryDefinition["machineDecision", Function[{Typed[q, TypeUniverse[0]], Annotation[Typed[d, Decidable[q]], "InstanceImplicit"]}, d]],
	(* the variable of the range names the element of the subtype: n["integer"] is the integer of a machine integer n *)
	TypeTheoryDefinition["integer64Range", Typed[Typed[integer, Integers] |-> Typed[lower, Integers] <= integer && integer < Typed[upper, Integers], Integers -> TypeUniverse[0]]],
	TypeTheoryDefinition["Integer64", Subtype["integer64Range"]],
	(* the compiler's names: "MachineInteger" is "Integer64" on a 64-bit machine, and "Boolean" the Booleans *)
	TypeTheoryDefinition["MachineInteger", "Integer64"],
	TypeTheoryDefinition["Boolean", Booleans],
	(* A machine value is one 64-bit integer, so its integer is kept as the class of one pair of literals, (n, 0) or
	   (0, n), whatever expression computed it: "machineResult" computes its argument first. The kernel reduces a term
	   only where it reads it, and a value that kept its sum as written would be computed again at every read, with
	   everything it was computed from.
	   "naturalStrict"[f, n] is f[n] with n computed first: the recursor reads n to choose its case, and gives f the
	   literal, 0 or the one before it and 1. "integerStrict"[f, x] is f[x] with x computed first, as the class of its
	   normal pair, each part computed. Both are f at the argument, "naturalStrictApply" and "integerStrictApply": the
	   first in each case by computation, the second for the class of a pair, whose normal pair is of its class,
	   "subtractionBalance". *)
	machineTheorem["additionSuccessorSwap",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, (k + m) + 1 == (k + 1) + m],
		{"Introduce"[k, m], "Ring"}
	],
	TypeTheoryTheorem["subtractionBalance",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Subtract[a, b] + b == a + Subtract[b, a]],
		Function[{Typed[a, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[n, NonNegativeIntegers]}, ForAll[{Typed[b, NonNegativeIntegers]}, Subtract[n, b] + b == n + Subtract[b, n]]],
			Function[{Typed[b, NonNegativeIntegers]}, "equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + b], "subtractionZeroLeft"[b]]],
			Function[{Typed[k, NonNegativeIntegers], Typed[ih, ForAll[{Typed[b, NonNegativeIntegers]}, Subtract[k, b] + b == k + Subtract[b, k]]], Typed[b, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[c, NonNegativeIntegers]}, Subtract[k + 1, c] + c == (k + 1) + Subtract[c, k + 1]],
					"equalitySymmetry"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, (k + 1) + x], "subtractionZeroLeft"[k + 1]]],
					Function[{Typed[d, NonNegativeIntegers], Typed[ihd, Subtract[k + 1, d] + d == (k + 1) + Subtract[d, k + 1]]},
						"equalityTransitivity"[
							"equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + (d + 1)], "subtractionSuccessor"[k, d]],
							"equalityTransitivity"[
								"equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + 1], ih[d]],
								"equalityTransitivity"[
									"additionSuccessorSwap"[k, Subtract[d, k]],
									"equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, (k + 1) + x], "equalitySymmetry"["subtractionSuccessor"[d, k]]]
								]
							]
						]
					],
					b
				]
			],
			a
		]]
	],
	TypeTheoryDefinition["naturalStrict", Function[{TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, NonNegativeIntegers -> B], Typed[n, NonNegativeIntegers]},
		InductiveRecursor[NonNegativeIntegers][Function[{Typed[j, NonNegativeIntegers]}, B], f[0], Function[{Typed[k, NonNegativeIntegers], Typed[r, B]}, f[k + 1]], n]
	]],
	TypeTheoryTheorem["naturalStrictApply",
		ForAll[{TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, NonNegativeIntegers -> B], Typed[n, NonNegativeIntegers]}, "naturalStrict"[f, n] == f[n]],
		Function[{TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, NonNegativeIntegers -> B], Typed[n, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[m, NonNegativeIntegers]}, "naturalStrict"[f, m] == f[m]],
				"equalityReflexivity"[f[0]],
				Function[{Typed[k, NonNegativeIntegers], Typed[h, "naturalStrict"[f, k] == f[k]]}, "equalityReflexivity"[f[k + 1]]],
				n
			]
		]
	],
	TypeTheoryDefinition["integerStrict", Function[{TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, Integers -> B], Typed[x, Integers]},
		"naturalStrict"[
			Function[{Typed[a, NonNegativeIntegers]}, "naturalStrict"[Function[{Typed[b, NonNegativeIntegers]}, f["integerOfPair"["pair"[a, b]]]], "integerNormalPair"[x][[2]]]],
			"integerNormalPair"[x][[1]]
		]
	]],
	TypeTheoryTheorem["integerStrictApply",
		ForAll[{TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, Integers -> B], Typed[x, Integers]}, "integerStrict"[f, x] == f[x]],
		Function[{TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, Integers -> B], Typed[x, Integers]},
			Construct[QuotientInduction, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers], "integerRelation",
				Function[{Typed[z, Integers]}, "integerStrict"[f, z] == f[z]],
				Function[{Typed[s, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]]},
					"equalityTransitivity"[
						"naturalStrictApply"[
							Function[{Typed[a, NonNegativeIntegers]}, "naturalStrict"[Function[{Typed[b, NonNegativeIntegers]}, f["integerOfPair"["pair"[a, b]]]], Subtract[s[[2]], s[[1]]]]],
							Subtract[s[[1]], s[[2]]]
						],
						"equalityTransitivity"[
							"naturalStrictApply"[Function[{Typed[b, NonNegativeIntegers]}, f["integerOfPair"["pair"[Subtract[s[[1]], s[[2]]], b]]]], Subtract[s[[2]], s[[1]]]],
							"equalityCongruence"[f, "quotientSoundness"[
								Typed["subtractionBalance"[s[[1]], s[[2]]], "integerRelation"["pair"[Subtract[s[[1]], s[[2]]], Subtract[s[[2]], s[[1]]]], s]]
							]]
						]
					]
				],
				x
			]
		]
	],
	(* the machine integer of an integer in range, and the leave where it is out of range, of the integer as it is given *)
	TypeTheoryDefinition["machineResultOfCanonical", Typed[
		Typed[x, Integers] |-> InductiveRecursor[Decidable][
			Typed[d, Decidable["integer64Range"[x]]] |-> "Integer64" | Failure,
			Typed[h, Not["integer64Range"[x]]] |-> Typed["right"[Failure["IntegerOverflow", <||>]], "Integer64" | Failure],
			Typed[h, "integer64Range"[x]] |-> Typed["left"["subtype"[x, h]], "Integer64" | Failure],
			"machineDecision"["integer64Range"[x]]
		],
		Integers -> ("Integer64" | Failure)
	]],
	(* an integer in range is the machine value, with no overflow: the decision of the range, whatever the instance,
	   takes its true case, and any two proofs of the range are one *)
	TypeTheoryTheorem["machineResultOfCanonicalInRange",
		ForAll[{Typed[x, Integers], Typed[h, "integer64Range"[x]]}, "machineResultOfCanonical"[x] == Typed["left"["subtype"[x, h]], "Integer64" | Failure]],
		Function[{Typed[x, Integers], Typed[h, "integer64Range"[x]]}, InductiveRecursor[Decidable][
			Typed[d, Decidable["integer64Range"[x]]] |-> InductiveRecursor[Decidable][
				Typed[e, Decidable["integer64Range"[x]]] |-> "Integer64" | Failure,
				Typed[k, Not["integer64Range"[x]]] |-> Typed["right"[Failure["IntegerOverflow", <||>]], "Integer64" | Failure],
				Typed[k, "integer64Range"[x]] |-> Typed["left"["subtype"[x, k]], "Integer64" | Failure],
				d
			] == Typed["left"["subtype"[x, h]], "Integer64" | Failure],
			Typed[k, Not["integer64Range"[x]]] |-> "falseElimination"[k[h]],
			Typed[k, "integer64Range"[x]] |-> "equalityReflexivity"[Typed["left"["subtype"[x, h]], "Integer64" | Failure]],
			"machineDecision"["integer64Range"[x]]
		]]
	],
	(* the machine result of an integer: of the integer computed first, so that the value holds the class of one pair of
	   literals *)
	TypeTheoryDefinition["machineResult", Typed[Function[{Typed[x, Integers]}, "integerStrict"["machineResultOfCanonical", x]], Integers -> ("Integer64" | Failure)]],
	(* an exact result in range is the machine value, with no overflow: computing the integer first changes no value *)
	TypeTheoryTheorem["machineResultInRange",
		ForAll[{Typed[x, Integers], Typed[h, "integer64Range"[x]]}, "machineResult"[x] == Typed["left"["subtype"[x, h]], "Integer64" | Failure]],
		Function[{Typed[x, Integers], Typed[h, "integer64Range"[x]]},
			"equalityTransitivity"["integerStrictApply"["machineResultOfCanonical", x], "machineResultOfCanonicalInRange"[x, h]]
		]
	],
	(* the compiler's If of a Boolean test, the first value where it is true and the second where it is false *)
	TypeTheoryDefinition["machineIf", Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[b, "Boolean"], Typed[x, A], Typed[y, A]},
		InductiveRecursor[Booleans][Function[{Typed[c, Booleans]}, A], y, x, b]
	]],
	(* the machine quotient and remainder of the values of two machine integers, as the compiler's C computes them: by a 0
	   divisor the typed entry leaves, Failure["DivideByZero", <||>]; otherwise the quotient rounded down, which is out of
	   range only for -2^63 / -1, and the remainder, which is always in range *)
	TypeTheoryDefinition["machineQuotient", Typed[
		Function[{Typed[x, Integers], Typed[y, Integers]}, "machineIf"["integerEqual"[y, 0], Typed["right"[Failure["DivideByZero", <||>]], "Integer64" | Failure], "machineResult"[Quotient[x, y]]]],
		Integers -> Integers -> ("Integer64" | Failure)
	]],
	TypeTheoryDefinition["machineMod", Typed[
		Function[{Typed[x, Integers], Typed[y, Integers]}, "machineIf"["integerEqual"[y, 0], Typed["right"[Failure["DivideByZero", <||>]], "Integer64" | Failure], "machineResult"[Mod[x, y]]]],
		Integers -> Integers -> ("Integer64" | Failure)
	]],
	(* the machine's sum and product of two integers, the values of machine integers or literals: the machine result of
	   the exact one, so each leaves with Failure["IntegerOverflow", <||>] where the exact value is out of range *)
	TypeTheoryDefinition["machinePlus", Typed[Function[{Typed[x, Integers], Typed[y, Integers]}, "machineResult"[x + y]], Integers -> Integers -> ("Integer64" | Failure)]],
	TypeTheoryDefinition["machineTimes", Typed[Function[{Typed[x, Integers], Typed[y, Integers]}, "machineResult"[x y]], Integers -> Integers -> ("Integer64" | Failure)]],
	(* the natural numbers below 2^63 are machine integers: the relations of the pairs, stated as the integers' order
	   unfolds them, proved by terms that reduce no sum that holds the bound, only sums of literals, so that a kernel
	   that unfolds a literal one unit at a time checks them too: x + 0 == x of such a
	   sum is "additionZeroRight", not a computation *)
	TypeTheoryTheorem["integer64LowerRelation",
		ForAll[{Typed[m, NonNegativeIntegers]}, m + (upper + 0) == (0 + (m + upper)) + 0],
		Function[{Typed[m, NonNegativeIntegers]}, "equalityTransitivity"["equalitySymmetry"["additionZeroLeft"[m + upper]], "equalitySymmetry"["additionZeroRight"[0 + (m + upper)]]]]
	],
	TypeTheoryTheorem["integer64UpperRelation",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[upper == m + 1 + k, upper + (0 + 0 + 0) == ((m + 1) + k) + 0]],
		Function[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[e, upper == m + 1 + k]}, e]
	],
	machineTheorem["naturalInteger64Range",
		ForAll[{Typed[m, NonNegativeIntegers]}, Implies[m < upper, "integer64Range"["integerOfNatural"[m]]]],
		{
			"Introduce"[m, h], "Constructor",
			"Exact"["existsIntroduction"[m + upper, "quotientSoundness"["integer64LowerRelation"[m]]]],
			"Exact"[InductiveRecursor[Exists][
				Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, upper == m + 1 + k]] |-> "integerOfNatural"[m] < Typed[upper, Integers],
				{Typed[k, NonNegativeIntegers], Typed[e, upper == m + 1 + k]} |-> "existsIntroduction"[k, "quotientSoundness"["integer64UpperRelation"[m, k, e]]],
				"lessEqualWitness"[m + 1, upper, h]
			]]
		}
	],
	(* a natural number below 2^63 is its machine result, the first step of every bridge: the theorem a proof rewrites a
	   step of compiled code with, where the step's exact value is known to be in range *)
	TypeTheoryTheorem["machineResultOfNatural",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[h, m < upper]}, "machineResult"["integerOfNatural"[m]] == Typed["left"["subtype"["integerOfNatural"[m], "naturalInteger64Range"[m, h]]], "Integer64" | Failure]],
		Function[{Typed[m, NonNegativeIntegers], Typed[h, m < upper]}, "machineResultInRange"["integerOfNatural"[m], "naturalInteger64Range"[m, h]]]
	],
	(* the machine's n - 1 of a positive natural number is the natural number before it: the value a recursion calls
	   itself with is the class of (k + 1, 1), which is the integer k, though not by computation *)
	machineTheorem["integerOfNaturalPredecessor",
		ForAll[{Typed[n, NonNegativeIntegers]}, "integerOfNatural"[n + 1] - 1 == "integerOfNatural"[n]],
		{"Introduce"[n], "Rewrite"["integerOfNaturalAddition"[n, 1]], "Ring"}
	]
}]
