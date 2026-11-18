(* ::Package:: *)

(* Tests for Elaboration/CompiledDefinitions.wl: a function formalized in an environment of the machine integers means
   what the compiler's typed entry computes, from the compiler's own typed code: each step a machine result, which leaves
   with Failure["IntegerOverflow", <||>] where the C does.
   Run with: TestReport["TypeTheory/Tests/Elaboration/CompiledDefinitions.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

machine = TypeTheoryEnvironment["Machine"]

compiledProduct[n_Integer] := n (n + 1)
compiledAbsolute[n_Integer] := If[n > 0, n, -n]
compiledNext[n_Integer] := compiledAbsolute[n] + 1
compiledSum[a_Integer, b_Integer, c_Integer] := a + b + c
compiledSign[n_Integer] := If[n < 0, -1, If[n == 0, 0, 1]]
compiledSmallQ[n_Integer] := n < 10
compiledUntyped[x_] := x
compiledEvenQ[n_Integer] := If[n == 0, True, compiledOddQ[n - 1]]
compiledOddQ[n_Integer] := If[n == 0, False, compiledEvenQ[n - 1]]
compiledTriangle[n_Integer] := If[n == 0, 0, n + compiledTriangle[n - 1]]
compiledDoubleTriangle[n_Integer] := 2 compiledTriangle[n]
compiledWhileSum[n_Integer] := Module[{s = 0, i = 1}, While[i <= n, s = s + i; i = i + 1]; s]
compiledTestSets[n_Integer] := Module[{s = 0, i = 0}, While[(i = i + 1) <= n, s = s + i]; s]
compiledNested[n_Integer] := Module[{s = 0, i = 1, j = 1}, While[i <= n, j = 1; While[j <= i, s = s + 1; j = j + 1]; i = i + 1]; s]
compiledTwiceSum[n_Integer] := compiledWhileSum[n] + compiledWhileSum[n]
compiledDoSum[n_Integer] := Module[{s = 0}, Do[s += i, {i, n}]; s]
compiledCollatz[n_Integer] := Module[{k = n, c = 0}, While[k != 1, If[Mod[k, 2] == 0, k = Quotient[k, 2], k = 3 k + 1]; c = c + 1]; c]
mathematicalTriangle[0] = 0
mathematicalTriangle[n_Integer] := n + mathematicalTriangle[n - 1]
compiledClosedForm[n_Integer] := Quotient[n (n + 1), 2]
compiledQuotient[a_Integer, b_Integer] := Quotient[a, b]
compiledMod[a_Integer, b_Integer] := Mod[a, b]
compiledFifth[n_Integer] := compiledQuotient[n, 5] + 1

compiledEnvironment = TypeTheoryEnvironment[machine, Catenate[{
	TypeTheoryFormalize[compiledProduct, machine],
	TypeTheoryFormalize[compiledNext, machine],
	TypeTheoryFormalize[compiledSum, machine],
	TypeTheoryFormalize[compiledSign, machine],
	TypeTheoryFormalize[compiledSmallQ, machine],
	TypeTheoryFormalize[compiledClosedForm, machine],
	TypeTheoryFormalize[compiledMod, machine],
	TypeTheoryFormalize[compiledFifth, machine]
}]]


VerificationTest[
	TypeTheoryFormalize[compiledProduct, machine],
	{TypeTheoryDefinition[compiledProduct, Typed[
		Function[{Typed[n, "Integer64"]}, "confirmBind"["machinePlus"[n[["integer"]], 1], Function[{Typed[WolframInstitute`TypeTheory`Compiled`t3, "Integer64"]}, "machineTimes"[n[["integer"]], WolframInstitute`TypeTheory`Compiled`t3[["integer"]]]]]],
		"Integer64" -> ("Integer64" | Failure)
	]]},
	TestID -> "A-compiled-function-is-its-typed-code-step-by-step"
]

(* the edges of n (n + 1) in the machine integers, which Wolfram 15's FunctionCompile declines at too *)
VerificationTest[
	Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[n, Integers]], compiledProduct], compiledEnvironment]]]], {3, 3037000499, 3037000500, -3037000500, -3037000501}],
	{12, 9223372033963249500, Failure["IntegerOverflow", <||>], 9223372033963249500, Failure["IntegerOverflow", <||>]},
	TestID -> "The-compiled-product-leaves-where-the-machine-overflows"
]

(* -n is -1 n, which overflows at -2^63; a call of another compiled function declares it first and continues with its
   result *)
VerificationTest[
	{
		Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[n, Integers]], compiledAbsolute], compiledEnvironment]]]], {-5, 7, -9223372036854775808}],
		Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[n, Integers]], compiledNext], compiledEnvironment]]]], {-5, 9223372036854775807}],
		Map[Function[declaration, HoldForm @@ Take[declaration, 1]], TypeTheoryFormalize[compiledNext, machine]]
	},
	{{5, 7, Failure["IntegerOverflow", <||>]}, {6, Failure["IntegerOverflow", <||>]}, {HoldForm[compiledAbsolute], HoldForm[compiledNext]}},
	TestID -> "Negation-and-calls-of-compiled-functions"
]

(* a + b + c is two steps, as the C combines them: 2^62 + 2^62 - 2^62 leaves, though the exact sum is in range *)
VerificationTest[
	Map[
		Apply[Function[{x, y, z}, TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			"confirmBind"["machineResult"[Typed[x, Integers]], Typed[a, "Integer64"] |-> "confirmBind"["machineResult"[Typed[y, Integers]], Typed[b, "Integer64"] |-> "confirmBind"["machineResult"[Typed[z, Integers]], Typed[c, "Integer64"] |-> compiledSum[a, b, c]]]],
			compiledEnvironment
		]]]]],
		{{1, 2, 3}, {4611686018427387904, 4611686018427387904, -4611686018427387904}, {-4611686018427387904, 4611686018427387904, 4611686018427387904}}
	],
	{6, Failure["IntegerOverflow", <||>], 4611686018427387904},
	TestID -> "A-sum-of-three-is-two-machine-steps"
]

(* comparisons are Booleans that never leave; If takes the branch of its test, and a Boolean function's value is a
   Boolean or its leave *)
VerificationTest[
	{
		Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[n, Integers]], compiledSign], compiledEnvironment]]]], {-7, 0, 9}],
		Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[n, Integers]], compiledSmallQ], compiledEnvironment]]]], {3, 10}],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm[compiledSmallQ, compiledEnvironment]], TypeTheoryTerm["Integer64" -> ("Boolean" | Failure), compiledEnvironment]]
	},
	{{-1, 0, 1}, {True, False}, True},
	TestID -> "Comparisons-and-If-in-compiled-code"
]

(* what the machine model does not have yet is a Failure, not a meaning *)
VerificationTest[
	{
		TypeTheoryFormalize[compiledUntyped, machine]["Tag"],
		TypeTheoryFormalize[compiledProduct, TypeTheoryEnvironment["Integers"], "Meaning" -> "Compiled"]["Tag"]
	},
	{"NoTypedEntry", "NoMachineIntegers"},
	TestID -> "Untyped-code-and-a-missing-machine-are-failures"
]

(* in the machine environment, "Meaning" -> "Function" is still the mathematical function *)
VerificationTest[
	TypeTheoryFormalize[compiledProduct, machine, "Meaning" -> "Function"],
	{TypeTheoryDefinition[compiledProduct, Function[{Typed[n, Integers]}, n (n + 1)]]},
	TestID -> "The-mathematical-meaning-in-the-machine-environment"
]

(* Quotient and Mod leave by 0, as the C's b == 0, and the quotient also at -2^63 / -1, the C's INT64_MIN with -1, the one
   quotient out of range; otherwise they round down as the integers' *)
VerificationTest[
	{
		Apply[Function[{x, y}, TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			"confirmBind"["machineResult"[Typed[x, Integers]], Typed[a, "Integer64"] |-> "confirmBind"["machineResult"[Typed[y, Integers]], Typed[b, "Integer64"] |-> compiledQuotient[a, b]]],
			compiledEnvironment
		]]]], {{7, -2}, {-7, 2}, {7, 0}, {-9223372036854775808, -1}, {-9223372036854775808, 1}}, {1}],
		Apply[Function[{x, y}, TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			"confirmBind"["machineResult"[Typed[x, Integers]], Typed[a, "Integer64"] |-> "confirmBind"["machineResult"[Typed[y, Integers]], Typed[b, "Integer64"] |-> compiledMod[a, b]]],
			compiledEnvironment
		]]]], {{7, -2}, {-7, 2}, {7, 0}, {-9223372036854775808, -1}}, {1}]
	},
	{
		{-4, -4, Failure["DivideByZero", <||>], Failure["IntegerOverflow", <||>], -9223372036854775808},
		{-1, 1, Failure["DivideByZero", <||>], 0}
	},
	TestID -> "Machine-Quotient-and-Mod-leave-where-the-C-does"
]

(* the closed form of the tutorial, Quotient[n (n + 1), 2]: its typed code leaves only where the product overflows, and a
   constant argument of a call is bound as a machine integer first *)
VerificationTest[
	{
		Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[n, Integers]], compiledClosedForm], compiledEnvironment]]]], {4, 3037000499, 3037000500, -3037000500}],
		Map[Function[n, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[n, Integers]], compiledFifth], compiledEnvironment]]]], {-11, 24}]
	},
	{{10, 4611686016981624750, Failure["IntegerOverflow", <||>], 4611686016981624750}, {-2, 5}},
	TestID -> "The-compiled-closed-form-and-a-constant-argument"
]

(* the bridge: for n <= 3037000499 the closed form's typed code never declines, and its value is the mathematical
   Quotient[n (n + 1), 2]. Each step of the typed code is shown in range, the sum, the product and the quotient, and the
   kernel computes the code between the steps; the proof rests on the integers' quotient axiom alone *)
VerificationTest[
	Module[{bounds, proof},
		bounds = TypeTheoryEnvironment[compiledEnvironment, {
			TypeTheoryTheorem["argumentBound", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 3037000499, n < 9223372036854775808]], compiledEnvironment, {"Introduce"[n, h], "LinearArithmetic"}]],
			TypeTheoryTheorem["successorBound", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 3037000499, n + 1 < 9223372036854775808]], compiledEnvironment, {"Introduce"[n, h], "LinearArithmetic"}]],
			TypeTheoryTheorem["pronicBound", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 3037000499, n (n + 1) < 9223372036854775808]], compiledEnvironment, {"Introduce"[n, h], "NonlinearArithmetic"}]]
		}];
		bounds = TypeTheoryEnvironment[bounds, {TypeTheoryTheorem["quotientBound",
			ForAll[{Typed[n, NonNegativeIntegers], Typed[h, n <= 3037000499]}, Quotient[n (n + 1), 2] < 9223372036854775808],
			Function[{Typed[n, NonNegativeIntegers], Typed[h, n <= 3037000499]}, "lessEqualTransitivity"["lessEqualSuccessor"["quotientLessEqual"[n (n + 1), 2]], "pronicBound"[n, h]]]
		]}];
		proof = TypeTheoryProof[
			ForAll[{Typed[n, NonNegativeIntegers], Typed[h, n <= 3037000499]},
				"confirmBind"["machineResult"["integerOfNatural"[n]], compiledClosedForm] ==
					Typed["left"["subtype"["integerOfNatural"[Quotient[n (n + 1), 2]], "naturalInteger64Range"[Quotient[n (n + 1), 2], "quotientBound"[n, h]]]], "Integer64" | Failure]
			],
			bounds,
			{"Introduce"[n, h], "Exact"[
				"equalityTransitivity"[
					"equalityCongruence"[Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, compiledClosedForm]], "machineResultOfNatural"[n, "argumentBound"[n, h]]],
					"equalityTransitivity"[
						"equalityCongruence"[
							Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t3, "Integer64"]}, "confirmBind"["machineTimes"["integerOfNatural"[n], t3["integer"]], Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4["integer"], 2]]]]]],
							"machineResultInRange"["integerOfNatural"[n] + 1, "naturalInteger64Range"[n + 1, "successorBound"[n, h]]]
						],
						"equalityTransitivity"[
							"equalityCongruence"[
								Function[{Typed[x, Integers]}, "confirmBind"["machineResult"[x], Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4["integer"], 2]]]],
								"equalitySymmetry"["integerOfNaturalMultiplication"[n, n + 1]]
							],
							"equalityTransitivity"[
								"equalityCongruence"[
									Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4["integer"], 2]]]],
									"machineResultOfNatural"[n (n + 1), "pronicBound"[n, h]]
								],
								"equalityTransitivity"[
									"equalityCongruence"[Function[{Typed[x, Integers]}, "machineResult"[x]], "integerQuotientOfNatural"[n (n + 1), 1]],
									"machineResultOfNatural"[Quotient[n (n + 1), 2], "quotientBound"[n, h]]
								]
							]
						]
					]
				]
			]}
		];
		{FailureQ[proof], TypeTheoryAxiomClosure[proof]}
	],
	{False, <|"quotientSoundness" -> "Proposition"|>},
	TestID -> "The-closed-forms-typed-code-never-declines-below-3037000500"
]

(* a function that calls itself takes first the levels left: each call of itself is one, and with none left it leaves, as
   a typed entry leaves where its recursion is deeper than its bound; a function that calls it passes the levels on.
   A machine integer's projection is its value at once in beta reduction, so a depth of 20 takes no longer than one *)
VerificationTest[
	With[{environment = TypeTheoryEnvironment[machine, TypeTheoryFormalize[compiledDoubleTriangle, machine]]},
		{
			Map[
				Apply[Function[{function, levels, k}, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], Typed[m, "Integer64"] |-> function[levels, m]], environment]]]]],
				{{compiledTriangle, 4, 3}, {compiledTriangle, 3, 3}, {compiledTriangle, 0, 0}, {compiledTriangle, 1, 0}, {compiledDoubleTriangle, 3, 2}, {compiledTriangle, 21, 20}, {compiledTriangle, 20, 20}}
			],
			DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm[compiledTriangle, environment]], TypeTheoryTerm[NonNegativeIntegers -> "Integer64" -> ("Integer64" | Failure), environment]]
		}
	],
	{{6, Failure["RecursionLimit", <||>], Failure["RecursionLimit", <||>], 0, 6, 210, Failure["RecursionLimit", <||>]}, True},
	TestID -> "Recursion-counts-the-levels-left-and-leaves-without-them"
]

(* the bridge for a recursion: with levels enough, more than n, and wherever the exact result fits a machine integer,
   the compiled triangle of a machine integer whose value is n is the machine integer of the mathematical triangle, a
   recursion on the natural numbers. By induction on n and cases on the levels: none is absurd; at 0 the test is true; at
   k + 1 the test is false, k is a machine integer, the recursion is the induction hypothesis at it, and the sum is the
   next triangle. The argument is any machine integer equal to n as an integer, since the recursion's own argument, the
   class of (k + 1, 1), is k only so *)
VerificationTest[
	Module[{environment, proof},
		environment = TypeTheoryEnvironment[machine, Join[
			TypeTheoryFormalize[mathematicalTriangle, machine, "Meaning" -> "Function", "Type" -> (NonNegativeIntegers -> NonNegativeIntegers)],
			TypeTheoryFormalize[compiledTriangle, machine]
		]];
		environment = TypeTheoryEnvironment[environment, {
			TypeTheoryTheorem["notLessZero", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n < 0, False]], environment, {"Introduce"[n, h], "LinearArithmetic"}]],
			TypeTheoryTheorem["lessOfSuccessors", TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[l, NonNegativeIntegers]}, Implies[n + 1 < l + 1, n < l]], environment, {"Introduce"[n, l, h], "LinearArithmetic"}]],
			TypeTheoryTheorem["partBound", TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[(a + 1) + t < u, t < u]], environment, {"Introduce"[a, t, u, h], "LinearArithmetic"}]],
			TypeTheoryTheorem["argumentBound", TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[(a + 1) + t < u, a < u]], environment, {"Introduce"[a, t, u, h], "LinearArithmetic"}]]
		}];
		proof = TypeTheoryProof[
			ForAll[{Typed[n, NonNegativeIntegers], Typed[levels, NonNegativeIntegers], Typed[m, "Integer64"]},
				Implies[n < levels, Implies[mathematicalTriangle[n] < 9223372036854775808, Implies[m["integer"] == "integerOfNatural"[n],
					Exists[{Typed[v, "Integer64"]}, compiledTriangle[levels, m] == Typed["left"[v], "Integer64" | Failure] && v["integer"] == "integerOfNatural"[mathematicalTriangle[n]]]]]]],
			environment,
			{
				"Introduce"[n], "Induction"[n], "Introduce"[levels], "Induction"[levels],
				"Introduce"[m, h], "Exact"["falseElimination"["notLessZero"[0, h]]],
				"Introduce"[l, ihl, m, h, b, e],
				"Exact"["existsIntroduction"[
					"subtype"["integerOfNatural"[mathematicalTriangle[0]], "naturalInteger64Range"[mathematicalTriangle[0], b]],
					"andIntroduction"[
						"equalityTransitivity"[
							"equalityCongruence"[
								Function[{Typed[x, Integers]}, "machineIf"["integerEqual"[x, 0], "machineResult"[0], "confirmBind"["machinePlus"[x, -1], Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"[x, t10["integer"]]]]]]]],
								e
							],
							"machineResultOfNatural"[mathematicalTriangle[0], b]
						],
						"equalityReflexivity"["integerOfNatural"[mathematicalTriangle[0]]]
					]
				]],
				"Introduce"[k, ih, levels], "Induction"[levels],
				"Introduce"[m, h], "Exact"["falseElimination"["notLessZero"[k + 1, h]]],
				"Introduce"[l, ihl, m, h, b, e],
				"Exact"[InductiveRecursor[Exists][
					Function[{w0}, Exists[{Typed[w, "Integer64"]}, compiledTriangle[l + 1, m] == Typed["left"[w], "Integer64" | Failure] && w["integer"] == "integerOfNatural"[mathematicalTriangle[k + 1]]]],
					Function[
						{
							Typed[v, "Integer64"],
							Typed[hv, compiledTriangle[l, "subtype"["integerOfNatural"[k], "naturalInteger64Range"[k, "argumentBound"[k, mathematicalTriangle[k], 9223372036854775808, b]]]] == Typed["left"[v], "Integer64" | Failure] && v["integer"] == "integerOfNatural"[mathematicalTriangle[k]]]
						},
						"existsIntroduction"[
							"subtype"["integerOfNatural"[mathematicalTriangle[k + 1]], "naturalInteger64Range"[mathematicalTriangle[k + 1], b]],
							"andIntroduction"[
								"equalityTransitivity"[
									"equalityCongruence"[
										Function[{Typed[x, Integers]}, "machineIf"["integerEqual"[x, 0], "machineResult"[0], "confirmBind"["machinePlus"[x, -1], Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"[x, t10["integer"]]]]]]]],
										e
									],
									"equalityTransitivity"[
										"equalityCongruence"[
											Function[{Typed[x, Integers]}, "confirmBind"["machineResult"[x], Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"["integerOfNatural"[k + 1], t10["integer"]]]]]]],
											"integerOfNaturalPredecessor"[k]
										],
										"equalityTransitivity"[
											"equalityCongruence"[
												Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machinePlus"["integerOfNatural"[k + 1], t10["integer"]]]]]]],
												"machineResultOfNatural"[k, "argumentBound"[k, mathematicalTriangle[k], 9223372036854775808, b]]
											],
											"equalityTransitivity"[
												"equalityCongruence"[
													Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t10, "Integer64"]}, "machinePlus"["integerOfNatural"[k + 1], t10["integer"]]]]],
													"andEliminationLeft"[hv]
												],
												"equalityTransitivity"[
													"equalityCongruence"[Function[{Typed[y, Integers]}, "machinePlus"["integerOfNatural"[k + 1], y]], "andEliminationRight"[hv]],
													"equalityTransitivity"[
														"equalityCongruence"[Function[{Typed[y, Integers]}, "machineResult"[y]], "equalitySymmetry"["integerOfNaturalAddition"[k + 1, mathematicalTriangle[k]]]],
														"machineResultOfNatural"[mathematicalTriangle[k + 1], b]
													]
												]
											]
										]
									]
								],
								"equalityReflexivity"["integerOfNatural"[mathematicalTriangle[k + 1]]]
							]
						]
					],
					ih[
						l,
						"subtype"["integerOfNatural"[k], "naturalInteger64Range"[k, "argumentBound"[k, mathematicalTriangle[k], 9223372036854775808, b]]],
						"lessOfSuccessors"[k, l, h],
						"partBound"[k, mathematicalTriangle[k], 9223372036854775808, b],
						"equalityReflexivity"["integerOfNatural"[k]]
					]
				]]
			}
		];
		{FailureQ[proof], TypeTheoryAxiomClosure[proof]}
	],
	{False, <|"quotientSoundness" -> "Proposition"|>},
	TestID -> "A-compiled-recursion-computes-the-mathematical-recursion"
]

(* a While is a constant of its own, "While[f]", by recursion on the fuel, the iterations it may take: its arguments are
   the fuel, the locals it reads and the locals it sets, and its value the pair of those it sets. The function takes the
   fuel first and goes on with the loop's value. A sum to n takes n rounds and a last test: with fuel n + 1 it is the sum,
   and with n it is out of fuel, Failure["OutOfFuel", <||>], which is no leave of the typed code *)
VerificationTest[
	With[{declarations = TypeTheoryFormalize[compiledWhileSum, machine]},
		With[{environment = TypeTheoryEnvironment[machine, declarations]},
			{
				Map[Function[declaration, HoldForm @@ Take[declaration, 1]], declarations],
				DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["While[compiledWhileSum]", environment]], TypeTheoryTerm[NonNegativeIntegers -> "Integer64" -> "Integer64" -> "Integer64" -> (CartesianProductType["Integer64", "Integer64"] | Failure), environment]],
				DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm[compiledWhileSum, environment]], TypeTheoryTerm[NonNegativeIntegers -> "Integer64" -> ("Integer64" | Failure), environment]],
				Map[
					Apply[Function[{fuel, k}, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], Typed[m, "Integer64"] |-> compiledWhileSum[fuel, m]], environment]]]]],
					{{4, 3}, {3, 3}, {1, 0}, {0, 0}, {30, 20}}
				]
			}
		]
	],
	{{HoldForm["While[compiledWhileSum]"], HoldForm[compiledWhileSum]}, True, True, {6, Failure["OutOfFuel", <||>], 0, Failure["OutOfFuel", <||>], 210}},
	TestID -> "A-While-is-a-constant-of-its-own-by-recursion-on-the-fuel"
]

(* a local that the test sets is of the loop's state too; a loop in a loop is a constant of its own, declared first; and a
   function that calls one with a loop takes the fuel and passes it on *)
VerificationTest[
	With[{environment = TypeTheoryEnvironment[machine, Join[TypeTheoryFormalize[compiledTestSets, machine], TypeTheoryFormalize[compiledNested, machine], TypeTheoryFormalize[compiledTwiceSum, machine]]]},
		{
			Map[Function[declaration, HoldForm @@ Take[declaration, 1]], TypeTheoryFormalize[compiledNested, machine]],
			Map[Function[declaration, HoldForm @@ Take[declaration, 1]], TypeTheoryFormalize[compiledTwiceSum, machine]],
			Map[
				Apply[Function[{function, fuel, k}, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], Typed[m, "Integer64"] |-> function[fuel, m]], environment]]]]],
				{{compiledTestSets, 50, 5}, {compiledTestSets, 5, 5}, {compiledNested, 50, 5}, {compiledNested, 5, 5}, {compiledTwiceSum, 50, 5}, {compiledTwiceSum, 5, 5}}
			]
		}
	],
	{
		{HoldForm["While[compiledNested, 2]"], HoldForm["While[compiledNested]"], HoldForm[compiledNested]},
		{HoldForm["While[compiledWhileSum]"], HoldForm[compiledWhileSum], HoldForm[compiledTwiceSum]},
		{15, Failure["OutOfFuel", <||>], 15, Failure["OutOfFuel", <||>], 30, Failure["OutOfFuel", <||>]}
	},
	TestID -> "A-loops-state-nested-loops-and-fuel-passed-on"
]

(* A Do with an iterator. The code keeps the counter in a local and the iterator's symbol, a global it localizes, in step
   with it; the meaning reads the symbol as a local that each round sets from the counter, so the Do is the While the
   compiler wrote, of the end, the step, and the locals it sets with the counter last. A sum to n takes n rounds and a
   last test, and a bound below the start takes none. *)
VerificationTest[
	With[{declarations = TypeTheoryFormalize[compiledDoSum, machine]},
		With[{environment = TypeTheoryEnvironment[machine, declarations]},
			{
				Map[Function[declaration, HoldForm @@ Take[declaration, 1]], declarations],
				DefinitionallyEqualQ[
					TypeTheoryType[TypeTheoryTerm["While[compiledDoSum]", environment]],
					TypeTheoryTerm[NonNegativeIntegers -> "Integer64" -> "Integer64" -> "Integer64" -> "Integer64" -> (CartesianProductType["Integer64", "Integer64"] | Failure), environment]
				],
				Map[
					Apply[Function[{fuel, k}, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], Typed[m, "Integer64"] |-> compiledDoSum[fuel, m]], environment]]]]],
					{{50, 0}, {50, 5}, {6, 5}, {5, 5}, {50, 20}, {50, -3}}
				]
			}
		]
	],
	{
		{HoldForm["While[compiledDoSum]"], HoldForm[compiledDoSum]},
		True,
		{compiledDoSum[0], compiledDoSum[5], compiledDoSum[5], Failure["OutOfFuel", <||>], compiledDoSum[20], compiledDoSum[-3]}
	},
	TestID -> "A-Do-is-the-While-of-its-counter-with-the-iterator-a-local"
]

(* A range with a start and a step, two Dos in turn over one iterator, and a Do in a Do, whose loop takes the iterator of
   the one around it as an argument. Each agrees with the Wolfram Language where the typed code does not leave. The
   counter's step is the machine's sum: a range that ends at the largest machine integer leaves after its last round,
   and a body that overflows midway leaves there. Compiled code on the kernel declines at both with IntegerOverflow,
   gives the Wolfram Language's value by its generic code, and leaves the iterator's symbol as it was before the call.
   Refused is a body that sets its iterator. *)
iteratorRange[n_Integer] := Module[{s = 0}, Do[s = s + i i, {i, 2, n, 3}]; s]
iteratorEdge[a_Integer, b_Integer] := Module[{s = 0}, Do[s = i, {i, a, b}]; s]
iteratorTwice[n_Integer] := Module[{s = 0}, Do[s = s + i, {i, n}]; Do[s = s + 2 i, {i, n}]; s]
iteratorNested[n_Integer] := Module[{s = 0}, Do[Do[s = s + i j, {j, i}], {i, n}]; s]
iteratorOverflows[n_Integer] := Module[{s = 1}, Do[s = s 1000000 i, {i, n}]; s]
iteratorSet[n_Integer] := Module[{s = 0}, Do[i = i + 1; s = s + i, {i, n}]; s]

VerificationTest[
	Module[{environment, model, model2},
		environment = TypeTheoryEnvironment[machine, Join[
			TypeTheoryFormalize[iteratorRange, machine], TypeTheoryFormalize[iteratorEdge, machine], TypeTheoryFormalize[iteratorTwice, machine],
			TypeTheoryFormalize[iteratorNested, machine], TypeTheoryFormalize[iteratorOverflows, machine]
		]];
		model[f_, fuel_, k_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], f[fuel]], environment]]];
		model2[f_, fuel_, a_, b_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			"confirmBind"["machineResult"[Typed[a, Integers]], Typed[x, "Integer64"] |-> "confirmBind"["machineResult"[Typed[b, Integers]], f[fuel, x]]],
			environment
		]]];
		{
			Head[environment],
			Map[Function[k, model[iteratorRange, 50, k] === iteratorRange[k]], {-4, 1, 2, 4, 5, 11, 12}],
			Map[Apply[Function[{a, b}, model2[iteratorEdge, 50, a, b] === iteratorEdge[a, b]]], {{3, 5}, {5, 3}, {-2, 2}, {9223372036854775804, 9223372036854775806}}],
			(* the end and the step add up past 2^63 - 1 *)
			{model2[iteratorEdge, 50, 9223372036854775805, 9223372036854775807], iteratorEdge[9223372036854775805, 9223372036854775807]},
			Map[Function[k, model[iteratorTwice, 50, k] === iteratorTwice[k]], {0, 1, 4, 9}],
			Map[Function[declaration, HoldForm @@ Take[declaration, 1]], TypeTheoryFormalize[iteratorNested, machine]],
			Map[Function[k, model[iteratorNested, 50, k] === iteratorNested[k]], {0, 1, 4, 6}],
			model[iteratorNested, 4, 4],
			(* the fourth round's product is past 2^63 - 1 *)
			{model[iteratorOverflows, 50, 3] === iteratorOverflows[3], model[iteratorOverflows, 50, 6], iteratorOverflows[6]},
			Replace[TypeTheoryFormalize[iteratorSet, machine], failure_Failure :> {failure["Tag"], StringContainsQ[ToString[failure["MessageParameters"]], "a Do whose body sets its iterator"]}]
		}
	],
	{
		TypeTheoryEnvironment,
		ConstantArray[True, 7],
		ConstantArray[True, 4],
		{Failure["IntegerOverflow", <||>], 9223372036854775807},
		ConstantArray[True, 4],
		{HoldForm["While[iteratorNested, 2]"], HoldForm["While[iteratorNested]"], HoldForm[iteratorNested]},
		ConstantArray[True, 4],
		Failure["OutOfFuel", <||>],
		{True, Failure["IntegerOverflow", <||>], 720000000000000000000000000000000000000},
		{"UnmodeledOperation", True}
	},
	TestID -> "Ranges-nested-Dos-and-where-a-Do-leaves"
]

(* A loop that calls its function. A loop is a constant declared before its function, so it takes the function's
   recursion as an argument, after the fuel: the function at the level below, of the function's own type. Four shapes: a
   While and a Do whose bodies call the function, a loop in a loop that does, and a While whose test does. Each agrees
   with the Wolfram Language given levels and fuel enough, leaves with Failure["RecursionLimit", <||>] with a level too
   few, and is out of fuel with a round too few. The functions call themselves 2^n times, which the model computes
   within the time the test gives it: a machine value holds its integer computed, not the sum it came from. *)
selfLoop[n_Integer] := Module[{s = 0, i = 1}, While[i < n, s = s + selfLoop[i]; i = i + 1]; s + 1]
selfDo[n_Integer] := Module[{s = 1}, Do[s = s + selfDo[i - 1], {i, n}]; s]
selfNested[n_Integer] := Module[{s = 1, i = 1, j = 1}, While[i <= n, j = 1; While[j < i, s = s + selfNested[j - 1]; j = j + 1]; i = i + 1]; s]
selfTested[n_Integer] := Module[{k = n, c = 0}, While[k > 0 && selfTested[k - 1] >= 0, c = c + 1; k = k - 1]; c]

VerificationTest[
	Module[{environment, model},
		environment = TypeTheoryEnvironment[machine, Join[
			TypeTheoryFormalize[selfLoop, machine], TypeTheoryFormalize[selfDo, machine], TypeTheoryFormalize[selfNested, machine], TypeTheoryFormalize[selfTested, machine]
		]];
		model[f_, levels_, fuel_, k_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], f[levels, fuel]], environment]]];
		{
			Head[environment],
			Map[Function[declaration, HoldForm @@ Take[declaration, 1]], TypeTheoryFormalize[selfNested, machine]],
			DefinitionallyEqualQ[
				TypeTheoryType[TypeTheoryTerm["While[selfLoop]", environment]],
				TypeTheoryTerm[
					NonNegativeIntegers -> NonNegativeIntegers -> ("Integer64" -> ("Integer64" | Failure)) -> "Integer64" -> "Integer64" -> "Integer64" -> (CartesianProductType["Integer64", "Integer64"] | Failure),
					environment
				]
			],
			Map[Function[k, model[selfLoop, 20, 20, k] === selfLoop[k]], {-1, 0, 1, 2, 5, 9}],
			Map[Function[k, model[selfDo, 20, 20, k] === selfDo[k]], {-1, 0, 1, 4, 8}],
			Map[Function[k, model[selfNested, 20, 20, k] === selfNested[k]], {0, 1, 4, 5, 7}],
			Map[Function[k, model[selfTested, 20, 20, k] === selfTested[k]], {-2, 0, 1, 4, 7}],
			(* selfLoop at 5 calls itself to a depth of 5, and its loop takes 4 rounds and a last test *)
			{model[selfLoop, 5, 5, 5], model[selfLoop, 4, 5, 5], model[selfLoop, 5, 4, 5]},
			(* selfDo at 4 calls itself down to 0, and its Do takes 4 rounds and a last test *)
			{model[selfDo, 5, 5, 4], model[selfDo, 4, 5, 4], model[selfDo, 5, 4, 4]},
			{model[selfTested, 5, 5, 4], model[selfTested, 4, 5, 4], model[selfTested, 5, 4, 4]},
			(* without a round no call is made, but the function is a level itself *)
			{model[selfLoop, 1, 1, 1], model[selfLoop, 0, 1, 1], model[selfLoop, 1, 0, 1]}
		}
	],
	{
		TypeTheoryEnvironment,
		{HoldForm["While[selfNested, 2]"], HoldForm["While[selfNested]"], HoldForm[selfNested]},
		True,
		ConstantArray[True, 6], ConstantArray[True, 5], ConstantArray[True, 5], ConstantArray[True, 5],
		{selfLoop[5], Failure["RecursionLimit", <||>], Failure["OutOfFuel", <||>]},
		{selfDo[4], Failure["RecursionLimit", <||>], Failure["OutOfFuel", <||>]},
		{selfTested[4], Failure["RecursionLimit", <||>], Failure["OutOfFuel", <||>]},
		{1, Failure["RecursionLimit", <||>], Failure["OutOfFuel", <||>]}
	},
	TimeConstraint -> 120,
	TestID -> "A-loop-that-calls-its-function-takes-the-functions-recursion"
]

(* a machine value holds its integer as the class of one pair of literals, whatever computed it: the head normal form of
   a loop's sum is the same size after 2 rounds and after 16 *)
VerificationTest[
	With[{environment = TypeTheoryEnvironment[machine, TypeTheoryFormalize[compiledWhileSum, machine]]},
		{
			Map[
				Apply[Function[{fuel, k}, LeafCount[WeakHeadNormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], Typed[m, "Integer64"] |-> compiledWhileSum[fuel, m]], environment]]]]],
				{{3, 2}, {5, 4}, {9, 8}, {17, 16}}
			],
			MatchQ[
				WeakHeadNormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[4, Integers]], Typed[m, "Integer64"] |-> compiledWhileSum[5, m]], environment]],
				TypeTheoryTerm[Typed["left"["subtype"["integerOfPair"["pair"[10, 0]], _]], _], _]
			]
		}
	],
	{{52, 52, 52, 52}, True},
	TestID -> "A-machine-value-holds-one-pair-of-literals-whatever-computed-it"
]

(* Functions that call each other are one recursion on the levels: the constant "Recursion[f, g]" is the functions
   together, a tuple in the order of their names, each function its part, and every call of one of them a level. Three
   groups: two tests of parity; three functions in a ring that call one outside it, called from outside; and two of
   which one calls the other in a loop, whose While takes the tuple at the level below. Each agrees with the Wolfram
   Language given levels and fuel enough, leaves with Failure["RecursionLimit", <||>] with a level too few, and is
   out of fuel with a round too few. Compiled code on the kernel counts the levels the same way: recursion of one
   function and of two that call each other both decline first at the argument 4096. *)
groupA[n_Integer] := If[n <= 0, 0, 1 + groupB[n - 1]]
groupB[n_Integer] := If[n <= 0, 0, 2 + groupC[n - 1]]
groupC[n_Integer] := If[n <= 0, 0, 3 + groupA[n - 1] + groupOutside[n]]
groupOutside[n_Integer] := n + 1
groupCaller[n_Integer] := groupA[n] + 1
groupLoop[n_Integer] := Module[{s = 0, i = 0}, While[i < n, s = s + groupStep[i]; i = i + 1]; s + 1]
groupStep[n_Integer] := If[n == 0, 1, groupLoop[n - 1] + 1]

VerificationTest[
	Module[{environment, leveled, fueled},
		environment = TypeTheoryEnvironment[machine, Join[TypeTheoryFormalize[compiledEvenQ, machine], TypeTheoryFormalize[groupCaller, machine], TypeTheoryFormalize[groupLoop, machine]]];
		leveled[f_, levels_, k_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], f[levels]], environment]]];
		fueled[f_, levels_, fuel_, k_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], f[levels, fuel]], environment]]];
		{
			Head[environment],
			Map[
				Function[declarations, Map[Function[declaration, HoldForm @@ Take[declaration, 1]], declarations]],
				{TypeTheoryFormalize[compiledOddQ, machine], TypeTheoryFormalize[groupCaller, machine], TypeTheoryFormalize[groupStep, machine]}
			],
			DefinitionallyEqualQ[
				TypeTheoryType[TypeTheoryTerm["Recursion[compiledEvenQ, compiledOddQ]", environment]],
				TypeTheoryTerm[NonNegativeIntegers -> CartesianProductType["Integer64" -> ("Boolean" | Failure), "Integer64" -> ("Boolean" | Failure)], environment]
			],
			DefinitionallyEqualQ[
				TypeTheoryType[TypeTheoryTerm["While[groupLoop]", environment]],
				TypeTheoryTerm[
					NonNegativeIntegers -> NonNegativeIntegers -> CartesianProductType["Integer64" -> ("Integer64" | Failure), "Integer64" -> ("Integer64" | Failure)] ->
						"Integer64" -> "Integer64" -> "Integer64" -> (CartesianProductType["Integer64", "Integer64"] | Failure),
					environment
				]
			],
			Map[Function[k, {leveled[compiledEvenQ, 20, k], leveled[compiledOddQ, 20, k]} === {compiledEvenQ[k], compiledOddQ[k]}], {0, 1, 2, 7, 12}],
			Map[Function[k, {leveled[groupA, 20, k], leveled[groupB, 20, k], leveled[groupC, 20, k], leveled[groupCaller, 20, k]} === {groupA[k], groupB[k], groupC[k], groupCaller[k]}], {-3, 0, 1, 5, 9}],
			Map[Function[k, {fueled[groupLoop, 20, 20, k], fueled[groupStep, 20, 20, k]} === {groupLoop[k], groupStep[k]}], {0, 1, 4, 7}],
			(* the parity of 7 calls down to 0, 8 levels; the ring from 6, 7 levels *)
			{leveled[compiledEvenQ, 8, 7], leveled[compiledEvenQ, 7, 7], leveled[groupA, 7, 6], leveled[groupA, 6, 6]},
			(* groupLoop at 4 calls to a depth of 5, and its loop takes 4 rounds and a last test *)
			{fueled[groupLoop, 5, 5, 4], fueled[groupLoop, 4, 5, 4], fueled[groupLoop, 5, 4, 4]}
		}
	],
	{
		TypeTheoryEnvironment,
		{
			{HoldForm["Recursion[compiledEvenQ, compiledOddQ]"], HoldForm[compiledEvenQ], HoldForm[compiledOddQ]},
			{HoldForm[groupOutside], HoldForm["Recursion[groupA, groupB, groupC]"], HoldForm[groupA], HoldForm[groupB], HoldForm[groupC], HoldForm[groupCaller]},
			{HoldForm["While[groupLoop]"], HoldForm["Recursion[groupLoop, groupStep]"], HoldForm[groupLoop], HoldForm[groupStep]}
		},
		True,
		True,
		ConstantArray[True, 5], ConstantArray[True, 5], ConstantArray[True, 4],
		{compiledEvenQ[7], Failure["RecursionLimit", <||>], groupA[6], Failure["RecursionLimit", <||>]},
		{groupLoop[4], Failure["RecursionLimit", <||>], Failure["OutOfFuel", <||>]}
	},
	TimeConstraint -> 120,
	TestID -> "Functions-that-call-each-other-are-one-recursion-on-the-levels"
]

(* And and Or of tests are the Ifs the compiler writes for them, with True or False outright in a branch, so the second
   test is computed only where the first leaves the value open: a quotient behind a test of its divisor never divides
   by 0 *)
testsBoth[a_Integer, b_Integer] := If[a > 0 && b > 0, 1, 0]
testsEither[a_Integer, b_Integer] := If[a > 0 || b > 0, 1, 0]
testsGuarded[a_Integer, b_Integer] := If[a != 0 && Quotient[b, a] > 1, 1, 0]
testsThree[a_Integer, b_Integer] := If[a > 0 && b > 0 && a < b, a, b]
testsMixed[a_Integer, b_Integer] := If[(a > 0 || b > 0) && ! (a == b), a + b, 0]

VerificationTest[
	Module[{environment, model},
		environment = TypeTheoryEnvironment[machine, Join[
			TypeTheoryFormalize[testsBoth, machine], TypeTheoryFormalize[testsEither, machine], TypeTheoryFormalize[testsGuarded, machine],
			TypeTheoryFormalize[testsThree, machine], TypeTheoryFormalize[testsMixed, machine]
		]];
		model[f_, a_, b_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm[
			"confirmBind"["machineResult"[Typed[a, Integers]], Typed[x, "Integer64"] |-> "confirmBind"["machineResult"[Typed[b, Integers]], f[x]]],
			environment
		]]];
		{
			Head[environment],
			Map[
				Function[f, AllTrue[Tuples[{-2, 0, 1, 3}, 2], Apply[Function[{a, b}, model[f, a, b] === f[a, b]]]]],
				{testsBoth, testsEither, testsGuarded, testsThree, testsMixed}
			],
			{model[testsGuarded, 0, 5], model[testsGuarded, 2, 5]}
		}
	],
	{TypeTheoryEnvironment, ConstantArray[True, 5], {0, 1}},
	TestID -> "And-and-Or-of-tests-compute-the-second-only-where-it-is-open"
]

(* an If whose branch sets a local, in the body of a loop: the steps to 1 of the Collatz map, counted, as the Wolfram
   Language counts them, and out of fuel with one round too few *)
VerificationTest[
	With[{environment = TypeTheoryEnvironment[machine, TypeTheoryFormalize[compiledCollatz, machine]]},
		Map[
			Apply[Function[{fuel, k}, TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], Typed[m, "Integer64"] |-> compiledCollatz[fuel, m]], environment]]]]],
			{{1, 1}, {9, 6}, {8, 6}, {17, 7}, {112, 27}}
		]
	],
	{compiledCollatz[1], compiledCollatz[6], Failure["OutOfFuel", <||>], compiledCollatz[7], compiledCollatz[27]},
	TestID -> "A-branch-that-sets-a-local-in-a-loop-counts-the-Collatz-steps"
]

(* The loop's theorem. A While of typed code is a constant by recursion on fuel, "While[loopSum]", and the compiled sum
   1 + ... + n is proved to be the triangular number: for every fuel above n, wherever the triangular number and n + 1
   fit a machine integer, the function gives a machine integer whose integer is loopTriangular[n]. The fuel stands
   in the statement for all fuel above n, so more fuel changes nothing.
   The proof: one round of the loop that continues and the round that stops, each by unfolding the loop once and
   rewriting its steps; then the invariant, that after j rounds the sum is loopTriangular[j] and the counter j + 1, by
   induction on the rounds left; then the function, which starts the loop at 0 and 1. *)
loopTriangular[0] = 0
loopTriangular[n_Integer] := n + loopTriangular[n - 1]
loopSum[n_Integer] := Module[{s = 0, i = 1}, While[i <= n, s = s + i; i = i + 1]; s]

loopFailures = {}
loopDeclare[environment_, declaration_] := Replace[TypeTheoryEnvironment[environment, {declaration}], failure_Failure :> (AppendTo[loopFailures, failure["Message"]]; environment)]
SetAttributes[loopTheorem, HoldAll]
loopTheorem[environment_, name_, statement_, tactics_] := Replace[TypeTheoryProof[statement, environment, tactics], {
	failure_Failure :> (AppendTo[loopFailures, {name, failure["Message"]}]; environment),
	proof_ :> loopDeclare[environment, TypeTheoryTheorem[name, proof]]
}]

loops = TypeTheoryEnvironment[machine, TypeTheoryFormalize[loopTriangular, machine, "Meaning" -> "Function", "Type" -> (NonNegativeIntegers -> NonNegativeIntegers)]]
loops = TypeTheoryEnvironment[loops, TypeTheoryFormalize[loopSum, loops]]

(* the order of the integers decided on natural numbers, both ways, and the machine's sum of two natural numbers are
   the machine library's: "integerLessEqualQOfNatural", "integerLessEqualQNotOfNatural", "machinePlusOfNatural" *)
loops = loopTheorem[loops, "notLessZero", ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n < 0, False]], {"Introduce"[n, h], "LinearArithmetic"}];
loops = loopTheorem[loops, "lessOfSuccessors", ForAll[{Typed[n, NonNegativeIntegers], Typed[l, NonNegativeIntegers]}, Implies[n + 1 < l + 1, n < l]], {"Introduce"[n, l, h], "LinearArithmetic"}];
loops = loopTheorem[loops, "roundContinues", ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), j + 1 <= k]], {"Introduce"[j, d, k, e], "LinearArithmetic"}];
loops = loopTheorem[loops, "roundStops", ForAll[{Typed[j, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j, Not[j + 1 <= k]]], {"Introduce"[j, k, e, h], "LinearArithmetic"}];
loops = loopTheorem[loops, "roundsLeft", ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), k == (j + 1) + d]], {"Introduce"[j, d, k, e], "LinearArithmetic"}];
loops = loopTheorem[loops, "counterBound", ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), Implies[k + 1 < 9223372036854775808, (j + 1) + 1 < 9223372036854775808]]], {"Introduce"[j, d, k, e, b], "LinearArithmetic"}];
loops = loopTheorem[loops, "commutedBound", ForAll[{Typed[a, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[(a + 1) + t < u, t + (a + 1) < u]], {"Introduce"[a, t, u, h], "LinearArithmetic"}];
(* the loopTriangular numbers grow *)
loops = loopTheorem[loops, "triangularStep", ForAll[{Typed[a, NonNegativeIntegers]}, loopTriangular[a] <= loopTriangular[a + 1]], {"Introduce"[a], "RewriteRepeated"[loopTriangular], "LinearArithmetic"}];
loops = loopTheorem[loops, "triangularMonotone", ForAll[{Typed[b, NonNegativeIntegers], Typed[a, NonNegativeIntegers]}, loopTriangular[a] <= loopTriangular[a + b]],
	{"Introduce"[b], "Induction"[b], "Introduce"[a], "Exact"["lessEqualReflexivity"], "Introduce"[c, ih, a], "Exact"["lessEqualTransitivity"[ih[a], "triangularStep"[a + c]]]}];
loops = loopTheorem[loops, "triangularBoundAt", ForAll[{Typed[a, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == a + d, Implies[loopTriangular[k] < 9223372036854775808, loopTriangular[a] < 9223372036854775808]]],
	{"Introduce"[a, d, k, e, b], "Rewrite"[e, "At" -> b], "Exact"["lessEqualTransitivity"["lessEqualSuccessor"["triangularMonotone"[d, a]], b]]}];

(* one round of the loop that continues, and the round that stops *)
loops = loopTheorem[loops, "whileRound",
	ForAll[{Typed[f, NonNegativeIntegers], Typed[n1, "Integer64"], Typed[s, "Integer64"], Typed[i, "Integer64"], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[top, NonNegativeIntegers],
			Typed[hn, n1[["integer"]] == "integerOfNatural"[top]], Typed[hs, s[["integer"]] == "integerOfNatural"[a]], Typed[hi, i[["integer"]] == "integerOfNatural"[b]],
			Typed[hle, b <= top], Typed[h1, a + b < 9223372036854775808], Typed[h2, b + 1 < 9223372036854775808]},
		"While[loopSum]"[f + 1, n1, s, i] == "While[loopSum]"[f, n1,
			"subtype"["integerOfNatural"[a + b], "naturalInteger64Range"[a + b, h1]],
			"subtype"["integerOfNatural"[b + 1], "naturalInteger64Range"[b + 1, h2]]]],
	{"Introduce"[f, n1, s, i, a, b, top, hn, hs, hi, hle, h1, h2], "RewriteRepeated"["While[loopSum]"], "Rewrite"[hi], "Rewrite"[hn], "Rewrite"[hs],
	 "Rewrite"["integerLessEqualQOfNatural"[b, top, hle]], "Rewrite"["machinePlusOfNatural"[a, b, h1]], "Rewrite"["machinePlusOfNatural"[b, 1, h2]], "Reflexivity"}];
loops = loopTheorem[loops, "whileStop",
	ForAll[{Typed[f, NonNegativeIntegers], Typed[n1, "Integer64"], Typed[s, "Integer64"], Typed[i, "Integer64"], Typed[b, NonNegativeIntegers], Typed[top, NonNegativeIntegers],
			Typed[hn, n1[["integer"]] == "integerOfNatural"[top]], Typed[hi, i[["integer"]] == "integerOfNatural"[b]], Typed[hle, Not[b <= top]]},
		"While[loopSum]"[f + 1, n1, s, i] == Typed["left"["pair"[s, i]], CartesianProductType["Integer64", "Integer64"] | Failure]],
	{"Introduce"[f, n1, s, i, b, top, hn, hi, hle], "RewriteRepeated"["While[loopSum]"], "Rewrite"[hi], "Rewrite"[hn],
	 "Rewrite"["integerLessEqualQNotOfNatural"[b, top, hle]], "Reflexivity"}];

(* the invariant of the loop, by induction on the rounds left, for all fuel above them *)
loops = loopTheorem[loops, "whileInvariant",
	ForAll[{Typed[top, NonNegativeIntegers], Typed[n1, "Integer64"]},
		Implies[n1[["integer"]] == "integerOfNatural"[top], Implies[loopTriangular[top] < 9223372036854775808, Implies[top + 1 < 9223372036854775808,
			ForAll[{Typed[d, NonNegativeIntegers], Typed[j, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[s, "Integer64"], Typed[i, "Integer64"]},
				Implies[top == j + d, Implies[d < fuel, Implies[s[["integer"]] == "integerOfNatural"[loopTriangular[j]], Implies[i[["integer"]] == "integerOfNatural"[j + 1],
					Exists[{Typed[v, "Integer64"], Typed[w, "Integer64"]},
						"While[loopSum]"[fuel, n1, s, i] == Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]]]]]]]]]],
	{
		"Introduce"[top, n1, hn, bT, bN, d], "Induction"[d],
		(* no round left: without fuel the bound on it is absurd; with fuel the loop stops with s *)
		"Introduce"[j, fuel], "Induction"[fuel],
		"Introduce"[s, i, e, h], "Exact"["falseElimination"["notLessZero"[0, h]]],
		"Introduce"[f, ihf, s, i, e, h, hs, hi],
		"Exact"["existsIntroduction"[s, "existsIntroduction"[i, "andIntroduction"[
			"whileStop"[f, n1, s, i, j + 1, top, hn, hi, "roundStops"[j, top, e]],
			"equalitySubstitution"["equalitySymmetry"[e], hs, P -> Function[{Typed[x, NonNegativeIntegers]}, s[["integer"]] == "integerOfNatural"[loopTriangular[x]]]]
		]]]],
		(* a round left: one round, then the hypothesis of the induction at the next counter and a unit of fuel less *)
		"Introduce"[d1, ihd, j, fuel], "Induction"[fuel],
		"Introduce"[s, i, e, h], "Exact"["falseElimination"["notLessZero"[d1 + 1, h]]],
		"Introduce"[f, ihf, s, i, e, h, hs, hi],
		"Rewrite"["whileRound"[f, n1, s, i, loopTriangular[j], j + 1, top, hn, hs, hi, "roundContinues"[j, d1, top, e],
			"commutedBound"[j, loopTriangular[j], 9223372036854775808, "triangularBoundAt"[j + 1, d1, top, "roundsLeft"[j, d1, top, e], bT]],
			"counterBound"[j, d1, top, e, bN]]],
		"Apply"[ihd[j + 1]],
		"Exact"["roundsLeft"[j, d1, top, e]],
		"Exact"["lessOfSuccessors"[d1, f, h]],
		"Exact"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, "integerOfNatural"[x]], "additionCommutativity"[loopTriangular[j], j + 1]]],
		"Reflexivity"
	}];

loops = loopTheorem[loops, "zeroPlus", ForAll[{Typed[t, NonNegativeIntegers]}, t == 0 + t], {"Introduce"[t], "LinearArithmetic"}];
loops = loopTheorem[loops, "zeroBound", 0 < 9223372036854775808, {"Decide"}];
loops = loopTheorem[loops, "oneBound", 1 < 9223372036854775808, {"Decide"}];
(* the function from the loop: where the loop gives the pair of v and w, the function gives v *)
loops = loopTheorem[loops, "loopSumOfLoop",
	ForAll[{Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"], Typed[v, "Integer64"], Typed[w, "Integer64"]},
		Implies[
			"While[loopSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
				Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure],
			loopSum[fuel, n] == Typed["left"[v], "Integer64" | Failure]]],
	{"Introduce"[fuel, n, v, w, h], "Exact"["equalityCongruence"[
		Function[{Typed[r, CartesianProductType["Integer64", "Integer64"] | Failure]},
			"confirmBind"[r, Function[{Typed[state, CartesianProductType["Integer64", "Integer64"]]}, Typed["left"[state[["first"]]], "Integer64" | Failure]]]],
		h]]}];
(* the theorem: with fuel above n, wherever the loopTriangular number and n + 1 fit, the compiled loop gives the loopTriangular number *)
loops = loopDeclare[loops, TypeTheoryTheorem["loopSumComputes",
	ForAll[{Typed[top, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"]},
		Implies[n[["integer"]] == "integerOfNatural"[top], Implies[loopTriangular[top] < 9223372036854775808, Implies[top + 1 < 9223372036854775808, Implies[top < fuel,
			Exists[{Typed[v, "Integer64"]}, loopSum[fuel, n] == Typed["left"[v], "Integer64" | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]]]]]],
	Function[{Typed[top, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"], Typed[hn, n[["integer"]] == "integerOfNatural"[top]],
			Typed[bT, loopTriangular[top] < 9223372036854775808], Typed[bN, top + 1 < 9223372036854775808], Typed[hf, top < fuel]},
		InductiveRecursor[Exists][
			Function[{Typed[t, Exists[{Typed[v, "Integer64"]}, Exists[{Typed[w, "Integer64"]},
				"While[loopSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
					Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]]]},
				Exists[{Typed[v, "Integer64"]}, loopSum[fuel, n] == Typed["left"[v], "Integer64" | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]],
			Function[{Typed[v, "Integer64"], Typed[hv, Exists[{Typed[w, "Integer64"]},
				"While[loopSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
					Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]]},
				InductiveRecursor[Exists][
					Function[{Typed[t, Exists[{Typed[w, "Integer64"]},
						"While[loopSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
							Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]]},
						Exists[{Typed[v1, "Integer64"]}, loopSum[fuel, n] == Typed["left"[v1], "Integer64" | Failure] && v1[["integer"]] == "integerOfNatural"[loopTriangular[top]]]],
					Function[{Typed[w, "Integer64"], Typed[hw,
						"While[loopSum]"[fuel, n, "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]]] ==
							Typed["left"["pair"[v, w]], CartesianProductType["Integer64", "Integer64"] | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]},
						"existsIntroduction"[v, "andIntroduction"["loopSumOfLoop"[fuel, n, v, w, hw[["left"]]], hw[["right"]]]]],
					hv
				]],
			"whileInvariant"[top, n, hn, bT, bN, top, 0, fuel,
				"subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]],
				"zeroPlus"[top], hf, "equalityReflexivity"["integerOfNatural"[0]], "equalityReflexivity"["integerOfNatural"[1]]]
		]
	]
]];

VerificationTest[
	{
		loopFailures,
		Sort[Select[Keys[Information[loops, "Theorems"]], Function[name, StringMatchQ[name, "while*" | "loopSum*"]]]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["loopSumComputes", loops]],
		(* the statement, as it is declared *)
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm["loopSumComputes", loops]],
			TypeTheoryTerm[
				ForAll[{Typed[top, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"]},
					Implies[n[["integer"]] == "integerOfNatural"[top], Implies[loopTriangular[top] < 9223372036854775808, Implies[top + 1 < 9223372036854775808, Implies[top < fuel,
						Exists[{Typed[v, "Integer64"]}, loopSum[fuel, n] == Typed["left"[v], "Integer64" | Failure] && v[["integer"]] == "integerOfNatural"[loopTriangular[top]]]]]]]],
				loops
			]
		],
		(* and the function runs: at 10 it gives 55 with fuel 11, and is out of fuel with 10 *)
		TypeTheoryExpression[NormalForm[TypeTheoryTerm[{"confirmBind"["machineResult"[10], Typed[m, "Integer64"] |-> loopSum[11, m]], "confirmBind"["machineResult"[10], Typed[m, "Integer64"] |-> loopSum[10, m]]}, loops]]]
	},
	{{}, {"loopSumComputes", "loopSumOfLoop", "whileInvariant", "whileRound", "whileStop"}, <|"quotientSoundness" -> "Proposition"|>, True, {55, Failure["OutOfFuel", <||>]}},
	TestID -> "The-compiled-loop-computes-the-triangular-number-for-all-fuel-above-its-rounds"
]


(* An If whose branch sets a local. The compiler keeps such a local lazily, its value in the C local; the meaning reads
   it as a local, and the If gives back the locals its branches set, each branch as it leaves them. Four shapes: both
   branches set the local; one branch sets it and the other leaves it; a branch sets two, one from the other; and an If
   that is read for its value and sets a local too. Each agrees with the Wolfram Language wherever the typed code does
   not leave, and leaves where a step overflows. *)
branchCollatz[n_Integer] := Module[{r = n}, If[Mod[n, 2] == 0, r = Quotient[n, 2], r = 3 n + 1]; r]
branchClamp[n_Integer] := Module[{r = n}, If[n < 0, r = 0]; r]
branchBoth[n_Integer] := Module[{a = 0, b = 1}, If[n < 5, a = n; b = a + 1, b = n]; a + b]
branchValued[n_Integer] := Module[{r = 0, q = 0}, q = If[n < 0, r = 1; -n, n]; q + r]

VerificationTest[
	Module[{environment, model},
		environment = TypeTheoryEnvironment[machine, Join[
			TypeTheoryFormalize[branchCollatz, machine], TypeTheoryFormalize[branchClamp, machine], TypeTheoryFormalize[branchBoth, machine], TypeTheoryFormalize[branchValued, machine]
		]];
		model[f_, k_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm["confirmBind"["machineResult"[Typed[k, Integers]], f], environment]]];
		{
			Head[environment],
			Map[Function[k, model[branchCollatz, k] === branchCollatz[k]], {0, 1, 6, 7, 27, -8, -7, 3074457345618258602}],
			(* 3 n + 1 past 2^63 - 1: the typed code leaves, and the Wolfram Language computes the number exactly *)
			{model[branchCollatz, 3074457345618258603], branchCollatz[3074457345618258603]},
			Map[Function[k, model[branchClamp, k] === branchClamp[k]], {-9223372036854775808, -5, -1, 0, 1, 9223372036854775807}],
			Map[Function[k, model[branchBoth, k] === branchBoth[k]], {-3, 0, 3, 4, 5, 9}],
			Map[Function[k, model[branchValued, k] === branchValued[k]], {-4, -1, 0, 4}],
			(* the one branch that sets the local gives it, and the other the local as it was *)
			TypeTheoryFormalize[branchClamp, machine]
		}
	],
	{
		TypeTheoryEnvironment,
		ConstantArray[True, 8],
		{Failure["IntegerOverflow", <||>], 9223372036854775810},
		ConstantArray[True, 6], ConstantArray[True, 6], ConstantArray[True, 4],
		{TypeTheoryDefinition[branchClamp, Typed[
			Function[{Typed[n, "Integer64"]}, "confirmBind"[
				"machineIf"["not"["integerLessEqualQ"[0, n[["integer"]]]],
					"confirmBind"["machineResult"[0], Function[{Typed[WolframInstitute`TypeTheory`Compiled`r2, "Integer64"]}, Typed["left"[WolframInstitute`TypeTheory`Compiled`r2], "Integer64" | Failure]]],
					Typed["left"[n], "Integer64" | Failure]],
				Function[{Typed[WolframInstitute`TypeTheory`Compiled`brancht4, "Integer64"]}, Typed["left"[WolframInstitute`TypeTheory`Compiled`brancht4], "Integer64" | Failure]]
			]],
			"Integer64" -> ("Integer64" | Failure)
		]]}
	},
	TestID -> "An-If-whose-branch-sets-a-local-gives-the-locals-back"
]

(* Vectors, the packed arrays of rank 1 of typed code (Library/MachineArrays.wl). A function of a vector is formalized
   with its types, Typed[f, {types} -> result], as FunctionCompile takes it: an argument x_List says no type of its own.
   A vector is a "PackedArray"["Integer64", 1], a list whose length a machine integer holds; Length of it never leaves,
   Part, Take, Total and ConstantArray leave where typed code does, and a[[i]] = v sets the local a to the array with
   the part set, so that a loop that sets parts carries the array in its state. *)
vectorSum[v_List] := Module[{s = 0, i = 1}, While[i <= Length[v], s = s + v[[i]]; i = i + 1]; s]
vectorSquares[n_Integer] := Module[{a = ConstantArray[0, n], i = 1}, While[i <= n, a[[i]] = i i; i = i + 1]; a]
vectorLast[v_List] := v[[-1]]
vectorHeadTotal[v_List, k_Integer] := Total[Take[v, k]]

vectors = TypeTheoryEnvironment[machine, Join[
	TypeTheoryFormalize[Typed[vectorSum, {"PackedArray"::["Integer64", 1]} -> "Integer64"], machine],
	TypeTheoryFormalize[vectorSquares, machine],
	TypeTheoryFormalize[Typed[vectorLast, {"PackedArray"::["MachineInteger", 1]} -> "MachineInteger"], machine],
	TypeTheoryFormalize[vectorHeadTotal, machine, "Type" -> ({"PackedArray"["Integer64", 1], "Integer64"} -> "Integer64")]
]]

SetAttributes[vectorValue, HoldFirst]
vectorValue[term_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm[term, vectors]]]

(* each of the four, at the squares of 1 to 5, gives what the Wolfram Language's evaluator gives, and leaves where typed
   code does: a part that is not there, a negative length, a total past the machine integers, and the fuel of a loop
   used up *)
VerificationTest[
	{
		Length[Information[vectors, "Constants"]] - Length[Information[machine, "Constants"]],
		vectorValue["confirmBind"["machineResult"[5], Typed[n, "Integer64"] |-> vectorSquares[20, n]]],
		vectorValue["confirmBind"["machineResult"[5], Typed[n, "Integer64"] |-> "confirmBind"[vectorSquares[20, n], Typed[a, "PackedArray"["Integer64", 1]] |-> vectorSum[20, a]]]],
		vectorValue["confirmBind"["machineResult"[5], Typed[n, "Integer64"] |-> "confirmBind"[vectorSquares[20, n], vectorLast]]],
		vectorValue["confirmBind"["machineResult"[5], Typed[n, "Integer64"] |-> "confirmBind"["machineResult"[3], Typed[k, "Integer64"] |->
			"confirmBind"[vectorSquares[20, n], Typed[a, "PackedArray"["Integer64", 1]] |-> vectorHeadTotal[a, k]]]]],
		{
			vectorValue["confirmBind"["machineResult"[5], Typed[n, "Integer64"] |-> "confirmBind"["machineResult"[6], Typed[k, "Integer64"] |->
				"confirmBind"[vectorSquares[20, n], Typed[a, "PackedArray"["Integer64", 1]] |-> vectorHeadTotal[a, k]]]]],
			vectorValue["confirmBind"["machineResult"[-1], Typed[n, "Integer64"] |-> vectorSquares[20, n]]],
			vectorValue["confirmBind"["machineResult"[0], Typed[n, "Integer64"] |-> "confirmBind"[vectorSquares[20, n], vectorLast]]],
			vectorValue["confirmBind"["machineResult"[4611686018427387904], Typed[x, "Integer64"] |-> "confirmBind"["machineResult"[2], Typed[k, "Integer64"] |->
				"confirmBind"["arrayConstant"[x, 2], Typed[a, "PackedArray"["Integer64", 1]] |-> vectorHeadTotal[a, k]]]]],
			vectorValue["confirmBind"["machineResult"[5], Typed[n, "Integer64"] |-> "confirmBind"[vectorSquares[20, n], Typed[a, "PackedArray"["Integer64", 1]] |-> vectorSum[5, a]]]]
		}
	},
	{
		6,
		vectorSquares[5],
		vectorSum[vectorSquares[5]],
		vectorLast[vectorSquares[5]],
		vectorHeadTotal[vectorSquares[5], 3],
		{Failure["PartRange", <||>], Failure["Range", <||>], Failure["PartRange", <||>], Failure["IntegerOverflow", <||>], Failure["OutOfFuel", <||>]}
	},
	TestID -> "Functions-of-vectors-compute-what-the-evaluator-computes-and-leave-where-typed-code-does"
]

(* the types given are the compiler's or the environment's names alike, as Typed or as the option "Type"; a function
   whose argument is x_List and whose types are not given is refused, saying to give them, and so are types that are
   not the compiler's: a result it does not find, a number of arguments it does not have, a rank the model does not
   have, and a type that is no {types} -> result *)
VerificationTest[
	{
		TypeTheoryFormalize[Typed[vectorSum, {"PackedArray"::["Integer64", 1]} -> "Integer64"], machine] ===
			TypeTheoryFormalize[vectorSum, machine, "Type" -> ({"PackedArray"["MachineInteger", 1]} -> "MachineInteger")],
		TypeTheoryFormalize[vectorSquares, machine] === TypeTheoryFormalize[Typed[vectorSquares, {"Integer64"} -> "PackedArray"::["Integer64", 1]], machine],
		Map[
			Function[failure, failure["Tag"]],
			{
				TypeTheoryFormalize[vectorSum, machine],
				TypeTheoryFormalize[Typed[vectorSum, {"PackedArray"::["Integer64", 1]} -> "Real64"], machine],
				TypeTheoryFormalize[Typed[vectorSum, {"PackedArray"::["Integer64", 1], "Integer64"} -> "Integer64"], machine],
				TypeTheoryFormalize[Typed[vectorSum, {"PackedArray"::["Integer64", 2]} -> "Integer64"], machine],
				TypeTheoryFormalize[Typed[vectorSum, "Integer64"], machine]
			}
		],
		StringContainsQ[TypeTheoryFormalize[vectorSum, machine]["Message"], "Typed["],
		(* a rank above 2 is refused by name, typed code having none *)
		With[{failure = TypeTheoryFormalize[Typed[vectorSum, {"PackedArray"::["Integer64", 3]} -> "Integer64"], machine]},
			{failure["Tag"], StringContainsQ[failure["Message"], "rank above 2"], StringContainsQ[ToString[failure["MessageParameters"], InputForm], "3"]}
		]
	},
	{True, True, {"NoTypedEntry", "TypedResult", "TypedArguments", "UnmodeledType", "TypedSignature"}, True, {"UnmodeledType", True, True}},
	TestID -> "A-function-of-a-vector-is-formalized-with-its-types-and-wrong-types-are-refused"
]

(* The two theorems of the vectors. vectorSum, a While over the parts of an array, computes the array's Total, with its
   leaves, for all fuel above the array's length, wherever its length and one more are machine integers, the counter
   that passes the last part being one more; and where no partial sum leaves, the sum of the integers of the list.
   vectorSquares, a ConstantArray whose parts a While sets, gives the squares of 1 to n wherever n n is a machine
   integer, for all fuel above n. The proofs: one round of each loop and the round that stops, by unfolding the loop
   once; an invariant, by induction on the elements left, with the array split at the place the loop is at, pre and the
   rest; then the function, which starts the loop at the first place. The library gives the parts of an array split so,
   "arrayPartOfJoin" and "arraySetPartOfJoin", and a continuation bound twice as once, "confirmBindThen". *)
vectorFailures = {}
vectorDeclare[environment_, declaration_] := Replace[TypeTheoryEnvironment[environment, {declaration}], failure_Failure :> (AppendTo[vectorFailures, failure["Message"]]; environment)]
SetAttributes[vectorTheorem, HoldAll]
vectorTheorem[environment_, name_, statement_, tactics_] := Replace[TypeTheoryProof[statement, environment, tactics], {
	failure_Failure :> (AppendTo[vectorFailures, {name, failure["Message"]}]; environment),
	proof_ :> vectorDeclare[environment, TypeTheoryTheorem[name, proof]]
}]

(* the squares of 1 to n, as integers, which vectorSquares is stated against *)
vectors = vectorDeclare[vectors, TypeTheoryDefinition["integerSquares", Typed[
	Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
		Function[{Typed[k, NonNegativeIntegers]}, {Integers}],
		Typed[{}, {Integers}],
		Function[{Typed[k, NonNegativeIntegers], Typed[r, {Integers}]}, Join[r, Prepend["integerOfNatural"[(k + 1) (k + 1)]][{}]]],
		n
	]],
	NonNegativeIntegers -> {Integers}
]]]

With[{
		upper = 9223372036854775808,
		integerOf = Function[{Typed[z, "Integer64"]}, z[["integer"]]],
		zeroValue = Typed["subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "Integer64"],
		oneValue = Typed["subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]], "Integer64"]
	},
	vectors = vectorTheorem[vectors, "notLessZero", ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n < 0, False]], {"Introduce"[n, h], "LinearArithmetic"}];
	vectors = vectorTheorem[vectors, "lessOfSuccessors", ForAll[{Typed[n, NonNegativeIntegers], Typed[l, NonNegativeIntegers]}, Implies[n + 1 < l + 1, n < l]], {"Introduce"[n, l, h], "LinearArithmetic"}];
	vectors = vectorTheorem[vectors, "roundBound",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[a + 1 <= b, Implies[b + 1 < u, (a + 1) + 1 < u]]],
		{"Introduce"[a, b, u, h, k], "LinearArithmetic"}
	];
	vectors = vectorTheorem[vectors, "lengthOfSplit",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[pre, {A}], Typed[x, A], Typed[rest, {A}]}, Implies[l == Join[pre, Prepend[x][rest]], Length[pre] + 1 <= Length[l]]],
		{"Introduce"[A, l, pre, x, rest, e], "Rewrite"[e], "Rewrite"["lengthJoin"[pre, Prepend[x][rest]]], "Change"[Length[pre] + 1 <= Length[pre] + (Length[rest] + 1)], "LinearArithmetic"}
	];
	vectors = vectorTheorem[vectors, "lengthOfWhole",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[pre, {A}]}, Implies[l == Join[pre, {}], Not[Length[pre] + 1 <= Length[l]]]],
		{"Introduce"[A, l, pre, e, h], "Rewrite"[e, "At" -> h], "Rewrite"["joinEmptyRight"[pre], "At" -> h], "LinearArithmetic"}
	];
	vectors = vectorTheorem[vectors, "vectorRound",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]], Typed[s, "Integer64"], Typed[i, "Integer64"], Typed[pre, {"Integer64"}], Typed[x, "Integer64"], Typed[rest, {"Integer64"}],
				Typed[e, v[["list"]] == Join[pre, Prepend[x][rest]]], Typed[hi, i[["integer"]] == "integerOfNatural"[Length[pre] + 1]], Typed[h2, (Length[pre] + 1) + 1 < 9223372036854775808]},
			"While[vectorSum]"[f + 1, v, s, i] == "confirmBind"["machinePlus"[s[["integer"]], x[["integer"]]],
				Function[{Typed[t, "Integer64"]}, "While[vectorSum]"[f, v, t, "subtype"["integerOfNatural"[(Length[pre] + 1) + 1], "naturalInteger64Range"[(Length[pre] + 1) + 1, h2]]]]]],
		{"Introduce"[f, v, s, i, pre, x, rest, e, hi, h2], "RewriteRepeated"["While[vectorSum]"], "Rewrite"["arrayLengthInteger"["Integer64", v]], "Rewrite"[hi],
			"Rewrite"["integerLessEqualQOfNatural"[Length[pre] + 1, Length[v[["list"]]], "lengthOfSplit"["Integer64", v[["list"]], pre, x, rest, e]]],
			"Rewrite"["arrayPartOfJoin"["Integer64", v, pre, x, rest, e]],
			"Rewrite"["machinePlusOfNatural"[Length[pre] + 1, 1, h2]],
			"Reflexivity"}
	];
	vectors = vectorTheorem[vectors, "vectorStop",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]], Typed[s, "Integer64"], Typed[i, "Integer64"], Typed[n, NonNegativeIntegers],
				Typed[hi, i[["integer"]] == "integerOfNatural"[n + 1]], Typed[hle, Not[n + 1 <= Length[v[["list"]]]]]},
			"While[vectorSum]"[f + 1, v, s, i] == Typed["left"["pair"[s, i]], CartesianProductType["Integer64", "Integer64"] | Failure]],
		{"Introduce"[f, v, s, i, n, hi, hle], "RewriteRepeated"["While[vectorSum]"], "Rewrite"["arrayLengthInteger"["Integer64", v]], "Rewrite"[hi],
			"Rewrite"["integerLessEqualQNotOfNatural"[n + 1, Length[v[["list"]]], hle]], "Reflexivity"}
	];
	vectors = vectorTheorem[vectors, "vectorInvariant",
		ForAll[{Typed[v, "PackedArray"["Integer64", 1]]}, Implies[Length[v[["list"]]] + 1 < 9223372036854775808,
			ForAll[{Typed[rest, {"Integer64"}], Typed[pre, {"Integer64"}], Typed[fuel, NonNegativeIntegers], Typed[s, "Integer64"], Typed[i, "Integer64"]},
				Implies[v[["list"]] == Join[pre, rest], Implies[i[["integer"]] == "integerOfNatural"[Length[pre] + 1], Implies[Length[rest] < fuel,
					"confirmBind"["While[vectorSum]"[fuel, v, s, i], Function[{Typed[state, CartesianProductType["Integer64", "Integer64"]]}, Typed["left"[state[["first"]]], "Integer64" | Failure]]] ==
						"integerListTotal"[rest][s]]]]]]],
		{"Introduce"[v, bound, rest], "Induction"[rest],
			(* nothing left: without fuel the bound on it is absurd; with fuel the loop stops with s *)
			"Introduce"[pre, fuel], "Cases"[fuel],
			"Introduce"[s, i, e, hi, hf], "Exact"["falseElimination"["notLessZero"[0, hf]]],
			"Introduce"[f, s, i, e, hi, hf],
			"Rewrite"["vectorStop"[f, v, s, i, Length[pre], hi, "lengthOfWhole"["Integer64", v[["list"]], pre, e]]], "Reflexivity",
			(* an element left: one round, then the hypothesis of the induction at the next place and a unit of fuel less *)
			"Introduce"[x, tail, ih, pre, fuel], "Cases"[fuel],
			"Introduce"[s, i, e, hi, hf], "Exact"["falseElimination"["notLessZero"[Length[tail] + 1, hf]]],
			"Introduce"[f, s, i, e, hi, hf],
			"Have"[h2, (Length[pre] + 1) + 1 < 9223372036854775808],
			"Exact"["roundBound"[Length[pre], Length[v[["list"]]], 9223372036854775808, "lengthOfSplit"["Integer64", v[["list"]], pre, x, tail, e], bound]],
			"Rewrite"["vectorRound"[f, v, s, i, pre, x, tail, e, hi, h2]],
			"Apply"["confirmBindThen"["Integer64", CartesianProductType["Integer64", "Integer64"], "Integer64", "machinePlus"[s[["integer"]], x[["integer"]]],
				Function[{Typed[t, "Integer64"]}, "While[vectorSum]"[f, v, t, "subtype"["integerOfNatural"[(Length[pre] + 1) + 1], "naturalInteger64Range"[(Length[pre] + 1) + 1, h2]]]],
				Function[{Typed[state, CartesianProductType["Integer64", "Integer64"]]}, Typed["left"[state[["first"]]], "Integer64" | Failure]],
				"integerListTotal"[tail]]],
			"Introduce"[t],
			"Apply"[ih[Join[pre, Prepend[x][{}]], f, t, "subtype"["integerOfNatural"[(Length[pre] + 1) + 1], "naturalInteger64Range"[(Length[pre] + 1) + 1, h2]]]],
			"Exact"["equalityTransitivity"[e, "equalitySymmetry"["joinAssociativity"[pre, Prepend[x][{}], tail]]]],
			"Exact"["equalityCongruence"[Function[{Typed[k, NonNegativeIntegers]}, "integerOfNatural"[k + 1]], "equalitySymmetry"["lengthJoin"[pre, Prepend[x][{}]]]]],
			"Exact"["lessOfSuccessors"[Length[tail], f, hf]]}
	];
	vectors = vectorTheorem[vectors, "zeroBound", 0 < 9223372036854775808, {"Decide"}];
	vectors = vectorTheorem[vectors, "oneBound", 1 < 9223372036854775808, {"Decide"}];
	vectors = vectorTheorem[vectors, "vectorSumIsTotal",
		ForAll[{Typed[fuel, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]]},
			Implies[Length[v[["list"]]] + 1 < 9223372036854775808, Implies[Length[v[["list"]]] < fuel, vectorSum[fuel, v] == "arrayTotal"[v]]]],
		{"Introduce"[fuel, v, bound, hf],
			"Exact"["vectorInvariant"[v, bound, v[["list"]], Typed[{}, {"Integer64"}], fuel,
				"subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]],
				"equalityReflexivity"[v[["list"]]], "equalityReflexivity"["integerOfNatural"[1]], hf]]}
	];
	vectors = vectorTheorem[vectors, "vectorSumComputes",
		ForAll[{Typed[fuel, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]]},
			Implies[Length[v[["list"]]] + 1 < 9223372036854775808, Implies[Length[v[["list"]]] < fuel, Implies["partialSumsInRange"[v[["list"]]][0],
				Exists[{Typed[r, "Integer64"]}, vectorSum[fuel, v] == Typed["left"[r], "Integer64" | Failure] && r[["integer"]] == "integerListSum"[v[["list"]]]]]]]],
		{"Introduce"[fuel, v, bound, hf, sums],
			"Rewrite"["vectorSumIsTotal"[fuel, v, bound, hf]],
			"Cases"["integerListTotalOfSums"[v[["list"]], "subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], sums]],
			"Introduce"[r, hr],
			"Exact"["existsIntroduction"[r, "andIntroduction"[hr[["left"]], "equalityTransitivity"[hr[["right"]], "integerAdditionZeroLeft"["integerListSum"[v[["list"]]]]]]]]}
	];
	vectors = vectorTheorem[vectors, "machineSquare",
		ForAll[{Typed[k, NonNegativeIntegers]}, Implies[k k < upper,
			Exists[{Typed[q, "Integer64"]}, "machineTimes"["integerOfNatural"[k], "integerOfNatural"[k]] == Typed["left"[q], "Integer64" | Failure] && q[["integer"]] == "integerOfNatural"[k k]]]],
		{"Introduce"[k, h], "Exact"["existsIntroduction"["subtype"["integerOfNatural"[k k], "naturalInteger64Range"[k k, h]],
			"andIntroduction"["machineTimesOfNatural"[k, k, h], "equalityReflexivity"["integerOfNatural"[k k]]]]]}
	];
	vectors = vectorTheorem[vectors, "roundContinues", ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), j + 1 <= k]], {"Introduce"[j, d, k, e], "LinearArithmetic"}];
	vectors = vectorTheorem[vectors, "roundsLeft", ForAll[{Typed[j, NonNegativeIntegers], Typed[d, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + (d + 1), k == (j + 1) + d]], {"Introduce"[j, d, k, e], "LinearArithmetic"}];
	vectors = vectorTheorem[vectors, "stopsAt", ForAll[{Typed[j, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[k == j + 0, Not[j + 1 <= k]]], {"Introduce"[j, k, e, h], "LinearArithmetic"}];
	vectors = vectorTheorem[vectors, "squareBound",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[u, NonNegativeIntegers]}, Implies[a <= t, Implies[t t < u, a a < u]]],
		{"Introduce"[a, t, u, h, k], "NonlinearArithmetic"}
	];
	vectors = vectorTheorem[vectors, "squareRootBound",
		ForAll[{Typed[t, NonNegativeIntegers]}, Implies[t t < upper, t + 1 < upper]],
		{"Introduce"[t], "Cases"[t],
			"Introduce"[h], "Decide",
			"Introduce"[k], "Cases"[k],
			"Introduce"[h], "Decide",
			"Introduce"[j, h], "LinearArithmetic"}
	];
	vectors = vectorTheorem[vectors, "squaresRound",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[n1, "Integer64"], Typed[a, "PackedArray"["Integer64", 1]], Typed[i, "Integer64"], Typed[top, NonNegativeIntegers], Typed[k, NonNegativeIntegers],
				Typed[q, "Integer64"], Typed[b, "PackedArray"["Integer64", 1]],
				Typed[hn, n1[["integer"]] == "integerOfNatural"[top]], Typed[hi, i[["integer"]] == "integerOfNatural"[k + 1]], Typed[hle, k + 1 <= top],
				Typed[hq, "machineTimes"["integerOfNatural"[k + 1], "integerOfNatural"[k + 1]] == Typed["left"[q], "Integer64" | Failure]],
				Typed[hb, "arraySetPart"[a, "integerOfNatural"[k + 1], q] == Typed["left"[b], "PackedArray"["Integer64", 1] | Failure]],
				Typed[h2, (k + 1) + 1 < upper]},
			"While[vectorSquares]"[f + 1, n1, a, i] == "While[vectorSquares]"[f, n1, b, "subtype"["integerOfNatural"[(k + 1) + 1], "naturalInteger64Range"[(k + 1) + 1, h2]]]],
		{"Introduce"[f, n1, a, i, top, k, q, b, hn, hi, hle, hq, hb, h2], "RewriteRepeated"["While[vectorSquares]"], "Rewrite"[hi], "Rewrite"[hn],
			"Rewrite"["integerLessEqualQOfNatural"[k + 1, top, hle]], "Rewrite"[hq], "RewriteRepeated"["confirmBind"], "Rewrite"[hb], "RewriteRepeated"["confirmBind"],
			"Rewrite"["machinePlusOfNatural"[k + 1, 1, h2]], "Reflexivity"}
	];
	vectors = vectorTheorem[vectors, "squaresStop",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[n1, "Integer64"], Typed[a, "PackedArray"["Integer64", 1]], Typed[i, "Integer64"], Typed[top, NonNegativeIntegers], Typed[k, NonNegativeIntegers],
				Typed[hn, n1[["integer"]] == "integerOfNatural"[top]], Typed[hi, i[["integer"]] == "integerOfNatural"[k + 1]], Typed[hle, Not[k + 1 <= top]]},
			"While[vectorSquares]"[f + 1, n1, a, i] == Typed["left"["pair"[a, i]], CartesianProductType["PackedArray"["Integer64", 1], "Integer64"] | Failure]],
		{"Introduce"[f, n1, a, i, top, k, hn, hi, hle], "RewriteRepeated"["While[vectorSquares]"], "Rewrite"[hi], "Rewrite"[hn],
			"Rewrite"["integerLessEqualQNotOfNatural"[k + 1, top, hle]], "Reflexivity"}
	];
	vectors = vectorTheorem[vectors, "squaresInvariant",
		ForAll[{Typed[top, NonNegativeIntegers], Typed[n1, "Integer64"]}, Implies[n1[["integer"]] == "integerOfNatural"[top], Implies[top top < upper, Implies[top + 1 < upper,
			ForAll[{Typed[rest, {"Integer64"}], Typed[pre, {"Integer64"}], Typed[fuel, NonNegativeIntegers], Typed[a, "PackedArray"["Integer64", 1]], Typed[i, "Integer64"]},
				Implies[a[["list"]] == Join[pre, rest], Implies[top == Length[pre] + Length[rest], Implies[i[["integer"]] == "integerOfNatural"[Length[pre] + 1], Implies[Length[rest] < fuel,
					Implies[Map[integerOf, pre] == "integerSquares"[Length[pre]],
						Exists[{Typed[b, "PackedArray"["Integer64", 1]], Typed[w, "Integer64"]},
							"While[vectorSquares]"[fuel, n1, a, i] == Typed["left"["pair"[b, w]], CartesianProductType["PackedArray"["Integer64", 1], "Integer64"] | Failure] &&
								Map[integerOf, b[["list"]]] == "integerSquares"[top]]]]]]]]]]]],
		{"Introduce"[top, n1, hn, bT, bN, rest], "Induction"[rest],
			(* nothing left to set: the loop stops with the array *)
			"Introduce"[pre, fuel], "Cases"[fuel],
			"Introduce"[a, i, e, ht, hi, hf, hp], "Exact"["falseElimination"["notLessZero"[0, hf]]],
			"Introduce"[f, a, i, e, ht, hi, hf, hp],
			"Have"[hm, Map[integerOf, a[["list"]]] == "integerSquares"[top]],
			"Rewrite"[e], "Rewrite"["joinEmptyRight"[pre]], "Rewrite"[ht], "Exact"[hp],
			"Exact"["existsIntroduction"[a, "existsIntroduction"[i, "andIntroduction"["squaresStop"[f, n1, a, i, top, Length[pre], hn, hi, "stopsAt"[Length[pre], top, ht]], hm]]]],
			(* a part left: one round sets it, then the hypothesis of the induction with the part among those set *)
			"Introduce"[y, tail, ih, pre, fuel], "Cases"[fuel],
			"Introduce"[a, i, e, ht, hi, hf, hp], "Exact"["falseElimination"["notLessZero"[Length[tail] + 1, hf]]],
			"Introduce"[f, a, i, e, ht, hi, hf, hp],
			"Have"[hle, Length[pre] + 1 <= top], "Exact"["roundContinues"[Length[pre], Length[tail], top, ht]],
			"Have"[h1, (Length[pre] + 1) (Length[pre] + 1) < upper], "Exact"["squareBound"[Length[pre] + 1, top, upper, hle, bT]],
			"Have"[h2, (Length[pre] + 1) + 1 < upper], "Exact"["roundBound"[Length[pre], top, upper, hle, bN]],
			"Cases"["machineSquare"[Length[pre] + 1, h1]], "Introduce"[q, hq],
			"Cases"["arraySetPartOfJoin"["Integer64", a, pre, y, q, tail, e]], "Introduce"[b, hb],
			"Rewrite"["squaresRound"[f, n1, a, i, top, Length[pre], q, b, hn, hi, hle, hq[["left"]], hb[["left"]], h2]],
			"Apply"[ih[Join[pre, Prepend[q][{}]], f, b, "subtype"["integerOfNatural"[(Length[pre] + 1) + 1], "naturalInteger64Range"[(Length[pre] + 1) + 1, h2]]]],
			"Exact"["equalityTransitivity"[hb[["right"]], "equalitySymmetry"["joinAssociativity"[pre, Prepend[q][{}], tail]]]],
			"Rewrite"["lengthJoin"[pre, Prepend[q][{}]]], "Exact"["roundsLeft"[Length[pre], Length[tail], top, ht]],
			"Exact"["equalityCongruence"[Function[{Typed[m, NonNegativeIntegers]}, "integerOfNatural"[m + 1]], "equalitySymmetry"["lengthJoin"[pre, Prepend[q][{}]]]]],
			"Exact"["lessOfSuccessors"[Length[tail], f, hf]],
			"Rewrite"["mapJoin"[integerOf, pre, Prepend[q][{}]]], "Rewrite"[hp], "Rewrite"["lengthJoin"[pre, Prepend[q][{}]]],
			"Change"[Join["integerSquares"[Length[pre]], Prepend[q[["integer"]]][{}]] == Join["integerSquares"[Length[pre]], Prepend["integerOfNatural"[(Length[pre] + 1) (Length[pre] + 1)]][{}]]],
			"Rewrite"[hq[["right"]]]}
	];
	vectors = vectorTheorem[vectors, "squaresOfLoop",
		ForAll[{Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"], Typed[a, "PackedArray"["Integer64", 1]], Typed[b, "PackedArray"["Integer64", 1]], Typed[w, "Integer64"]},
			Implies["arrayConstant"[zeroValue, n[["integer"]]] == Typed["left"[a], "PackedArray"["Integer64", 1] | Failure],
				Implies["While[vectorSquares]"[fuel, n, a, oneValue] == Typed["left"["pair"[b, w]], CartesianProductType["PackedArray"["Integer64", 1], "Integer64"] | Failure],
					vectorSquares[fuel, n] == Typed["left"[b], "PackedArray"["Integer64", 1] | Failure]]]],
		{"Introduce"[fuel, n, a, b, w, h1, h2],
			"Change"["confirmBind"["arrayConstant"[zeroValue, n[["integer"]]], Function[{Typed[t, "PackedArray"["Integer64", 1]]},
				"confirmBind"["While[vectorSquares]"[fuel, n, t, oneValue], Function[{Typed[state, CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]}, Typed["left"[state[["first"]]], "PackedArray"["Integer64", 1] | Failure]]]]] ==
					Typed["left"[b], "PackedArray"["Integer64", 1] | Failure]],
			"Rewrite"[h1],
			"Change"["confirmBind"["While[vectorSquares]"[fuel, n, a, oneValue], Function[{Typed[state, CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]}, Typed["left"[state[["first"]]], "PackedArray"["Integer64", 1] | Failure]]] ==
				Typed["left"[b], "PackedArray"["Integer64", 1] | Failure]],
			"Rewrite"[h2], "Reflexivity"}
	];
	vectors = vectorTheorem[vectors, "squaresComputes",
		ForAll[{Typed[top, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"]},
			Implies[n[["integer"]] == "integerOfNatural"[top], Implies[top top < upper, Implies[top < fuel,
				Exists[{Typed[a, "PackedArray"["Integer64", 1]]}, vectorSquares[fuel, n] == Typed["left"[a], "PackedArray"["Integer64", 1] | Failure] && Map[integerOf, a[["list"]]] == "integerSquares"[top]]]]]],
		{"Introduce"[top, fuel, n, hn, bT, hf],
			"Have"[bN, top + 1 < upper], "Exact"["squareRootBound"[top, bT]],
			"Have"[bK, top < upper], "LinearArithmetic",
			"Cases"["arrayConstantOfNatural"["Integer64", zeroValue, top, bK]], "Introduce"[a0, h0],
			"Have"[h1, "arrayConstant"[zeroValue, n[["integer"]]] == Typed["left"[a0], "PackedArray"["Integer64", 1] | Failure]], "Rewrite"[hn], "Exact"[h0[["left"]]],
			"Have"[ht, top == 0 + Length["listConstant"[zeroValue, top]]], "Rewrite"["listConstantLength"["Integer64", zeroValue, top]], "LinearArithmetic",
			"Have"[hl, Length["listConstant"[zeroValue, top]] < fuel], "Rewrite"["listConstantLength"["Integer64", zeroValue, top]], "Exact"[hf],
			"Cases"["squaresInvariant"[top, n, hn, bT, bN, "listConstant"[zeroValue, top], Typed[{}, {"Integer64"}], fuel, a0, oneValue,
				h0[["right"]], ht, "equalityReflexivity"["integerOfNatural"[1]], hl, "equalityReflexivity"[Typed[{}, {Integers}]]]],
			"Introduce"[b, hb], "Cases"[hb], "Introduce"[w, hw],
			"Exact"["existsIntroduction"[b, "andIntroduction"["squaresOfLoop"[fuel, n, a0, b, w, h1, hw[["left"]]], hw[["right"]]]]]}
	]
]

VerificationTest[
	{
		vectorFailures,
		Map[Function[name, TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, vectors}]], {"vectorSumIsTotal", "vectorSumComputes", "squaresComputes"}],
		(* the statements, as they are declared *)
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm["vectorSumIsTotal", vectors]],
			TypeTheoryTerm[
				ForAll[{Typed[fuel, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]]},
					Implies[Length[v[["list"]]] + 1 < 9223372036854775808, Implies[Length[v[["list"]]] < fuel, vectorSum[fuel, v] == "arrayTotal"[v]]]],
				vectors
			]
		],
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm["vectorSumComputes", vectors]],
			TypeTheoryTerm[
				ForAll[{Typed[fuel, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]]},
					Implies[Length[v[["list"]]] + 1 < 9223372036854775808, Implies[Length[v[["list"]]] < fuel, Implies["partialSumsInRange"[v[["list"]]][0],
						Exists[{Typed[r, "Integer64"]}, vectorSum[fuel, v] == Typed["left"[r], "Integer64" | Failure] && r[["integer"]] == "integerListSum"[v[["list"]]]]]]]],
				vectors
			]
		],
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm["squaresComputes", vectors]],
			TypeTheoryTerm[
				ForAll[{Typed[top, NonNegativeIntegers], Typed[fuel, NonNegativeIntegers], Typed[n, "Integer64"]},
					Implies[n[["integer"]] == "integerOfNatural"[top], Implies[top top < 9223372036854775808, Implies[top < fuel,
						Exists[{Typed[a, "PackedArray"["Integer64", 1]]}, vectorSquares[fuel, n] == Typed["left"[a], "PackedArray"["Integer64", 1] | Failure] &&
							Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], a[["list"]]] == "integerSquares"[top]]]]]],
				vectors
			]
		]
	},
	{{}, ConstantArray[<|"quotientSoundness" -> "Proposition"|>, 3], True, True, True},
	TimeConstraint -> 300,
	TestID -> "The-vector-sum-is-the-total-and-the-squares-loop-gives-the-squares-for-all-fuel-above-its-rounds"
]


(* Matrices, the packed arrays of rank 2 typed code makes by Partition of a vector (Library/MachineArrays.wl): Length of
   one, a row and an element, each index counted as Part counts it, read as typed code computes them, with its leaves,
   "Range" for Partition by less than 1 and "PartRange" for a part that is not there. *)
partitionedEntry[data_List, k_Integer, i_Integer, j_Integer] := Partition[data, k][[i, j]]
partitionedRows[data_List, k_Integer] := Length[Partition[data, k]]
partitionedRow[data_List, k_Integer, i_Integer] := Partition[data, k][[i]]
partitionedProduct[data_List, k_Integer, v_List] := Module[{m = Partition[data, k], r = ConstantArray[0, Length[Partition[data, k]]], i = 1, j = 1, s = 0},
	While[i <= Length[m], s = 0; j = 1; While[j <= Length[v], s = s + m[[i, j]] v[[j]]; j = j + 1]; r[[i]] = s; i = i + 1];
	r
]

matrices = TypeTheoryEnvironment[vectors, Join[
	TypeTheoryFormalize[Typed[partitionedEntry, {"PackedArray"::["Integer64", 1], "Integer64", "Integer64", "Integer64"} -> "Integer64"], machine],
	TypeTheoryFormalize[Typed[partitionedRows, {"PackedArray"::["Integer64", 1], "Integer64"} -> "Integer64"], machine],
	TypeTheoryFormalize[Typed[partitionedRow, {"PackedArray"::["Integer64", 1], "Integer64", "Integer64"} -> "PackedArray"::["Integer64", 1]], machine],
	TypeTheoryFormalize[Typed[partitionedProduct, {"PackedArray"::["Integer64", 1], "Integer64", "PackedArray"::["Integer64", 1]} -> "PackedArray"::["Integer64", 1]], machine]
]]

(* a function of the squares of 1 to n, with machine integers bound by name *)
SetAttributes[withSquares, HoldRest]
withSquares[n_Integer, body_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm[
	"confirmBind"["machineResult"[n], Typed[size, "Integer64"] |-> "confirmBind"[vectorSquares[20, size], Typed[a, "PackedArray"["Integer64", 1]] |-> body]],
	matrices
]]]

VerificationTest[
	{
		withSquares[5, "confirmBind"["machineResult"[2], Typed[k, "Integer64"] |-> "confirmBind"["machineResult"[2], Typed[i, "Integer64"] |-> "confirmBind"["machineResult"[1], Typed[j, "Integer64"] |-> partitionedEntry[a, k, i, j]]]]],
		withSquares[5, "confirmBind"["machineResult"[2], Typed[k, "Integer64"] |-> partitionedRows[a, k]]],
		withSquares[5, "confirmBind"["machineResult"[2], Typed[k, "Integer64"] |-> "confirmBind"["machineResult"[-1], Typed[i, "Integer64"] |-> partitionedRow[a, k, i]]]],
		withSquares[6, "confirmBind"["machineResult"[3], Typed[k, "Integer64"] |-> "confirmBind"["machineResult"[3], Typed[three, "Integer64"] |->
			"confirmBind"[vectorSquares[20, three], Typed[v, "PackedArray"["Integer64", 1]] |-> partitionedProduct[30, a, k, v]]]]],
		{
			withSquares[5, "confirmBind"["machineResult"[0], Typed[k, "Integer64"] |-> partitionedRows[a, k]]],
			withSquares[5, "confirmBind"["machineResult"[2], Typed[k, "Integer64"] |-> "confirmBind"["machineResult"[3], Typed[i, "Integer64"] |-> "confirmBind"["machineResult"[1], Typed[j, "Integer64"] |-> partitionedEntry[a, k, i, j]]]]],
			withSquares[5, "confirmBind"["machineResult"[2], Typed[k, "Integer64"] |-> "confirmBind"["machineResult"[0], Typed[i, "Integer64"] |-> partitionedRow[a, k, i]]]]
		}
	},
	{
		partitionedEntry[vectorSquares[5], 2, 2, 1],
		partitionedRows[vectorSquares[5], 2],
		partitionedRow[vectorSquares[5], 2, -1],
		partitionedProduct[vectorSquares[6], 3, vectorSquares[3]],
		{Failure["Range", <||>], Failure["PartRange", <||>], Failure["PartRange", <||>]}
	},
	TestID -> "Functions-of-matrices-compute-what-the-evaluator-computes-and-leave-where-typed-code-does"
]

(* The theorem of the matrices: partitionedProduct, Partition and then two loops over m[[i, j]] v[[j]], gives the vector
   whose integers are the library's "matrixVectorProduct", where Partition gives a matrix, the vector is as long as a
   row, the counters stay machine integers, the fuel is above either loop's rounds and no product or partial sum leaves.
   The inner loop is the machine's dot product of a row with the vector, "integerListDotTotal"; the outer one runs it
   for each row with the function's whole fuel and sets the row's part of r, so its recursor is named, productRounds,
   with the rounds left counted down and the inner fuel fixed. Each loop has a round, a stop and an invariant, as the
   vectors' do; the library's "rowsDotTotalsOfSums" gives the exact sums. *)
matrices = vectorDeclare[matrices, TypeTheoryDefinition["productRounds", Typed[Function[{Typed[fuel, NonNegativeIntegers], Typed[m4, "PackedArray"["Integer64", 2]], Typed[v3, "PackedArray"["Integer64", 1]], Typed[roundsLeft, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[j, NonNegativeIntegers]}, "Integer64" -> "Integer64" -> "PackedArray"["Integer64", 1] -> "Integer64" -> CartesianProductType["Integer64", CartesianProductType["Integer64", CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]] | Failure], Function[{Typed[s8, "Integer64"], Typed[j7, "Integer64"], Typed[r5, "PackedArray"["Integer64", 1]], Typed[i6, "Integer64"]}, Typed["right"[Failure["OutOfFuel", Association[]]], CartesianProductType["Integer64", CartesianProductType["Integer64", CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]] | Failure]], Function[{Typed[fuelLeft, NonNegativeIntegers], Typed[loop, "Integer64" -> "Integer64" -> "PackedArray"["Integer64", 1] -> "Integer64" -> CartesianProductType["Integer64", CartesianProductType["Integer64", CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]] | Failure]}, Function[{Typed[s8, "Integer64"], Typed[j7, "Integer64"], Typed[r5, "PackedArray"["Integer64", 1]], Typed[i6, "Integer64"]}, "machineIf"["integerLessEqualQ"[i6[["integer"]], "matrixLength"[m4][["integer"]]], "confirmBind"["machineResult"[0], Function[{Typed[s8, "Integer64"]}, "confirmBind"["machineResult"[1], Function[{Typed[j7, "Integer64"]}, "confirmBind"["While[partitionedProduct, 2]"[fuel, v3, m4, i6, s8, j7], Function[{Typed[state2, CartesianProductType["Integer64", "Integer64"]]}, "confirmBind"["arraySetPart"[r5, i6[["integer"]], state2[["first"]]], Function[{Typed[setPart1, "PackedArray"["Integer64", 1]]}, "confirmBind"["machinePlus"[i6[["integer"]], 1], Function[{Typed[t34, "Integer64"]}, loop[state2[["first"]], state2[["second"]], setPart1, t34]]]]]]]]]]], Typed["left"["pair"[s8, "pair"[j7, "pair"[r5, i6]]]], CartesianProductType["Integer64", CartesianProductType["Integer64", CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]] | Failure]]]], roundsLeft]], NonNegativeIntegers -> "PackedArray"["Integer64", 2] -> "PackedArray"["Integer64", 1] -> NonNegativeIntegers -> "Integer64" -> "Integer64" -> "PackedArray"["Integer64", 1] -> "Integer64" -> CartesianProductType["Integer64", CartesianProductType["Integer64", CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]] | Failure]]]

With[{state = CartesianProductType["Integer64", CartesianProductType["Integer64", CartesianProductType["PackedArray"["Integer64", 1], "Integer64"]]]}, With[{
		upper = 9223372036854775808,
		zero = Typed["subtype"["integerOfNatural"[0], "naturalInteger64Range"[0, "zeroBound"]], "Integer64"],
		one = Typed["subtype"["integerOfNatural"[1], "naturalInteger64Range"[1, "oneBound"]], "Integer64"],
		listOfState = Function[{Typed[st, state]}, Typed["left"[st[["second"]][["second"]][["first"]][["list"]]], {"Integer64"} | Failure]]
	},
	matrices = vectorTheorem[matrices, "lengthOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[pre, {A}], Typed[rest, {A}]}, Implies[l == Join[pre, rest], Length[l] == Length[pre] + Length[rest]]],
		{"Introduce"[A, l, pre, rest, e], "Rewrite"[e], "Exact"["lengthJoin"[pre, rest]]}
	];
	matrices = vectorTheorem[matrices, "innerRound",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]], Typed[m, "PackedArray"["Integer64", 2]], Typed[i, "Integer64"], Typed[s, "Integer64"], Typed[j, "Integer64"],
				Typed[preRows, {{"Integer64"}}], Typed[row, {"Integer64"}], Typed[restRows, {{"Integer64"}}], Typed[pre, {"Integer64"}], Typed[x, "Integer64"], Typed[rest, {"Integer64"}],
				Typed[preV, {"Integer64"}], Typed[y, "Integer64"], Typed[restV, {"Integer64"}],
				Typed[e1, m[["rows"]] == Join[preRows, Prepend[row][restRows]]], Typed[hi, i[["integer"]] == "integerOfNatural"[Length[preRows] + 1]],
				Typed[e2, row == Join[pre, Prepend[x][rest]]], Typed[e3, v[["list"]] == Join[preV, Prepend[y][restV]]], Typed[hl, Length[preV] == Length[pre]],
				Typed[hj, j[["integer"]] == "integerOfNatural"[Length[preV] + 1]], Typed[h2, (Length[preV] + 1) + 1 < upper]},
			"While[partitionedProduct, 2]"[f + 1, v, m, i, s, j] == "confirmBind"["machineTimes"[x[["integer"]], y[["integer"]]], Function[{Typed[p, "Integer64"]},
				"confirmBind"["machinePlus"[s[["integer"]], p[["integer"]]], Function[{Typed[u, "Integer64"]},
					"While[partitionedProduct, 2]"[f, v, m, i, u, "subtype"["integerOfNatural"[(Length[preV] + 1) + 1], "naturalInteger64Range"[(Length[preV] + 1) + 1, h2]]]]]]]],
		{"Introduce"[f, v, m, i, s, j, preRows, row, restRows, pre, x, rest, preV, y, restV, e1, hi, e2, e3, hl, hj, h2],
			"RewriteRepeated"["While[partitionedProduct, 2]"], "Rewrite"["arrayLengthInteger"["Integer64", v]], "Rewrite"[hj], "Rewrite"[hi],
			"Rewrite"["integerLessEqualQOfNatural"[Length[preV] + 1, Length[v[["list"]]], "lengthOfSplit"["Integer64", v[["list"]], preV, y, restV, e3]]],
			"Rewrite"["matrixPartOfJoin"["Integer64", m, preRows, row, restRows, pre, x, rest, Length[preV], e1, e2, hl]],
			"Rewrite"["arrayPartOfJoin"["Integer64", v, preV, y, restV, e3]],
			"Rewrite"["machinePlusOfNatural"[Length[preV] + 1, 1, h2]],
			"Reflexivity"}
	];
	matrices = vectorTheorem[matrices, "innerStop",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[v, "PackedArray"["Integer64", 1]], Typed[m, "PackedArray"["Integer64", 2]], Typed[i, "Integer64"], Typed[s, "Integer64"], Typed[j, "Integer64"],
				Typed[n, NonNegativeIntegers], Typed[hj, j[["integer"]] == "integerOfNatural"[n + 1]], Typed[hle, Not[n + 1 <= Length[v[["list"]]]]]},
			"While[partitionedProduct, 2]"[f + 1, v, m, i, s, j] == Typed["left"["pair"[s, j]], CartesianProductType["Integer64", "Integer64"] | Failure]],
		{"Introduce"[f, v, m, i, s, j, n, hj, hle], "RewriteRepeated"["While[partitionedProduct, 2]"], "Rewrite"["arrayLengthInteger"["Integer64", v]], "Rewrite"[hj],
			"Rewrite"["integerLessEqualQNotOfNatural"[n + 1, Length[v[["list"]]], hle]], "Reflexivity"}
	];
	matrices = vectorTheorem[matrices, "innerInvariant",
		ForAll[{Typed[v, "PackedArray"["Integer64", 1]], Typed[m, "PackedArray"["Integer64", 2]], Typed[i, "Integer64"],
				Typed[preRows, {{"Integer64"}}], Typed[row, {"Integer64"}], Typed[restRows, {{"Integer64"}}]},
			Implies[m[["rows"]] == Join[preRows, Prepend[row][restRows]], Implies[i[["integer"]] == "integerOfNatural"[Length[preRows] + 1],
				Implies[Length[row] == Length[v[["list"]]], Implies[Length[v[["list"]]] + 1 < upper,
					ForAll[{Typed[rest, {"Integer64"}], Typed[pre, {"Integer64"}], Typed[preV, {"Integer64"}], Typed[restV, {"Integer64"}], Typed[fuel, NonNegativeIntegers], Typed[s, "Integer64"], Typed[j, "Integer64"]},
						Implies[row == Join[pre, rest], Implies[v[["list"]] == Join[preV, restV], Implies[Length[preV] == Length[pre],
							Implies[j[["integer"]] == "integerOfNatural"[Length[preV] + 1], Implies[Length[restV] < fuel,
								"confirmBind"["While[partitionedProduct, 2]"[fuel, v, m, i, s, j], Function[{Typed[st, CartesianProductType["Integer64", "Integer64"]]}, Typed["left"[st[["first"]]], "Integer64" | Failure]]] ==
									"integerListDotTotal"[rest, restV, s]]]]]]]]]]]],
		{"Introduce"[v, m, i, preRows, row, restRows, e1, hi, hrow, bound, rest], "Induction"[rest],
			(* nothing left of the row: nothing is left of the vector either, and the loop stops *)
			"Introduce"[pre, preV, restV, fuel, s, j, e2, e3, hl, hj, hf],
			"Have"[l2, Length[row] == Length[pre]], "Exact"["lengthOfJoin"["Integer64", row, pre, Typed[{}, {"Integer64"}], e2]],
			"Have"[l3, Length[v[["list"]]] == Length[preV] + Length[restV]], "Exact"["lengthOfJoin"["Integer64", v[["list"]], preV, restV, e3]],
			"Generalize"[hf], "Generalize"[l3], "Generalize"[e3], "Cases"[restV],
			"Introduce"[e3, l3, hf], "Generalize"[hf], "Cases"[fuel],
			"Introduce"[hf], "Exact"["falseElimination"["notLessZero"[0, hf]]],
			"Introduce"[f, hf],
			"Rewrite"["innerStop"[f, v, m, i, s, j, Length[preV], hj, "lengthOfWhole"["Integer64", v[["list"]], preV, e3]]], "Reflexivity",
			"Introduce"[y, ys, e3, l3, hf], "Have"[l4, Length[v[["list"]]] == Length[preV] + (Length[ys] + 1)], "Exact"[l3],
			"Have"[contradiction, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[contradiction]],
			(* an element left of the row: one of the vector too, one round, then the hypothesis at the next place *)
			"Introduce"[x, xs, ih, pre, preV, restV, fuel, s, j, e2, e3, hl, hj, hf],
			"Have"[l2, Length[row] == Length[pre] + (Length[xs] + 1)], "Exact"["lengthOfJoin"["Integer64", row, pre, Prepend[x][xs], e2]],
			"Have"[l3, Length[v[["list"]]] == Length[preV] + Length[restV]], "Exact"["lengthOfJoin"["Integer64", v[["list"]], preV, restV, e3]],
			"Generalize"[hf], "Generalize"[l3], "Generalize"[e3], "Cases"[restV],
			"Introduce"[e3, l3, hf], "Have"[l4, Length[v[["list"]]] == Length[preV]], "Exact"[l3],
			"Have"[contradiction, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[contradiction]],
			"Introduce"[y, ys, e3, l3, hf], "Generalize"[hf], "Cases"[fuel],
			"Introduce"[hf], "Exact"["falseElimination"["notLessZero"[Length[ys] + 1, hf]]],
			"Introduce"[f, hf],
			"Have"[h2, (Length[preV] + 1) + 1 < upper], "Exact"["roundBound"[Length[preV], Length[v[["list"]]], upper, "lengthOfSplit"["Integer64", v[["list"]], preV, y, ys, e3], bound]],
			"Rewrite"["innerRound"[f, v, m, i, s, j, preRows, row, restRows, pre, x, xs, preV, y, ys, e1, hi, e2, e3, hl, hj, h2]],
			"Apply"["confirmBindThen"["Integer64", CartesianProductType["Integer64", "Integer64"], "Integer64", "machineTimes"[x[["integer"]], y[["integer"]]],
				Function[{Typed[p, "Integer64"]}, "confirmBind"["machinePlus"[s[["integer"]], p[["integer"]]], Function[{Typed[u, "Integer64"]},
					"While[partitionedProduct, 2]"[f, v, m, i, u, "subtype"["integerOfNatural"[(Length[preV] + 1) + 1], "naturalInteger64Range"[(Length[preV] + 1) + 1, h2]]]]]],
				Function[{Typed[st, CartesianProductType["Integer64", "Integer64"]]}, Typed["left"[st[["first"]]], "Integer64" | Failure]],
				Function[{Typed[p, "Integer64"]}, "confirmBind"["machinePlus"[s[["integer"]], p[["integer"]]], Function[{Typed[u, "Integer64"]}, "integerListDotTotal"[xs, ys, u]]]]]],
			"Introduce"[p],
			"Apply"["confirmBindThen"["Integer64", CartesianProductType["Integer64", "Integer64"], "Integer64", "machinePlus"[s[["integer"]], p[["integer"]]],
				Function[{Typed[u, "Integer64"]}, "While[partitionedProduct, 2]"[f, v, m, i, u, "subtype"["integerOfNatural"[(Length[preV] + 1) + 1], "naturalInteger64Range"[(Length[preV] + 1) + 1, h2]]]],
				Function[{Typed[st, CartesianProductType["Integer64", "Integer64"]]}, Typed["left"[st[["first"]]], "Integer64" | Failure]],
				Function[{Typed[u, "Integer64"]}, "integerListDotTotal"[xs, ys, u]]]],
			"Introduce"[u],
			"Apply"[ih[Join[pre, Prepend[x][{}]], Join[preV, Prepend[y][{}]], ys, f, u, "subtype"["integerOfNatural"[(Length[preV] + 1) + 1], "naturalInteger64Range"[(Length[preV] + 1) + 1, h2]]]],
			"Exact"["equalityTransitivity"[e2, "equalitySymmetry"["joinAssociativity"[pre, Prepend[x][{}], xs]]]],
			"Exact"["equalityTransitivity"[e3, "equalitySymmetry"["joinAssociativity"[preV, Prepend[y][{}], ys]]]],
			"Exact"["equalityTransitivity"["lengthJoin"[preV, Prepend[y][{}]], "equalityTransitivity"["equalityCongruence"[Function[{Typed[k, NonNegativeIntegers]}, k + 1], hl], "equalitySymmetry"["lengthJoin"[pre, Prepend[x][{}]]]]]],
			"Exact"["equalityCongruence"[Function[{Typed[k, NonNegativeIntegers]}, "integerOfNatural"[k + 1]], "equalitySymmetry"["lengthJoin"[preV, Prepend[y][{}]]]]],
			"Exact"["lessOfSuccessors"[Length[ys], f, hf]]}
	];
	matrices = vectorTheorem[matrices, "outerStop",
		ForAll[{Typed[fuel, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[m, "PackedArray"["Integer64", 2]], Typed[v, "PackedArray"["Integer64", 1]],
				Typed[s, "Integer64"], Typed[j, "Integer64"], Typed[r, "PackedArray"["Integer64", 1]], Typed[i, "Integer64"], Typed[n, NonNegativeIntegers],
				Typed[hi, i[["integer"]] == "integerOfNatural"[n + 1]], Typed[hle, Not[n + 1 <= Length[m[["rows"]]]]]},
			"productRounds"[fuel, m, v, k + 1][s, j, r, i] == Typed["left"["pair"[s, "pair"[j, "pair"[r, i]]]], state | Failure]],
		{"Introduce"[fuel, k, m, v, s, j, r, i, n, hi, hle], "RewriteRepeated"["productRounds"], "Rewrite"["matrixLengthInteger"["Integer64", m]], "Rewrite"[hi],
			"Rewrite"["integerLessEqualQNotOfNatural"[n + 1, Length[m[["rows"]]], hle]], "Reflexivity"}
	];
	matrices = vectorTheorem[matrices, "outerInvariant",
		ForAll[{Typed[fuel, NonNegativeIntegers], Typed[m, "PackedArray"["Integer64", 2]], Typed[v, "PackedArray"["Integer64", 1]]},
			Implies[Length[v[["list"]]] == m[["columns"]], Implies[Length[v[["list"]]] + 1 < upper, Implies[Length[m[["rows"]]] + 1 < upper, Implies[Length[v[["list"]]] < fuel,
				ForAll[{Typed[restRows, {{"Integer64"}}], Typed[preRows, {{"Integer64"}}], Typed[done, {"Integer64"}], Typed[rest0, {"Integer64"}], Typed[k, NonNegativeIntegers],
						Typed[s, "Integer64"], Typed[j, "Integer64"], Typed[r, "PackedArray"["Integer64", 1]], Typed[i, "Integer64"]},
					Implies[m[["rows"]] == Join[preRows, restRows], Implies[r[["list"]] == Join[done, rest0], Implies[Length[done] == Length[preRows],
						Implies[Length[rest0] == Length[restRows], Implies[i[["integer"]] == "integerOfNatural"[Length[done] + 1], Implies[Length[restRows] < k,
							"confirmBind"["productRounds"[fuel, m, v, k][s, j, r, i], listOfState] ==
								"confirmBind"["rowsDotTotals"[restRows, v[["list"]]], Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Join[done, ds]], {"Integer64"} | Failure]]]]]]]]]]]]]]],
		{"Introduce"[fuel, m, v, hcols, boundV, boundR, hF, restRows], "Induction"[restRows],
			(* no row left: the loop stops, and r is done *)
			"Introduce"[preRows, done, rest0, k, s, j, r, i, e1, er, hd, hr0, hi, hk],
			"Have"[whole, Not[Length[done] + 1 <= Length[m[["rows"]]]]], "Rewrite"[hd], "Exact"["lengthOfWhole"[{"Integer64"}, m[["rows"]], preRows, e1]],
			"Generalize"[hk], "Cases"[k],
			"Introduce"[hk], "Exact"["falseElimination"["notLessZero"[0, hk]]],
			"Introduce"[k2, hk], "Rewrite"["outerStop"[fuel, k2, m, v, s, j, r, i, Length[done], hi, whole]],
			"Generalize"[er], "Generalize"[hr0], "Cases"[rest0],
			"Introduce"[hr0, er], "Exact"["equalityCongruence"[Function[{Typed[l, {"Integer64"}]}, Typed["left"[l], {"Integer64"} | Failure]], er]],
			"Introduce"[y, ys, hr0, er], "Exact"["falseElimination"["successorNotZero"[Length[ys]][hr0]]],
			(* a row left: its dot product by the inner loop, its part of r set, then the hypothesis at the next row *)
			"Introduce"[row, rest, ih, preRows, done, rest0, k, s, j, r, i, e1, er, hd, hr0, hi, hk],
			"Have"[split, Length[preRows] + 1 <= Length[m[["rows"]]]], "Exact"["lengthOfSplit"[{"Integer64"}, m[["rows"]], preRows, row, rest, e1]],
			"Have"[less, Length[done] + 1 <= Length[m[["rows"]]]], "Rewrite"[hd], "Exact"[split],
			"Have"[h2, (Length[done] + 1) + 1 < upper], "Exact"["roundBound"[Length[done], Length[m[["rows"]]], upper, less, boundR]],
			"Have"[hi2, i[["integer"]] == "integerOfNatural"[Length[preRows] + 1]],
			"Exact"["equalityTransitivity"[hi, "equalityCongruence"[Function[{Typed[c, NonNegativeIntegers]}, "integerOfNatural"[c + 1]], hd]]],
			"Have"[hrow, Length[row] == Length[v[["list"]]]],
			"Exact"["equalityTransitivity"[
				"rowsOfLengthOfJoin"["Integer64", m[["columns"]], row, rest, preRows,
					"equalitySubstitution"[e1, m[["proof"]][["right"]][["right"]][["right"]], P -> Function[{Typed[l, {{"Integer64"}}]}, "rowsOfLength"[l, m[["columns"]]]]]],
				"equalitySymmetry"[hcols]]],
			"Generalize"[hk], "Generalize"[er], "Generalize"[hr0], "Cases"[rest0],
			"Introduce"[hr0, er, hk], "Exact"["falseElimination"["successorNotZero"[Length[rest]]["equalitySymmetry"[hr0]]]],
			"Introduce"[y, ys, hr0, er, hk], "Generalize"[hk], "Cases"[k],
			"Introduce"[hk], "Exact"["falseElimination"["notLessZero"[Length[rest] + 1, hk]]],
			"Introduce"[k2, hk],
			"RewriteRepeated"["productRounds"], "Rewrite"["matrixLengthInteger"["Integer64", m]], "Rewrite"[hi],
			"Rewrite"["integerLessEqualQOfNatural"[Length[done] + 1, Length[m[["rows"]]], less]],
			"Apply"["confirmBindFirstThen"["Integer64", "Integer64", state, {"Integer64"}, {"Integer64"},
				"While[partitionedProduct, 2]"[fuel, v, m, i, zero, one],
				"integerListDotTotal"[row, v[["list"]], zero],
				Function[{Typed[st, CartesianProductType["Integer64", "Integer64"]]}, "confirmBind"["arraySetPart"[r, "integerOfNatural"[Length[done] + 1], st[["first"]]], Function[{Typed[r2, "PackedArray"["Integer64", 1]]},
					"confirmBind"["machinePlus"["integerOfNatural"[Length[done] + 1], 1], Function[{Typed[i2, "Integer64"]}, "productRounds"[fuel, m, v, k2][st[["first"]], st[["second"]], r2, i2]]]]]],
				listOfState,
				Function[{Typed[d, "Integer64"]}, "confirmBind"["rowsDotTotals"[rest, v[["list"]]], Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Prepend[d][ds]], {"Integer64"} | Failure]]]],
				Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Join[done, ds]], {"Integer64"} | Failure]]]],
			"Exact"["innerInvariant"[v, m, i, preRows, row, rest, e1, hi2, hrow, boundV, row, Typed[{}, {"Integer64"}], Typed[{}, {"Integer64"}], v[["list"]], fuel, zero, one,
				"equalityReflexivity"[row], "equalityReflexivity"[v[["list"]]], "equalityReflexivity"[0], "equalityReflexivity"["integerOfNatural"[1]], hF]],
			"Introduce"[t],
			"Have"[hR, "arrayLengthRange"["Integer64"][Join[done, Prepend[t[["first"]]][ys]]]], "Exact"["arraySetPartRange"["Integer64", r, done, y, t[["first"]], ys, er]],
			"Rewrite"["arraySetPartOfJoinInRange"["Integer64", r, done, y, t[["first"]], ys, hR, er]],
			"Rewrite"["machinePlusOfNatural"[Length[done] + 1, 1, h2]],
			"Exact"["equalityTransitivity"[
				ih[Join[preRows, Prepend[row][{}]], Join[done, Prepend[t[["first"]]][{}]], ys, k2, t[["first"]], t[["second"]],
					"subtype"[Join[done, Prepend[t[["first"]]][ys]], hR], "subtype"["integerOfNatural"[(Length[done] + 1) + 1], "naturalInteger64Range"[(Length[done] + 1) + 1, h2]],
					"equalityTransitivity"[e1, "equalitySymmetry"["joinAssociativity"[preRows, Prepend[row][{}], rest]]],
					"equalitySymmetry"["joinAssociativity"[done, Prepend[t[["first"]]][{}], ys]],
					"equalityTransitivity"["lengthJoin"[done, Prepend[t[["first"]]][{}]],
						"equalityTransitivity"["equalityCongruence"[Function[{Typed[c, NonNegativeIntegers]}, c + 1], hd], "equalitySymmetry"["lengthJoin"[preRows, Prepend[row][{}]]]]],
					"successorInjectivity"[hr0],
					"equalityCongruence"[Function[{Typed[c, NonNegativeIntegers]}, "integerOfNatural"[c + 1]], "equalitySymmetry"["lengthJoin"[done, Prepend[t[["first"]]][{}]]]],
					"lessOfSuccessors"[Length[rest], k2, hk]],
				"equalityTransitivity"[
					"confirmBindCongruence"[{"Integer64"}, {"Integer64"}, "rowsDotTotals"[rest, v[["list"]]],
						Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Join[Join[done, Prepend[t[["first"]]][{}]], ds]], {"Integer64"} | Failure]],
						Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Join[done, Prepend[t[["first"]]][ds]]], {"Integer64"} | Failure]],
						Function[{Typed[ds, {"Integer64"}]}, "equalityCongruence"[Function[{Typed[l, {"Integer64"}]}, Typed["left"[l], {"Integer64"} | Failure]], "joinAssociativity"[done, Prepend[t[["first"]]][{}], ds]]]],
					"equalitySymmetry"["confirmBindAssociativity"[{"Integer64"}, {"Integer64"}, {"Integer64"}, "rowsDotTotals"[rest, v[["list"]]],
						Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Prepend[t[["first"]]][ds]], {"Integer64"} | Failure]],
						Function[{Typed[ds, {"Integer64"}]}, Typed["left"[Join[done, ds]], {"Integer64"} | Failure]]]]]]]}
	];
	matrices = vectorTheorem[matrices, "partitionedProductComputes",
		ForAll[{Typed[fuel, NonNegativeIntegers], Typed[data, "PackedArray"["Integer64", 1]], Typed[k, "Integer64"], Typed[v, "PackedArray"["Integer64", 1]], Typed[m, "PackedArray"["Integer64", 2]]},
			Implies["matrixOfPartition"[data, k[["integer"]]] == Typed["left"[m], "PackedArray"["Integer64", 2] | Failure],
				Implies[Length[v[["list"]]] == m[["columns"]], Implies[Length[m[["rows"]]] + 1 < upper, Implies[Length[v[["list"]]] + 1 < upper,
					Implies[Length[m[["rows"]]] < fuel, Implies[Length[v[["list"]]] < fuel, Implies["rowsDotSumsInRange"[m[["rows"]], v[["list"]]],
						Exists[{Typed[r, "PackedArray"["Integer64", 1]]}, partitionedProduct[fuel, data, k, v] == Typed["left"[r], "PackedArray"["Integer64", 1] | Failure] &&
							Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], r[["list"]]] == "matrixVectorProduct"[m, v]]]]]]]]]],
		{"Introduce"[fuel, data, k, v, m, hm, hcols, boundR, boundV, hR, hV, sums],
			"Have"[rowsBound, Length[m[["rows"]]] < upper], "LinearArithmetic",
			"Cases"["arrayConstantOfNatural"["Integer64", zero, Length[m[["rows"]]], rowsBound]], "Introduce"[a, ha],
			"Cases"["rowsDotTotalsOfSums"[m[["rows"]], v[["list"]], sums]], "Introduce"[ds, hds],
			"Have"[inv, "confirmBind"["productRounds"[fuel, m, v, fuel][zero, one, a, one], listOfState] ==
				"confirmBind"["rowsDotTotals"[m[["rows"]], v[["list"]]], Function[{Typed[es, {"Integer64"}]}, Typed["left"[Join[Typed[{}, {"Integer64"}], es]], {"Integer64"} | Failure]]]],
			"Exact"["outerInvariant"[fuel, m, v, hcols, boundV, boundR, hV, m[["rows"]], Typed[{}, {{"Integer64"}}], Typed[{}, {"Integer64"}], a[["list"]], fuel, zero, one, a, one,
				"equalityReflexivity"[m[["rows"]]], "equalityReflexivity"[a[["list"]]], "equalityReflexivity"[0],
				"equalityTransitivity"["equalityCongruence"[Function[{Typed[l, {"Integer64"}]}, Length[l]], ha[["right"]]], "listConstantLength"["Integer64", zero, Length[m[["rows"]]]]],
				"equalityReflexivity"["integerOfNatural"[1]], hR]],
			"Rewrite"[hds[["left"]], "At" -> inv],
			"Change"[Exists[{Typed[r, "PackedArray"["Integer64", 1]]},
				"confirmBind"["matrixOfPartition"[data, k[["integer"]]], Function[{Typed[t3, "PackedArray"["Integer64", 2]]}, "confirmBind"["matrixOfPartition"[data, k[["integer"]]], Function[{Typed[t6, "PackedArray"["Integer64", 2]]},
					"confirmBind"["confirmBind"["machineResult"[0], Function[{Typed[element, "Integer64"]}, "arrayConstant"[element, "matrixLength"[t6][["integer"]]]]], Function[{Typed[t8, "PackedArray"["Integer64", 1]]},
						"confirmBind"["machineResult"[1], Function[{Typed[i6, "Integer64"]}, "confirmBind"["machineResult"[1], Function[{Typed[j7, "Integer64"]}, "confirmBind"["machineResult"[0], Function[{Typed[s8, "Integer64"]},
							"confirmBind"["While[partitionedProduct]"[fuel, t3, v, s8, j7, t8, i6], Function[{Typed[state1, state]}, Typed["left"[state1[["second"]][["second"]][["first"]]], "PackedArray"["Integer64", 1] | Failure]]]]]]]]]]]]]]] ==
						Typed["left"[r], "PackedArray"["Integer64", 1] | Failure] &&
					Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], r[["list"]]] == "matrixVectorProduct"[m, v]]],
			"Rewrite"[hm],
			"Rewrite"["machineResultInRange"[0, "naturalInteger64Range"[0, "zeroBound"]]],
			"Rewrite"["machineResultInRange"[1, "naturalInteger64Range"[1, "oneBound"]]],
			"Change"[Exists[{Typed[r, "PackedArray"["Integer64", 1]]},
				"confirmBind"["arrayConstant"[zero, "integerOfNatural"[Length[m[["rows"]]]]], Function[{Typed[t8, "PackedArray"["Integer64", 1]]},
					"confirmBind"["While[partitionedProduct]"[fuel, m, v, zero, one, t8, one], Function[{Typed[state1, state]}, Typed["left"[state1[["second"]][["second"]][["first"]]], "PackedArray"["Integer64", 1] | Failure]]]]] ==
						Typed["left"[r], "PackedArray"["Integer64", 1] | Failure] &&
					Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], r[["list"]]] == "matrixVectorProduct"[m, v]]],
			"Rewrite"[ha[["left"]]],
			"Generalize"[inv],
			"Change"[Implies["confirmBind"["While[partitionedProduct]"[fuel, m, v, zero, one, a, one], listOfState] == Typed["left"[ds], {"Integer64"} | Failure],
				Exists[{Typed[r, "PackedArray"["Integer64", 1]]},
					"confirmBind"["While[partitionedProduct]"[fuel, m, v, zero, one, a, one], Function[{Typed[state1, state]}, Typed["left"[state1[["second"]][["second"]][["first"]]], "PackedArray"["Integer64", 1] | Failure]]] ==
						Typed["left"[r], "PackedArray"["Integer64", 1] | Failure] &&
					Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], r[["list"]]] == "matrixVectorProduct"[m, v]]]],
			"Cases"["While[partitionedProduct]"[fuel, m, v, zero, one, a, one]],
			"Introduce"[st, inv],
			"Exact"["existsIntroduction"[st[["second"]][["second"]][["first"]], "andIntroduction"[
				"equalityReflexivity"[Typed["left"[st[["second"]][["second"]][["first"]]], "PackedArray"["Integer64", 1] | Failure]],
				"equalityTransitivity"["equalityCongruence"[Function[{Typed[l, {"Integer64"}]}, Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], l]],
					"leftInjective"[{"Integer64"}, Failure, st[["second"]][["second"]][["first"]][["list"]], ds, inv]], hds[["right"]]]]]],
			"Introduce"[f, inv], "Exact"["falseElimination"["rightNotLeft"[{"Integer64"}, Failure, ds, f, inv]]]}
	];
]]

VerificationTest[
	{
		vectorFailures,
		TypeTheoryAxiomClosure[TypeTheoryTerm["partitionedProductComputes", matrices]],
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm["partitionedProductComputes", matrices]],
			TypeTheoryTerm[
				ForAll[{Typed[fuel, NonNegativeIntegers], Typed[data, "PackedArray"["Integer64", 1]], Typed[k, "Integer64"], Typed[v, "PackedArray"["Integer64", 1]], Typed[m, "PackedArray"["Integer64", 2]]},
					Implies["matrixOfPartition"[data, k[["integer"]]] == Typed["left"[m], "PackedArray"["Integer64", 2] | Failure],
						Implies[Length[v[["list"]]] == m[["columns"]], Implies[Length[m[["rows"]]] + 1 < 9223372036854775808, Implies[Length[v[["list"]]] + 1 < 9223372036854775808,
							Implies[Length[m[["rows"]]] < fuel, Implies[Length[v[["list"]]] < fuel, Implies["rowsDotSumsInRange"[m[["rows"]], v[["list"]]],
								Exists[{Typed[r, "PackedArray"["Integer64", 1]]}, partitionedProduct[fuel, data, k, v] == Typed["left"[r], "PackedArray"["Integer64", 1] | Failure] &&
									Map[Function[{Typed[z, "Integer64"]}, z[["integer"]]], r[["list"]]] == "matrixVectorProduct"[m, v]]]]]]]]]],
				matrices
			]
		]
	},
	{{}, <|"quotientSoundness" -> "Proposition"|>, True},
	TimeConstraint -> 300,
	TestID -> "The-matrix-vector-product-by-two-loops-computes-the-librarys-product"
]


(* the machine reals once, outside any test's time limit: where no saved environment is current, a fresh checkout or a
   changed kernel, they are built and checked from their declarations, which takes minutes *)
machineReals = TypeTheoryEnvironment["MachineReals"]

(* Typed code on machine reals, in TypeTheoryEnvironment["MachineReals"]. An argument x_Real is a machine real, a
   rational that binary64 represents, and each step is the compiler's: a sum, a product and a difference are the results
   of the exact ones; a quotient is x times the rounded 1/y, as the compiler writes it, Power[y, -1] and a product; a
   machine integer in an operation with a real is made a real first; an order of reals is the rationals', Equal within
   its tolerance; Round, Floor, Abs, Sqrt and N are the library's. Each function gives the Wolfram Language's own
   machine real, to the last bit, with the rounding computed by NormalForm's "Implementations", and leaves where compiled
   code declines. In "Machine", which has no reals, such code is a Failure that names the environment. *)
realHalf[x_Real] := x / 2.
realMix[x_Real, n_Integer] := (x + n) 2.5 - x / 3.
realWhole[x_Real, y_Real] := If[x < y && x != 0., Round[x], Floor[y]]
realRoot[x_Real] := Sqrt[Abs[x]] + N[2]
realNewton[x_Real] := Module[{y = 1., i = 0}, While[i < 5, y = (y + x / y) / 2.; i = i + 1]; y]

VerificationTest[
	Module[{reals, environment, exact, value, one, two, mixed, fueled},
		reals = machineReals;
		environment = TypeTheoryEnvironment[reals, Join[
			TypeTheoryFormalize[realHalf, reals], TypeTheoryFormalize[realMix, reals], TypeTheoryFormalize[realWhole, reals],
			TypeTheoryFormalize[realRoot, reals], TypeTheoryFormalize[realNewton, reals]
		]];
		exact[x_] := SetPrecision[x, Infinity];
		value[term_] := TypeTheoryExpression[NormalForm[term, "Implementations" -> True]];
		one[f_, x_] := With[{q = exact[x]}, value[TypeTheoryTerm["confirmBind"["real64Result"[Typed[q, Rationals]], f], environment]]];
		two[f_, x_, y_] := With[{p = exact[x], q = exact[y]},
			value[TypeTheoryTerm["confirmBind"["real64Result"[Typed[p, Rationals]], Function[{Typed[u, "Real64"]}, "confirmBind"["real64Result"[Typed[q, Rationals]], f[u]]]], environment]]];
		mixed[f_, x_, n_] := With[{p = exact[x]},
			value[TypeTheoryTerm["confirmBind"["real64Result"[Typed[p, Rationals]], Function[{Typed[u, "Real64"]}, "confirmBind"["machineResult"[n], f[u]]]], environment]]];
		fueled[f_, fuel_, x_] := With[{q = exact[x]}, value[TypeTheoryTerm["confirmBind"["real64Result"[Typed[q, Rationals]], f[fuel]], environment]]];
		{
			Head[environment],
			TypeTheoryFormalize[realHalf, reals],
			Map[Function[x, one[realHalf, x] === exact[realHalf[x]]], {0.3, -7.25, 1.*^300}],
			Map[Apply[Function[{x, n}, mixed[realMix, x, n] === exact[realMix[x, n]]]], {{0.1, 3}, {-2.5, -4}, {0.1, 9007199254740993}}],
			Map[Apply[Function[{x, y}, two[realWhole, x, y] === realWhole[x, y]]], {{2.5, 7.9}, {8.5, 7.9}, {0., 7.9}, {-3.5, -2.2}}],
			Map[Function[x, one[realRoot, x] === exact[realRoot[x]]], {-2., 0.2, 9.}],
			{fueled[realNewton, 6, 2.] === exact[realNewton[2.]], fueled[realNewton, 5, 2.]},
			(* half of a subnormal is below the smallest normal real; a whole number from 9*10^18 on *)
			{one[realHalf, 1.*^-320], two[realWhole, 9.5*^18, 9.9*^18]},
			TypeTheoryFormalize[realHalf, machine]["Tag"],
			(* by its name, "Machine" is the environment of the machine reals for code on reals *)
			TypeTheoryFormalize[realHalf, "Machine"] === TypeTheoryFormalize[realHalf, reals]
		}
	],
	{
		TypeTheoryEnvironment,
		{TypeTheoryDefinition[realHalf, Typed[
			Function[{Typed[x, "Real64"]}, "confirmBind"["real64Reciprocal"[Typed[2, Rationals]],
				Function[{Typed[WolframInstitute`TypeTheory`Compiled`t2, "Real64"]}, "real64Times"[x[["rational"]], WolframInstitute`TypeTheory`Compiled`t2[["rational"]]]]]],
			"Real64" -> ("Real64" | Failure)
		]]},
		ConstantArray[True, 3], ConstantArray[True, 3], ConstantArray[True, 4], ConstantArray[True, 3],
		{True, Failure["OutOfFuel", <||>]},
		{Failure["Underflow", <||>], Failure["IntegerOverflow", <||>]},
		"NoMachineReals",
		True
	},
	TimeConstraint -> 300,
	TestID -> "Typed-code-on-machine-reals-gives-the-Wolfram-Languages-reals"
]

(* a real to an integer power, a constant or a machine integer, is the library's "real64IntegerPower": Wolfram 15's
   order of the products, on bases where another order rounds differently, and the leaves of typed code on the final
   value only *)
realCube[x_Real] := x^3
realPower[x_Real, n_Integer] := x^n

VerificationTest[
	Module[{reals, environment, exact, value, cube, power},
		reals = machineReals;
		environment = TypeTheoryEnvironment[reals, Join[TypeTheoryFormalize[realCube, reals], TypeTheoryFormalize[realPower, reals]]];
		exact[x_] := SetPrecision[x, Infinity];
		value[term_] := TypeTheoryExpression[NormalForm[term, "Implementations" -> True]];
		cube[x_] := With[{q = exact[x]}, value[TypeTheoryTerm["confirmBind"["real64Result"[Typed[q, Rationals]], realCube], environment]]];
		power[x_, n_] := With[{q = exact[x]},
			value[TypeTheoryTerm["confirmBind"["real64Result"[Typed[q, Rationals]], Function[{Typed[u, "Real64"]}, "confirmBind"["machineResult"[n], realPower[u]]]], environment]]];
		{
			{FreeQ[TypeTheoryFormalize[realCube, reals], "real64IntegerPower"], FreeQ[TypeTheoryFormalize[realPower, reals], "real64IntegerPower"]},
			Map[Function[x, cube[x] === exact[realCube[x]]], {1.8595758754054015, -0.3, 1.*^100}],
			Map[Apply[Function[{x, n}, power[x, n] === exact[realPower[x, n]]]], {{1.8595758754054015, 6}, {1.8595758754054015, -21}, {1.3231998472169695, 1000}}],
			{cube[1.*^200], power[10., -400], power[0., 0]}
		}
	],
	{
		{False, False},
		ConstantArray[True, 3], ConstantArray[True, 3],
		{Failure["NotFinite", <||>], Failure["Underflow", <||>], Failure["Domain", <||>]}
	},
	TimeConstraint -> 300,
	TestID -> "Typed-code-raises-a-real-to-an-integer-power-as-Wolfram-15-does"
]

(* Vectors of machine reals, in TypeTheoryEnvironment["MachineReals"], with the definitions of the integers' vectors
   at "Real64": a dot product, a vector made by setting its parts, and Take. Their values are the evaluator's machine
   reals, to the last bit, and a part that is not there leaves. A function of real vectors is refused among the integers
   alone, and "Machine" by name formalizes it among the reals; typed code has no Total of reals. *)
realDot[u_List, v_List] := Module[{s = 0., i = 1}, While[i <= Length[u], s = s + u[[i]] v[[i]]; i = i + 1]; s]
realHalves[n_Integer] := Module[{a = ConstantArray[0., n], i = 1}, While[i <= n, a[[i]] = 0.5 i; i = i + 1]; a]
realHead[v_List, k_Integer] := Take[v, k]
realTotal[v_List] := Total[v]

realVectors = TypeTheoryEnvironment[machineReals, Join[
	TypeTheoryFormalize[Typed[realDot, {"PackedArray"::["Real64", 1], "PackedArray"::["Real64", 1]} -> "Real64"], "Machine"],
	TypeTheoryFormalize[realHalves, machineReals],
	TypeTheoryFormalize[Typed[realHead, {"PackedArray"::["MachineReal", 1], "MachineInteger"} -> "PackedArray"::["MachineReal", 1]], machineReals]
]]

SetAttributes[realVectorValue, HoldFirst]
realVectorValue[term_] := TypeTheoryExpression[NormalForm[TypeTheoryTerm[term, realVectors], "Implementations" -> True]]

VerificationTest[
	{
		TypeTheoryFormalize[Typed[realDot, {"PackedArray"::["Real64", 1], "PackedArray"::["Real64", 1]} -> "Real64"], machine]["Tag"],
		TypeTheoryFormalize[Typed[realTotal, {"PackedArray"::["Real64", 1]} -> "Real64"], machineReals]["Tag"],
		realVectorValue["confirmBind"["machineResult"[3], Typed[n, "Integer64"] |-> realHalves[10, n]]],
		realVectorValue["confirmBind"["machineResult"[3], Typed[n, "Integer64"] |-> "confirmBind"[realHalves[10, n], Typed[a, "PackedArray"["Real64", 1]] |-> realDot[10, a, a]]]],
		realVectorValue["confirmBind"["machineResult"[3], Typed[n, "Integer64"] |-> "confirmBind"[realHalves[10, n], Typed[a, "PackedArray"["Real64", 1]] |->
			"confirmBind"["machineResult"[2], Typed[k, "Integer64"] |-> realHead[a, k]]]]],
		realVectorValue["confirmBind"["machineResult"[3], Typed[n, "Integer64"] |-> "confirmBind"[realHalves[10, n], Typed[a, "PackedArray"["Real64", 1]] |->
			"confirmBind"["machineResult"[4], Typed[k, "Integer64"] |-> realHead[a, k]]]]]
	},
	{
		"NoMachineReals",
		"NoTypedEntry",
		SetPrecision[realHalves[3], Infinity],
		SetPrecision[realDot[realHalves[3], realHalves[3]], Infinity],
		SetPrecision[realHead[realHalves[3], 2], Infinity],
		Failure["PartRange", <||>]
	},
	TimeConstraint -> 300,
	TestID -> "Vectors-of-machine-reals-compute-the-evaluators-reals"
]
