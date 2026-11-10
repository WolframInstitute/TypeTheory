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
		TypeTheoryFormalize[compiledEvenQ, machine]["Tag"],
		TypeTheoryFormalize[compiledUntyped, machine]["Tag"],
		TypeTheoryFormalize[compiledProduct, TypeTheoryEnvironment["Integers"], "Meaning" -> "Compiled"]["Tag"]
	},
	{"Recursive", "NoTypedEntry", "NoMachineIntegers"},
	TestID -> "Recursion-untyped-code-and-a-missing-machine-are-failures"
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

(* a Do, whose iterator is a global the code localizes, and an If whose branch sets a local are not read yet *)
VerificationTest[
	{TypeTheoryFormalize[compiledDoSum, machine]["Tag"], TypeTheoryFormalize[compiledCollatz, machine]["Tag"]},
	{"UnmodeledOperation", "UnmodeledOperation"},
	TestID -> "A-Do-and-a-branch-that-sets-a-local-are-not-read-yet"
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

(* the order of the integers decided on the images of natural numbers, both ways *)
loops = loopDeclare[loops, TypeTheoryTheorem["integerLessEqualQOfNatural",
	ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies[m <= n, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "true"]],
	Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[h, m <= n]},
		InductiveRecursor[Exists][
			Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, n == m + k]] |-> "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "true",
			{Typed[k, NonNegativeIntegers], Typed[e, n == m + k]} |-> "equalitySubstitution"[
				P -> Function[{Typed[x, NonNegativeIntegers]}, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[x]] == "true"],
				"equalitySymmetry"[e],
				"equalitySubstitution"[
					P -> Function[{Typed[y, Integers]}, "integerLessEqualQ"["integerOfNatural"[m], y] == "true"],
					"equalitySymmetry"["integerOfNaturalAddition"[m, k]],
					"integerLessEqualQSelfAddition"["integerOfNatural"[m], k]
				]
			],
			"lessEqualWitness"[m, n, h]
		]
	]
]];
loops = loopDeclare[loops, TypeTheoryTheorem["integerLessEqualQNotOfNatural",
	ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies[Not[m <= n], "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "false"]],
	Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[h, Not[m <= n]]},
		InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == b, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "false"]],
			Function[{Typed[e, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "false"]}, e],
			Function[{Typed[e, "integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]] == "true"]},
				"falseElimination"[h["integerOfNaturalLessEqual"[m, n, "integerLessEqualQTrue"["integerOfNatural"[m], "integerOfNatural"[n], e]]]]],
			"integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]]
		]["equalityReflexivity"["integerLessEqualQ"["integerOfNatural"[m], "integerOfNatural"[n]]]]
	]
]];
(* the machine's sum of two natural numbers whose sum is below 2^63 is the machine integer of the sum *)
loops = loopDeclare[loops, TypeTheoryTheorem["machinePlusOfNatural",
	ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[h, a + b < 9223372036854775808]},
		"machinePlus"["integerOfNatural"[a], "integerOfNatural"[b]] == Typed["left"["subtype"["integerOfNatural"[a + b], "naturalInteger64Range"[a + b, h]]], "Integer64" | Failure]],
	Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[h, a + b < 9223372036854775808]},
		"equalityTransitivity"[
			"equalityCongruence"[Function[{Typed[x, Integers]}, "machineResult"[x]], "equalitySymmetry"["integerOfNaturalAddition"[a, b]]],
			"machineResultOfNatural"[a + b, h]
		]
	]
]];
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
			"equalitySubstitution"[P -> Function[{Typed[x, NonNegativeIntegers]}, s[["integer"]] == "integerOfNatural"[loopTriangular[x]]], "equalitySymmetry"[e], hs]
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
