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
		Function[{Typed[n, "Integer64"]}, "confirmBind"["machineResult"[n[[1]] + 1], Function[{Typed[WolframInstitute`TypeTheory`Compiled`t3, "Integer64"]}, "machineResult"[n[[1]] WolframInstitute`TypeTheory`Compiled`t3[[1]]]]]],
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
							Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t3, "Integer64"]}, "confirmBind"["machineResult"["integerOfNatural"[n] t3[[1]]], Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4[[1]], 2]]]]]],
							"machineResultInRange"["integerOfNatural"[n] + 1, "naturalInteger64Range"[n + 1, "successorBound"[n, h]]]
						],
						"equalityTransitivity"[
							"equalityCongruence"[
								Function[{Typed[x, Integers]}, "confirmBind"["machineResult"[x], Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4[[1]], 2]]]],
								"equalitySymmetry"["integerOfNaturalMultiplication"[n, n + 1]]
							],
							"equalityTransitivity"[
								"equalityCongruence"[
									Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t4, "Integer64"]}, "machineQuotient"[t4[[1]], 2]]]],
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
				Implies[n < levels, Implies[mathematicalTriangle[n] < 9223372036854775808, Implies[m[[1]] == "integerOfNatural"[n],
					Exists[{Typed[v, "Integer64"]}, compiledTriangle[levels, m] == Typed["left"[v], "Integer64" | Failure] && v[[1]] == "integerOfNatural"[mathematicalTriangle[n]]]]]]],
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
								Function[{Typed[x, Integers]}, "machineIf"["integerEqual"[x, 0], "machineResult"[0], "confirmBind"["machineResult"[x - 1], Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machineResult"[x + t10[[1]]]]]]]]],
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
					Function[{w0}, Exists[{Typed[w, "Integer64"]}, compiledTriangle[l + 1, m] == Typed["left"[w], "Integer64" | Failure] && w[[1]] == "integerOfNatural"[mathematicalTriangle[k + 1]]]],
					Function[
						{
							Typed[v, "Integer64"],
							Typed[hv, compiledTriangle[l, "subtype"["integerOfNatural"[k], "naturalInteger64Range"[k, "argumentBound"[k, mathematicalTriangle[k], 9223372036854775808, b]]]] == Typed["left"[v], "Integer64" | Failure] && v[[1]] == "integerOfNatural"[mathematicalTriangle[k]]]
						},
						"existsIntroduction"[
							"subtype"["integerOfNatural"[mathematicalTriangle[k + 1]], "naturalInteger64Range"[mathematicalTriangle[k + 1], b]],
							"andIntroduction"[
								"equalityTransitivity"[
									"equalityCongruence"[
										Function[{Typed[x, Integers]}, "machineIf"["integerEqual"[x, 0], "machineResult"[0], "confirmBind"["machineResult"[x - 1], Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machineResult"[x + t10[[1]]]]]]]]],
										e
									],
									"equalityTransitivity"[
										"equalityCongruence"[
											Function[{Typed[x, Integers]}, "confirmBind"["machineResult"[x], Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machineResult"["integerOfNatural"[k + 1] + t10[[1]]]]]]]],
											"integerOfNaturalPredecessor"[k]
										],
										"equalityTransitivity"[
											"equalityCongruence"[
												Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t9, "Integer64"]}, "confirmBind"[compiledTriangle[l, t9], Function[{Typed[t10, "Integer64"]}, "machineResult"["integerOfNatural"[k + 1] + t10[[1]]]]]]]],
												"machineResultOfNatural"[k, "argumentBound"[k, mathematicalTriangle[k], 9223372036854775808, b]]
											],
											"equalityTransitivity"[
												"equalityCongruence"[
													Function[{Typed[r, "Integer64" | Failure]}, "confirmBind"[r, Function[{Typed[t10, "Integer64"]}, "machineResult"["integerOfNatural"[k + 1] + t10[[1]]]]]],
													"andEliminationLeft"[hv]
												],
												"equalityTransitivity"[
													"equalityCongruence"[Function[{Typed[y, Integers]}, "machineResult"["integerOfNatural"[k + 1] + y]], "andEliminationRight"[hv]],
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

