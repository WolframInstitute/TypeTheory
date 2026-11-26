(* ::Package:: *)

(* Tests for Proofs/Superfunctions.wl: TypeTheoryDetermine, TypeTheoryAssumptions,
   TypeTheoryConsequences, and TypeTheoryTermination. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]
constructive = TypeTheoryEnvironment["Constructive"]
integers = TypeTheoryEnvironment["Integers"]

(* Helper verifying that a returned proof is accepted as a real TypeTheoryTheorem by the trusted kernel *)
theoremAcceptedQ[env_, proof_TypeTheoryProof] :=
	! FailureQ[TypeTheoryEnvironment[env, {TypeTheoryTheorem["checkedSuperfunctionTheorem", proof]}]]
theoremAcceptedQ[___] := False

(* whether one of the assumptions found reads as term, whichever environment handle it carries: an assumption over the
   statement's variables (1 <= c) is open, so DefinitionallyEqualQ cannot compare it, and the handle is not the point *)
SetAttributes[assumptionReadsQ, HoldRest]
assumptionReadsQ[res_List, term_] := MemberQ[Map[heldSurfaceTerm, Lookup[res, "Assumption"]], HoldComplete[term]]
heldSurfaceTerm[TypeTheoryTerm[term_, ___]] := HoldComplete[term]
heldSurfaceTerm[_] := None


(* ::Section:: *)
(*Trust Boundary and Input Guards*)


VerificationTest[
	FreeQ[WolframInstitute`TypeTheory`PackageScope`$trustedSources, s_String /; StringContainsQ[s, "Superfunctions"]],
	True,
	TestID -> "Superfunctions-is-outside-the-kernel-trust-boundary"
]

VerificationTest[
	{
		MatchQ[TypeTheoryDetermine[_Association], _TypeTheoryDetermine],
		MatchQ[TypeTheoryAssumptions[_Association], _TypeTheoryAssumptions],
		MatchQ[TypeTheoryConsequences[_Association], _TypeTheoryConsequences],
		FailureQ[TypeTheoryDetermine[NonNegativeIntegers, prelude]],
		TypeTheoryDetermine[NonNegativeIntegers, prelude]["Tag"]
	},
	{True, True, True, True, "NotAProposition"},
	TestID -> "Pattern-inputs-stay-unevaluated-and-non-propositions-fail"
]

VerificationTest[
	Block[{n = 99},
		With[{r = TypeTheoryDetermine[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude]},
			{r["Status"], theoremAcceptedQ[prelude, r["Proof"]]}
		]
	],
	{"Proved", True},
	TestID -> "Surface-propositions-stay-held-when-symbols-have-values"
]


(* ::Section:: *)
(*TypeTheoryDetermine*)


VerificationTest[
	With[
		{
			rTrue = TypeTheoryDetermine[2 + 2 == 4, prelude],
			rFalse = TypeTheoryDetermine[2 + 2 == 5, prelude]
		},
		{
			rTrue["Status"], rTrue["ComputationallyDecidable"], rTrue["Method"], theoremAcceptedQ[prelude, rTrue["Proof"]],
			rFalse["Status"], rFalse["ComputationallyDecidable"], rFalse["Method"], theoremAcceptedQ[prelude, rFalse["Proof"]]
		}
	],
	{"Proved", True, "Decide", True, "Refuted", True, "Decide", True},
	TestID -> "Determine-decides-closed-decidable-propositions-with-kernel-proofs"
]

VerificationTest[
	With[{r = TypeTheoryDetermine[ForAll[{Typed[n, NonNegativeIntegers]}, n^2 <= 2^n], prelude]},
		{r["Status"], r["Counterexample"], r["Method"], theoremAcceptedQ[prelude, r["Proof"]]}
	],
	{"Refuted", <|"n" -> 3|>, "Counterexample", True},
	TestID -> "Determine-refutes-false-universal-conjecture-with-counterexample"
]

VerificationTest[
	With[
		{
			rInd = TypeTheoryDetermine[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude],
			rInt = TypeTheoryDetermine[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x <= y, x <= y + 1]], integers]
		},
		{
			rInd["Status"], theoremAcceptedQ[prelude, rInd["Proof"]],
			rInt["Status"], theoremAcceptedQ[integers, rInt["Proof"]]
		}
	],
	{"Proved", True, "Proved", True},
	TestID -> "Determine-proves-inductive-natural-and-integer-linear-theorems"
]

VerificationTest[
	With[{r = TypeTheoryDetermine[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]], constructive]},
		{
			r["Status"],
			r["Details"]["ClassicallyProvable"],
			Length[r["Details"]["RequiredAxioms"]] > 0,
			theoremAcceptedQ[prelude, r["Details"]["ClassicalProof"]]
		}
	],
	{"Undetermined", True, True, True},
	TestID -> "Determine-reports-Undetermined-and-classical-axiom-gap-in-Constructive"
]

VerificationTest[
	With[{envF = TypeTheoryEnvironment[prelude, {TypeTheoryAxiom[opaqueInv, NonNegativeIntegers -> NonNegativeIntegers]}]},
		With[{r = TypeTheoryDetermine[ForAll[{Typed[x, NonNegativeIntegers]}, opaqueInv[opaqueInv[x]] == x], envF]},
			{
				r["Status"],
				r["Method"],
				theoremAcceptedQ[envF, r["Models"]["TrueModel"]["Proof"]],
				theoremAcceptedQ[envF, r["Models"]["FalseModel"]["Proof"]]
			}
		]
	],
	{"Independent", "CertifiedModelIndependence", True, True},
	TestID -> "Determine-certifies-independence-via-kernel-checked-models-for-opaque-function"
]

VerificationTest[
	With[
		{
			envMagma = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[magmaCarrier, TypeUniverse[1]],
				TypeTheoryAxiom[magmaOp, magmaCarrier -> magmaCarrier -> magmaCarrier]
			}]
		},
		With[{r = TypeTheoryDetermine[ForAll[{Typed[x, magmaCarrier], Typed[y, magmaCarrier]}, magmaOp[x, y] == magmaOp[y, x]], envMagma]},
			{
				r["Status"],
				r["Method"],
				theoremAcceptedQ[envMagma, r["Models"]["TrueModel"]["Proof"]],
				theoremAcceptedQ[envMagma, r["Models"]["FalseModel"]["Proof"]]
			}
		]
	],
	{"Independent", "CertifiedModelIndependence", True, True},
	TestID -> "Determine-certifies-independence-over-opaque-carrier-via-finite-models"
]

VerificationTest[
	With[{term = TypeTheoryTerm[2 + 3 == 5, prelude]},
		TypeTheoryDetermine[term]["Status"]
	],
	"Proved",
	TestID -> "Determine-accepts-a-TypeTheoryTerm-in-its-own-environment"
]


(* ::Section:: *)
(*TypeTheoryAssumptions*)


VerificationTest[
	TypeTheoryAssumptions[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude],
	{},
	TestID -> "Assumptions-returns-empty-list-for-already-provable-theorem"
]

VerificationTest[
	(* the proofs of both guards take 2-4 s each on a slow machine, more than the default 15 s leaves them after the
	   other candidates *)
	With[{res = TypeTheoryAssumptions[ForAll[{Typed[n, NonNegativeIntegers]}, n^2 <= 2^n], prelude, TimeConstraint -> 60]},
		{
			Length[res] >= 2,
			AllTrue[res, Function[item, TrueQ[item["Verified"]] && theoremAcceptedQ[prelude, item["Proof"]] && AssociationQ[item["Witness"]]]],
			assumptionReadsQ[res, 4 <= n],
			assumptionReadsQ[res, Not[n == 3]],
			AnyTrue[Lookup[res, "Statement"], Function[s, DefinitionallyEqualQ[s, TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[4 <= n, n^2 <= 2^n]], prelude]]]],
			AnyTrue[Lookup[res, "Statement"], Function[s, DefinitionallyEqualQ[s, TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[Not[n == 3], n^2 <= 2^n]], prelude]]]]
		}
	],
	{True, True, True, True, True, True},
	TestID -> "Assumptions-finds-exact-and-tail-guards-for-n-squared-leq-2-to-n"
]

(* a candidate whose proof runs out of its first 2.5 s retries with twice its share of the time left, at least 5 s,
   bounded by the deadline, and 10 s without a deadline; with a fixed 2.5 s, 4 <= n above was lost on a kernel where
   its proof takes 2.9 s *)
VerificationTest[
	With[
		{
			retryAt = Function[{secondsLeft, candidatesLeft},
				Block[{WolframInstitute`TypeTheory`Proofs`Superfunctions`Private`$superfunctionDeadline = AbsoluteTime[] + secondsLeft},
					WolframInstitute`TypeTheory`Proofs`Superfunctions`Private`retryProofBudget[2.5, candidatesLeft]
				]
			]
		},
		{
			9 < retryAt[10, 2] <= 10,
			retryAt[10, 20],
			retryAt[-1, 3],
			retryAt[Infinity, 3]
		}
	],
	{True, 5., 0.2, 10.},
	TestID -> "Assumptions-retry-proof-budget-scales-with-the-time-left"
]

(* every step's time limit scales with the budget: unchanged at the default 15 s, four times at 60 s, and four times
   without a time limit, so that no step runs unbounded *)
VerificationTest[
	{
		WolframInstitute`TypeTheory`Proofs`Superfunctions`Private`superfunctionScale /@ {15, 60, 5, Infinity},
		Block[{WolframInstitute`TypeTheory`Proofs`Superfunctions`Private`$superfunctionScale = 4},
			WolframInstitute`TypeTheory`Proofs`Superfunctions`Private`budgetScaled[2.5]
		],
		WolframInstitute`TypeTheory`Proofs`Superfunctions`Private`budgetScaled[2.5]
	},
	{{1, 4, 1/3, 4}, 10., 2.5},
	TestID -> "Assumptions-step-time-limits-scale-with-the-budget"
]

(* a proof search that runs out of its time says so, as the retry above needs: the time limit's abort could come back
   as a plain abort, tagged "Aborted" *)
VerificationTest[
	With[{resolved = WolframInstitute`TypeTheory`Proofs`Superfunctions`Private`resolveProposition[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[4 <= n, n^2 <= 2^n]], prelude]},
		With[{result = WolframInstitute`TypeTheory`PackageScope`enhancedProveCore[resolved["Environment"], resolved["CoreStatement"], resolved["UniverseParameters"], 0.2]},
			{FailureQ[result], First[result]}
		]
	],
	{True, "TimedOut"},
	TestID -> "Assumptions-proof-search-out-of-time-is-tagged-timed-out"
]

VerificationTest[
	With[{res = TypeTheoryAssumptions[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Subtract[a, b] + b == a], prelude]},
		{
			Length[res] >= 1,
			AllTrue[res, Function[item, TrueQ[item["Verified"]] && theoremAcceptedQ[prelude, item["Proof"]]]],
			assumptionReadsQ[res, b <= a],
			AnyTrue[Lookup[res, "Statement"], Function[s, DefinitionallyEqualQ[s, TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[b <= a, Subtract[a, b] + b == a]], prelude]]]]
		}
	],
	{True, True, True, True},
	TestID -> "Assumptions-finds-b-leq-a-for-natural-subtraction-cancellation"
]

VerificationTest[
	(* which candidates verify within the default 15 s depends on the machine's load: twice on a busy Mac neither guard
	   came back *)
	With[{res = TypeTheoryAssumptions[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, Implies[a * c == b * c, a == b]], prelude, TimeConstraint -> 60]},
		{
			Length[res] >= 1,
			AllTrue[res, Function[item, TrueQ[item["Verified"]] && theoremAcceptedQ[prelude, item["Proof"]]]],
			assumptionReadsQ[res, 1 <= c] ||
				assumptionReadsQ[res, Not[c == 0]],
			AnyTrue[Lookup[res, "Statement"], Function[s,
				DefinitionallyEqualQ[s, TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, Implies[1 <= c, Implies[a * c == b * c, a == b]]], prelude]] ||
				DefinitionallyEqualQ[s, TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, Implies[Not[c == 0], Implies[a * c == b * c, a == b]]], prelude]]
			]],
			! assumptionReadsQ[res, a == b]
		}
	],
	{True, True, True, True, True},
	TestID -> "Assumptions-finds-nonzero-factor-and-filters-trivial-conclusion-for-cancellation"
]

VerificationTest[
	With[{res = TypeTheoryAssumptions[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]], constructive]},
		{
			Length[res] >= 1,
			First[res]["Method"],
			DefinitionallyEqualQ[First[res]["Assumption"], TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]], constructive]],
			theoremAcceptedQ[constructive, First[res]["Proof"]]
		}
	],
	{True, "AxiomDiff", True, True},
	TestID -> "Assumptions-discovers-excluded-middle-for-DNE-in-Constructive"
]

VerificationTest[
	With[
		{
			envOp = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[algCarrier, TypeUniverse[1]],
				TypeTheoryAxiom[algOp, algCarrier -> algCarrier -> algCarrier]
			}]
		},
		(* at half a processor the default 15 s found nothing: the catalog's checks need the larger budget's longer steps *)
		With[{res = TypeTheoryAssumptions[ForAll[{Typed[x, algCarrier], Typed[y, algCarrier], Typed[z, algCarrier]}, algOp[algOp[x, y], z] == algOp[x, algOp[z, y]]], envOp, TimeConstraint -> 60]},
			{
				Length[res] >= 1,
				First[res]["Method"],
				DefinitionallyEqualQ[
					First[res]["Assumption"],
					TypeTheoryTerm[
						And[
							ForAll[{Typed[x, algCarrier], Typed[y, algCarrier]}, algOp[x, y] == algOp[y, x]],
							ForAll[{Typed[x, algCarrier], Typed[y, algCarrier], Typed[z, algCarrier]}, algOp[algOp[x, y], z] == algOp[x, algOp[y, z]]]
						],
						envOp
					]
				],
				theoremAcceptedQ[envOp, First[res]["Proof"]]
			}
		]
	],
	{True, "AlgebraicCatalog", True, True},
	TestID -> "Assumptions-discovers-associativity-and-commutativity-from-algebraic-catalog"
]

VerificationTest[
	Module[{openProof, res},
		openProof = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n == 0], prelude, {"Introduce"[n]}];
		res = TypeTheoryAssumptions[openProof];
		{Length[res], First[res]["Scope"], TrueQ[First[res]["Verified"]]}
	],
	{1, "GoalHole", True},
	TestID -> "Assumptions-extracts-hole-closing-assumptions-from-open-TypeTheoryProof"
]


(* ::Section:: *)
(*TypeTheoryConsequences*)


VerificationTest[
	With[{res = TypeTheoryConsequences[ForAll[{Typed[n, NonNegativeIntegers]}, n^2 <= 2^n], prelude]},
		{
			Length[res],
			First[res]["Consequence"],
			First[res]["Inconsistent"],
			theoremAcceptedQ[prelude, First[res]["Proof"]]
		}
	],
	{1, TypeTheoryTerm[False, prelude], True, True},
	TestID -> "Consequences-short-circuits-to-False-on-inconsistent-proposition"
]

VerificationTest[
	With[{envF = TypeTheoryEnvironment[prelude, {TypeTheoryAxiom[involFn, NonNegativeIntegers -> NonNegativeIntegers]}]},
		With[{res = TypeTheoryConsequences[ForAll[{Typed[x, NonNegativeIntegers]}, involFn[involFn[x]] == x], envF, TimeConstraint -> 30]},
			{
				Length[res] >= 3,
				AllTrue[res, Function[item, TrueQ[item["Verified"]] && theoremAcceptedQ[envF, item["Proof"]]]],
				AnyTrue[Lookup[res, "Consequence"], Function[c, DefinitionallyEqualQ[c, TypeTheoryTerm[ForAll[{Typed[y, NonNegativeIntegers]}, Exists[{Typed[x, NonNegativeIntegers]}, involFn[x] == y]], envF]]]],
				AnyTrue[Lookup[res, "Consequence"], Function[c, DefinitionallyEqualQ[c, TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[involFn[x] == involFn[y], x == y]], envF]]]],
				AnyTrue[Lookup[res, "Consequence"], Function[c, DefinitionallyEqualQ[c, TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, involFn[involFn[involFn[x]]] == involFn[x]], envF]]]]
			}
		]
	],
	{True, True, True, True, True},
	TestID -> "Consequences-derives-injectivity-and-surjectivity-from-involution"
]

VerificationTest[
	With[
		{
			envXY = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[xCircle, NonNegativeIntegers],
				TypeTheoryAxiom[yCircle, NonNegativeIntegers]
			}]
		},
		With[{res = TypeTheoryConsequences[xCircle^2 + yCircle^2 == 25, envXY]},
			{
				Length[res] >= 2,
				AllTrue[res, Function[item, TrueQ[item["Verified"]] && theoremAcceptedQ[envXY, item["Proof"]]]],
				MemberQ[Lookup[res, "Consequence"], TypeTheoryTerm[xCircle <= 5, envXY]],
				MemberQ[Lookup[res, "Consequence"], TypeTheoryTerm[yCircle <= 5, envXY]]
			}
		]
	],
	{True, True, True, True},
	TestID -> "Consequences-projects-tight-bounds-from-circle-equation"
]

VerificationTest[
	With[{res = TypeTheoryConsequences[ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]], constructive]},
		{
			Length[res] >= 3,
			AllTrue[res, Function[item, TrueQ[item["Verified"]] && theoremAcceptedQ[constructive, item["Proof"]]]],
			AnyTrue[Lookup[res, "Consequence"], Function[c, DefinitionallyEqualQ[c, TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]], constructive]]]],
			AnyTrue[Lookup[res, "Consequence"], Function[c, DefinitionallyEqualQ[c, TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Implies[Implies[p, q], p], p]], constructive]]]],
			AnyTrue[Lookup[res, "Consequence"], Function[c, DefinitionallyEqualQ[c, TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Implies[Not[q], Not[p]], Implies[p, q]]], constructive]]]]
		}
	],
	{True, True, True, True, True},
	TestID -> "Consequences-derives-classical-principles-from-excluded-middle-in-Constructive"
]

VerificationTest[
	With[
		{
			envAB = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[aOrd, NonNegativeIntegers],
				TypeTheoryAxiom[bOrd, NonNegativeIntegers]
			}]
		},
		With[{res = TypeTheoryConsequences[And[aOrd <= bOrd, bOrd <= aOrd], envAB]},
			{
				MemberQ[Lookup[res, "Consequence"], TypeTheoryTerm[aOrd == bOrd, envAB]],
				AllTrue[res, Function[item, TrueQ[item["Verified"]] && theoremAcceptedQ[envAB, item["Proof"]]]]
			}
		]
	],
	{True, True},
	TestID -> "Consequences-forward-chains-antisymmetry-to-equality"
]


(* ::Section:: *)
(*TypeTheoryTermination*)


VerificationTest[
	With[{r = TypeTheoryTermination[rwA[rwB[0]], {rwA[rwB[x_]] :> rwB[rwA[x]]}]},
		{r["Status"], r["Steps"], TrueQ[r["Verified"]], MatchQ[r["Proof"], _TypeTheoryProof]}
	],
	{"Terminating", 1, True, True},
	TestID -> "Termination-certifies-pointwise-rewrite-termination"
]

VerificationTest[
	With[{r = TypeTheoryTermination[{rwA[rwB[x_]] :> rwB[rwA[x]]}]},
		{r["Status"], r["Method"], TrueQ[r["Verified"]], MatchQ[r["Proof"], _TypeTheoryProof]}
	],
	{"Terminating", "PolynomialWeightInterpretation", True, True},
	TestID -> "Termination-certifies-global-TRS-termination-via-polynomial-weights"
]

VerificationTest[
	Module[{lassoFn, r},
		lassoFn[x_] := lassoFn[x];
		r = TypeTheoryTermination[lassoFn[0]];
		{r["Status"], r["Method"], r["Cycle"]["Period"], TrueQ[r["Verified"]], MatchQ[r["Proof"], _TypeTheoryProof]}
	],
	{"NonTerminating", "LassoCycleInduction", 1, True, True},
	TestID -> "Termination-certifies-pointwise-lasso-cycle-non-termination"
]

VerificationTest[
	Module[{growFn, r},
		growFn[x_] := growFn[x + 1];
		r = TypeTheoryTermination[growFn, "Meaning" -> "Rules"];
		{r["Status"], r["Method"], TrueQ[r["Verified"]], MatchQ[r["Proof"], _TypeTheoryProof]}
	],
	{"NonTerminating", "SelfEmbeddingDivergenceInvariant", True, True},
	TestID -> "Termination-certifies-unbounded-self-embedding-divergence"
]

VerificationTest[
	Module[{sumLoop, r},
		sumLoop[n_Integer] := Module[{i = n, s = 0}, While[i > 0, s += i; i--]; s];
		r = TypeTheoryTermination[sumLoop];
		{r["Status"], r["Method"], r["Measure"], TrueQ[r["Verified"]], theoremAcceptedQ[integers, r["Proof"]]}
	],
	{"Terminating", "FarkasAffineRankingFunction", "i", True, True},
	TestID -> "Termination-certifies-While-loop-via-Farkas-affine-ranking-function"
]

VerificationTest[
	Module[{factFn, r},
		factFn[n_Integer] := If[n == 0, 1, n * factFn[n - 1]];
		r = TypeTheoryTermination[factFn];
		{
			r["Status"],
			r["Precondition"],
			r["NonTerminationWitness"],
			TrueQ[r["Verified"]],
			theoremAcceptedQ[integers, r["TerminationProof"]],
			theoremAcceptedQ[integers, r["NonTerminationProof"]]
		}
	],
	{"ConditionallyTerminating", "0 <= n", <|"n" -> -1|>, True, True, True},
	TestID -> "Termination-certifies-conditional-termination-and-divergence-witness-for-factorial"
]

VerificationTest[
	Module[{doubleInt, r},
		doubleInt[n_Integer] := 2 * n;
		r = TypeTheoryTermination[doubleInt, "Meaning" -> "Function"];
		{r["Status"], r["Method"], TrueQ[r["Verified"]]}
	],
	{"Terminating", "StructuralRecursor", True},
	TestID -> "Termination-certifies-total-formalized-function-by-structural-recursion"
]

VerificationTest[
	{
		TypeTheoryDetermine[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude, ProgressReporting -> False]["Status"],
		TypeTheoryDetermine[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude, ProgressReporting -> True]["Status"],
		Length[TypeTheoryAssumptions[ForAll[{Typed[n, NonNegativeIntegers]}, n^2 <= 2^n], prelude, ProgressReporting -> False]] >= 1,
		First[TypeTheoryConsequences[ForAll[{Typed[n, NonNegativeIntegers]}, n^2 <= 2^n], prelude, ProgressReporting -> False]]["Inconsistent"],
		TypeTheoryTermination[rwA[rwB[0]], {rwA[rwB[x_]] :> rwB[rwA[x]]}, ProgressReporting -> False]["Status"]
	},
	{"Proved", "Proved", True, True, "Terminating"},
	TestID -> "ProgressReporting-option-works-across-all-four-superfunctions"
]
