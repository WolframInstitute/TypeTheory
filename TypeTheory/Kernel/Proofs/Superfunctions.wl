(* ::Package:: *)

(*
Superfunctions: kernel-certified proposition determination, sensible assumption abduction,
sensible consequence discovery, and termination analysis for formalized Wolfram Language code.

Everything in this file is UNTRUSTED: it lies outside $trustedSources and never modifies the
kernel's trust boundary. Every proof returned as verified is explicitly checked by the kernel's
type checker (checkHasType) before leaving this module.

Four exported superfunctions:

	TypeTheoryDetermine[proposition, environment, options]
		Determines whether proposition is "Proved", "Refuted" (with counterexample witness),
		"Independent" (certified by models satisfying both proposition and its negation), or
		"Undetermined" (honestly reporting search exhaustion alongside "ComputationallyDecidable").

	TypeTheoryAssumptions[proposition | openProof, environment, options]
		Finds ranked, sensible, non-vacuous, non-trivial assumptions A that turn an unprovable
		proposition into a kernel-checked theorem A => P (or fill open proof goals), combining
		symbolic domain abduction (Reduce/Resolve), tactic-residual lemma abduction, axiom diff,
		counterexample refinement, algebraic property catalog, and optional LLMFunction.

	TypeTheoryConsequences[proposition, environment, options]
		Discovers ranked, sensible, non-trivial consequences C following from proposition P,
		with inconsistency short-circuiting, exact proof-term relevance checking (h must occur
		free in the normalized proof term), non-background novelty filtering, and subsumption
		pruning.

	TypeTheoryTermination[target, ..., options]
		Checks termination of formalized Wolfram Language rewrite rule systems, expressions,
		direct definitions, and fueled While/recursive functions: concrete execution and
		kernel-checked lasso cycle proofs, linear polynomial weight interpretations for rewrite
		rules, affine Farkas ranking functions, divergence invariants, and conditional
		termination preconditions.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryDetermine]
PackageExported[TypeTheoryAssumptions]
PackageExported[TypeTheoryConsequences]
PackageExported[TypeTheoryTermination]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[verifyProofInKernel]
PackageScoped[enhancedProveCore]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryDetermine::usage = "TypeTheoryDetermine[proposition] determines whether proposition is \"Proved\", \"Refuted\", \"Independent\" or \"Undetermined\" in the default environment, returning an Association with kernel-checked certificates.\n\
TypeTheoryDetermine[proposition, environment] determines proposition in environment (a TypeTheoryEnvironment or library name).\n\
Options: Method -> Automatic (strictly offline heuristic; \"LLM\" or {\"Heuristic\", \"LLM\"} enables optional LLMFunction assistance), TimeConstraint -> 15, \"MaxModelSize\" -> 3, \"LLMEvaluator\" -> Automatic, ProgressReporting -> Automatic."

TypeTheoryAssumptions::usage = "TypeTheoryAssumptions[proposition] finds ranked, sensible, non-vacuous, non-trivial assumptions that make proposition a kernel-checked theorem in the default environment.\n\
TypeTheoryAssumptions[proposition, environment] searches in environment.\n\
TypeTheoryAssumptions[openProof] extracts and simplifies sensible assumptions filling the open goals of an unfinished TypeTheoryProof.\n\
Returns a list of Associations <|\"Assumption\" -> term, \"Statement\" -> implication, \"Proof\" -> proof, ...|>.\n\
Options: Method -> Automatic, TimeConstraint -> 15, MaxItems -> 5, \"EquivalentConditions\" -> True, \"IncludeOpen\" -> False, \"LLMEvaluator\" -> Automatic, ProgressReporting -> Automatic."

TypeTheoryConsequences::usage = "TypeTheoryConsequences[proposition] discovers ranked, sensible, non-trivial consequences of proposition in the default environment, each kernel-checked and verified to genuinely use proposition in its proof term.\n\
TypeTheoryConsequences[proposition, environment] searches in environment.\n\
If Not[proposition] is provable, short-circuits and returns False tagged with \"Inconsistent\" -> True.\n\
Returns a list of Associations <|\"Consequence\" -> term, \"Statement\" -> implication, \"Proof\" -> proof, ...|>.\n\
Options: Method -> Automatic, TimeConstraint -> 15, MaxItems -> 8, \"IncludeEquivalents\" -> False, \"LLMEvaluator\" -> Automatic, ProgressReporting -> Automatic."

TypeTheoryTermination::usage = "TypeTheoryTermination[symbol] analyzes termination of a Wolfram Language function or rewrite symbol (formalized via TypeTheoryFormalize) and returns an Association with \"Status\" -> \"Terminating\" | \"NonTerminating\" | \"ConditionallyTerminating\" | \"Undetermined\" and kernel-checked certificates.\n\
TypeTheoryTermination[symbol, environment] analyzes symbol in environment.\n\
TypeTheoryTermination[expression, rules] checks pointwise termination or non-termination (lasso cycle) of expression under rules.\n\
TypeTheoryTermination[rules] checks global termination of a list of rewrite rules via polynomial weight interpretations or divergence witnesses.\n\
Options: Method -> Automatic, \"Meaning\" -> Automatic, \"MaxSteps\" -> 100, TimeConstraint -> 15, \"LLMEvaluator\" -> Automatic, ProgressReporting -> Automatic."

verifyProofInKernel::usage = "verifyProofInKernel[environment, coreStatement, universeParameters, proof] verifies with the trusted kernel that proof is finished and its proof term has type coreStatement in environment."
enhancedProveCore::usage = "enhancedProveCore[environment, coreStatement, universeParameters, timeLimit] attempts to build a kernel-checked TypeTheoryProof of coreStatement using Automatic plus untrusted induction, cancellation, subtraction, integer linear arithmetic and Boolean case-splitting heuristics."


(* ::Section:: *)
(*Options and Attributes*)


Options[TypeTheoryDetermine] = {
	Method -> Automatic,
	TimeConstraint -> 15,
	"MaxModelSize" -> 3,
	"LLMEvaluator" -> Automatic,
	ProgressReporting -> Automatic
}

Options[TypeTheoryAssumptions] = {
	Method -> Automatic,
	TimeConstraint -> 15,
	MaxItems -> 5,
	"EquivalentConditions" -> True,
	"IncludeOpen" -> False,
	"LLMEvaluator" -> Automatic,
	ProgressReporting -> Automatic
}

Options[TypeTheoryConsequences] = {
	Method -> Automatic,
	TimeConstraint -> 15,
	MaxItems -> 8,
	"IncludeEquivalents" -> False,
	"LLMEvaluator" -> Automatic,
	ProgressReporting -> Automatic
}

Options[TypeTheoryTermination] = {
	Method -> Automatic,
	"Meaning" -> Automatic,
	"MaxSteps" -> 100,
	TimeConstraint -> 15,
	"LLMEvaluator" -> Automatic,
	ProgressReporting -> Automatic
}

SetAttributes[TypeTheoryDetermine, HoldFirst]
SetAttributes[TypeTheoryAssumptions, HoldFirst]
SetAttributes[TypeTheoryConsequences, HoldFirst]
SetAttributes[TypeTheoryTermination, HoldAllComplete]


(* ::Section:: *)
(*Shared Core Infrastructure and Kernel Trust Gate*)


(* Local proof-state utilities (self-contained so Superfunctions.wl stays completely decoupled from ProofStates.wl internals) *)
statementQ[Unevaluated[_Association]] := False
statementQ[Unevaluated[statement_]] :=
	FreeQ[ReplaceAll[HoldComplete[statement], (Rule | RuleDelayed)[_, _] -> Null], _Pattern | _Blank | _BlankSequence | _BlankNullSequence]

termExpressionQ[Unevaluated[_TypeTheoryTerm]] := True
termExpressionQ[Unevaluated[symbol_Symbol]] := MatchQ[OwnValues[symbol], {Verbatim[RuleDelayed][_, _TypeTheoryTerm]}]
termExpressionQ[_] := False

proofState[data_Association] := TypeTheoryProof[data]

startProof[environment_, held_HoldComplete, Hold[___]] := Replace[held, HoldComplete[stmt_] :> TypeTheoryProof[stmt, environment]]

newProofState[environment_, statement_, universeParameters_List] := With[{root = freshMetavariableId[]},
	proofState[<|
		"Environment" -> environment,
		"Statement" -> statement,
		"UniverseParameters" -> universeParameters,
		"Root" -> root,
		"Goals" -> {root},
		"Metavariables" -> <|root -> <|"Context" -> <||>, "Type" -> statement, "Case" -> None|>|>,
		"Assignments" -> <||>
	|>]
]

runTactics[state_, tactics_List] := Fold[Function[{current, tactic}, If[FailureQ[current], current, tactic[current]]], state, tactics]

currentGoal[data_, goal_] := With[{entry = data["Metavariables"][goal]},
	<|
		"Context" -> Function[hypothesis, Append[hypothesis, "Type" -> instantiateProofTerm[data, hypothesis["Type"]]]] /@ entry["Context"],
		"Type" -> instantiateProofTerm[data, entry["Type"]]
	|>
]

solveGoal[data_, goal_, term_, newGoals_List] := Join[data, <|
	"Assignments" -> Append[data["Assignments"], goal -> term],
	"Metavariables" -> Join[data["Metavariables"], Association[newGoals]],
	"Goals" -> Join[Keys[newGoals], DeleteCases[data["Goals"], goal]]
|>]

contextScope[context_Association] := Association @ KeyValueMap[Function[{id, entry}, entry["Name"] -> {freeVariable[id], entry["Type"]}], context]

mentionedFreeVariables[term_] := Union[Cases[term, freeVariable[id_] :> id, {0, Infinity}]]

neededContext[context_Association, term_] := With[
	{
		needed = FixedPoint[
			Function[ids, Union[ids, mentionedFreeVariables[Function[id, {context[id]["Type"], Lookup[context[id], "Value", {}]}] /@ ids]]],
			Intersection[mentionedFreeVariables[term], Keys[context]]
		]
	},
	KeySelect[context, Function[id, MemberQ[needed, id]]]
]

naturalNumberTypeQ[environment_, context_, type_] := MatchQ[weakHeadNormalForm[environment, context, type], constantReference[HoldComplete[NonNegativeIntegers], _]]
integerTypeQ[environment_, type_] := type === constantReference[HoldComplete[Integers], {}] && constantDeclaredQ[environment, HoldComplete["integerRelation"]]
rationalTypeQ[environment_, type_] := type === constantReference[HoldComplete[Rationals], {}] && constantDeclaredQ[environment, HoldComplete["rationalRelation"]]

conclusionName[dependentFunctionType[_, _, codomain_, _]] := conclusionName[codomain]
conclusionName[type_] := Replace[First[applicationSpine[type]], {constantReference[name_, _] :> name, _ -> None}]

(* Introduce all leading universal binders and hypotheses via the exported "Introduce" tactic *)
introducedHypotheses[data_Association, goal_, _Integer] := Module[{cur = proofState[data], next},
	While[ ! FailureQ[cur] && cur["Goals"] =!= {},
		next = Quiet @ catchKernelFailure[TypeTheoryTactic["Introduce"][cur]];
		If[ FailureQ[next],
			Break[],
			cur = next
		]
	];
	First[cur]
]

(* Resolve any local pendingAbstraction wrappers bottom-up BEFORE ProofStates's instantiateProofTerm runs,
   using memoization so each metavariable assignment is resolved at most once. *)
finalizeSuperProof[TypeTheoryProof[data_Association]] := If[ data["Goals"] =!= {},
	proofState[data],
	Module[{asg = data["Assignments"], memo = <||>, resolveTerm, rawTerm},
		resolveTerm[term_] := ReplaceAll[
			term,
			{
				metavariable[id_] /; KeyExistsQ[asg, id] :> With[{v = Lookup[memo, id, memo[id] = resolveTerm[asg[id]]]}, v /; True],
				pendingAbstraction[ctx_, ids_, body_] :> With[{v = makeLambda[ctx, ids, resolveTerm[body]]}, v /; True]
			}
		];
		rawTerm = resolveTerm[metavariable[data["Root"]]];
		rawTerm = instantiateProofTerm[Append[data, "Assignments" -> <|data["Root"] -> rawTerm|>], metavariable[data["Root"]]];
		proofState[Append[data, "Assignments" -> <|data["Root"] -> rawTerm|>]]
	]
]


(* Strict kernel check: every finished proof returned as verified must pass checkHasType in the trusted kernel. *)
verifyProofInKernel[environment_, coreStatement_, universeParameters_List, proof_TypeTheoryProof] := Module[{finalProof, term, checked},
	If[ proof["Goals"] =!= {},
		Failure["ProofIncomplete", <|
			"MessageTemplate" -> "The proof still has open goals.",
			"MessageParameters" -> {}
		|>],

		finalProof = finalizeSuperProof[proof];
		term = Quiet @ catchKernelFailure[completedProofTerm[finalProof]];
		If[ FailureQ[term],
			term,

			checked = Quiet @ catchKernelFailure[
				withKernelCaches[
					Block[{$termsChecked = False, $universeParameterNames = universeParameters},
						checkHasType[environment, <||>, term, coreStatement]
					]
				]
			];
			If[ FailureQ[checked],
				Failure["KernelVerificationFailed", <|
					"MessageTemplate" -> "The kernel rejected the candidate proof term.",
					"MessageParameters" -> {},
					"Reason" -> checked
				|>],

				finalProof
			]
		]
	]
]
verifyProofInKernel[_, _, _, failure_Failure] := failure
verifyProofInKernel[_, _, _, other_] := Failure["KernelVerificationFailed", <|
	"MessageTemplate" -> "Expected a TypeTheoryProof, not `1`.",
	"MessageParameters" -> {other}
|>]


(* Resolve environment argument: TypeTheoryEnvironment, library name string, or default *)
resolveEnvironmentArg[environment_?environmentQ] := environment
resolveEnvironmentArg[name_String] := TypeTheoryEnvironment[name]
resolveEnvironmentArg[other_] := Failure["InvalidEnvironment", <|
	"MessageTemplate" -> "`1` is not a TypeTheoryEnvironment or library environment name.",
	"MessageParameters" -> {other}
|>]


(* Resolve a held proposition (surface statement or TypeTheoryTerm) in an environment and check it lives in Prop. *)
SetAttributes[resolveProposition, HoldFirst]
resolveProposition[statement_, environmentSpec_] := Module[{environment, held, started, coreStatement, universeParameters, isProp},
	If[ termExpressionQ[Unevaluated[statement]],
		With[{evaluated = statement},
			environment = If[ environmentSpec === Automatic,
				termEnvironment[evaluated],
				resolveEnvironmentArg[environmentSpec]
			];
			held = heldTerm[evaluated]
		],

		environment = If[ environmentSpec === Automatic,
			defaultEnvironment[],
			resolveEnvironmentArg[environmentSpec]
		];
		held = HoldComplete[statement]
	];
	If[ FailureQ[environment],
		environment,

		started = Quiet @ catchKernelFailure[startProof[environment, held, Hold[]]];
		If[ FailureQ[started],
			started,

			coreStatement = proofStatement[started];
			universeParameters = proofUniverseParameters[started];
			isProp = TrueQ @ Quiet @ catchKernelFailure[
				withKernelCaches[
					Block[{$universeParameterNames = universeParameters},
						propositionQ[environment, <||>, coreStatement]
					]
				]
			];
			If[ ! isProp,
				Failure["NotAProposition", <|
					"MessageTemplate" -> "The term `1` is not a proposition (its type does not reduce to Prop).",
					"MessageParameters" -> {coreToTypeTheoryTerm[environment, <||>, coreStatement]}
				|>],

				<|
					"Environment" -> environment,
					"CoreStatement" -> coreStatement,
					"UniverseParameters" -> universeParameters,
					"SurfaceTerm" -> coreToTypeTheoryTerm[environment, <||>, coreStatement]
				|>
			]
		]
	]
]


(* Method parsing: strictly offline by default (Method -> Automatic -> {"Heuristic"}). *)
resolveMethodList[Automatic] := {"Heuristic"}
resolveMethodList["Heuristic"] := {"Heuristic"}
resolveMethodList["LLM"] := {"LLM"}
resolveMethodList[methods_List] := Select[methods, MatchQ[#, "Heuristic" | "LLM"] &]
resolveMethodList[_] := {"Heuristic"}

useHeuristicQ[method_] := MemberQ[resolveMethodList[method], "Heuristic"]
useLLMQ[method_] := MemberQ[resolveMethodList[method], "LLM"]


(* Native Wolfram Language progress bar and shared deadline guard *)
$inSuperfunctionProgress = False
$progressText = ""
$progressFraction = Indeterminate
$superfunctionDeadline = Infinity

reportProgress[text_String, fraction_ : Indeterminate] := (
	$progressText = text;
	$progressFraction = fraction;
)

deadlineExceededQ[] := NumericQ[$superfunctionDeadline] && AbsoluteTime[] >= $superfunctionDeadline

remainingBudget[fallback_ : 5] := If[ NumericQ[$superfunctionDeadline],
	Max[0.2, Min[fallback, $superfunctionDeadline - AbsoluteTime[]]],
	fallback
]

(* The time a candidate's proof gets when it tries again after running out of floor seconds: twice its fair share of
   what is left of the budget and at least twice floor, bounded by the deadline; without a deadline, four times floor.
   Only the retry grows, so every answer the first pass finds stays found, and the time left over finds the slow
   ones: 4 <= n => n^2 <= 2^n took 2.0 s on one kernel and 2.9 s on the next, and a fixed 2.5 s dropped it. *)
(* A step's time limit given as its value at the default budget of 15 s, scaled with the budget of the call: TimeConstraint
   is then the one dial, and a slower machine given a larger budget gets it for every step, not only for the steps
   bounded by the deadline. At the default budget the scale is 1; findAssumptions sets it, and without a time limit
   it is 4, so that no step runs without a limit. *)
$superfunctionScale = 1

budgetScaled[seconds_] := seconds * $superfunctionScale

superfunctionScale[timeBudget_] := If[ timeBudget < Infinity, timeBudget / 15, 4 ]

retryProofBudget[floor_, candidatesLeft_Integer] := If[ NumericQ[$superfunctionDeadline],
	remainingBudget[Max[2 * floor, 2 * ($superfunctionDeadline - AbsoluteTime[]) / Max[1, candidatesLeft]]],
	4 * floor
]

SetAttributes[withSuperfunctionProgress, HoldAll]
withSuperfunctionProgress[title_String, progressOpt_, timeBudget_, body_] := Module[{effectiveProgress, deadline},
	effectiveProgress = Replace[progressOpt, {
		Automatic :> ($ProgressReporting =!= False),
		True -> True,
		_ -> False
	}];
	deadline = If[ NumericQ[timeBudget] && timeBudget > 0, AbsoluteTime[] + timeBudget, Infinity ];
	Block[
		{
			$superfunctionDeadline = If[ NumericQ[$superfunctionDeadline], Min[$superfunctionDeadline, deadline], deadline ],
			$progressText = "Starting...",
			$progressFraction = Indeterminate
		},
		If[ TrueQ[effectiveProgress] && ! TrueQ[$inSuperfunctionProgress] && NameQ["Progress`EvaluateWithProgress"],
			Block[{$inSuperfunctionProgress = True},
				Progress`EvaluateWithProgress[
					body,
					<|
						"Text" :> $progressText,
						"Progress" :> $progressFraction,
						"ElapsedTime" -> Automatic
					|>,
					ProgressReporting -> If[progressOpt === Automatic, Automatic, True],
					Title -> title
				]
			],
			body
		]
	]
]


(* Core term builders (always computing parts before wrapping held core heads). *)
coreConstant[name_HoldComplete, levels_List : {}] := Construct[constantReference, name, levels]
coreFalse[] := coreConstant[HoldComplete[False]]
coreTrue[] := coreConstant[HoldComplete[True]]
coreNaturals[] := coreConstant[HoldComplete[NonNegativeIntegers]]
coreBooleans[] := coreConstant[HoldComplete[Booleans]]
coreIntegers[] := coreConstant[HoldComplete[Integers]]
coreRationals[] := coreConstant[HoldComplete[Rationals]]

coreNegation[environment_, statement_] := If[ constantDeclaredQ[environment, HoldComplete[Not]],
	Construct[application, coreConstant[HoldComplete[Not]], statement],
	With[{lifted = liftBoundVariables[coreFalse[], 1, 0]},
		Construct[dependentFunctionType, HoldComplete[\[FormalX]], statement, lifted, "Explicit"]
	]
]

coreImplication[premise_, conclusion_] := With[{lifted = liftBoundVariables[conclusion, 1, 0]},
	Construct[dependentFunctionType, HoldComplete[\[FormalX]], premise, lifted, "Explicit"]
]

coreConjunction[left_, right_] := makeApplication[coreConstant[HoldComplete[And]], {left, right}]
coreDisjunction[left_, right_] := makeApplication[coreConstant[HoldComplete[Or]], {left, right}]
coreEquality[type_, left_, right_, levels_List : {1}] := makeApplication[coreConstant[HoldComplete[Equal], levels], {type, left, right}]
coreNaturalLessEqual[left_, right_] := makeApplication[coreConstant[HoldComplete[LessEqual]], {left, right}]
coreNaturalLess[left_, right_] := makeApplication[coreConstant[HoldComplete[Less]], {left, right}]
coreNaturalPlus[left_, right_] := makeApplication[coreConstant[HoldComplete[Plus]], {left, right}]
coreNaturalTimes[left_, right_] := makeApplication[coreConstant[HoldComplete[Times]], {left, right}]
coreNaturalPower[left_, right_] := makeApplication[coreConstant[HoldComplete[Power]], {left, right}]
coreNaturalSubtract[left_, right_] := makeApplication[coreConstant[HoldComplete[Subtract]], {left, right}]

coreIntegerOfNatural[term_] := Construct[application, coreConstant[HoldComplete["integerOfNatural"]], term]
coreIntegerNegation[term_] := Construct[application, coreConstant[HoldComplete["integerNegation"]], term]
coreIntegerLiteral[n_Integer?NonNegative] := coreIntegerOfNatural[naturalLiteral[n]]
coreIntegerLiteral[n_Integer?Negative] := coreIntegerNegation[coreIntegerOfNatural[naturalLiteral[-n]]]
coreIntegerAddition[left_, right_] := makeApplication[coreConstant[HoldComplete["integerAddition"]], {left, right}]
coreIntegerSubtraction[left_, right_] := makeApplication[coreConstant[HoldComplete["integerSubtraction"]], {left, right}]
coreIntegerMultiplication[left_, right_] := makeApplication[coreConstant[HoldComplete["integerMultiplication"]], {left, right}]
coreIntegerLessEqual[left_, right_] := makeApplication[coreConstant[HoldComplete["integerLessEqual"]], {left, right}]
coreIntegerLess[left_, right_] := makeApplication[coreConstant[HoldComplete["integerLess"]], {left, right}]

coreExists[type_, name_HoldComplete, body_, levels_List : {1}] := With[
	{predicate = Construct[lambdaAbstraction, name, type, body, "Explicit"]},
	makeApplication[coreConstant[HoldComplete[Exists], levels], {type, predicate}]
]

coreTermSize[term_] := LeafCount[term]

(* Complexity metric for non-triviality comparisons on core propositions *)
coreComplexity[application[f_, a_]] := 1 + coreComplexity[f] + coreComplexity[a]
coreComplexity[dependentFunctionType[_, dom_, cod_, _]] := 1 + coreComplexity[dom] + coreComplexity[cod]
coreComplexity[lambdaAbstraction[_, dom_, body_, _]] := 1 + coreComplexity[dom] + coreComplexity[body]
coreComplexity[localDefinition[_, type_, val_, body_]] := 1 + coreComplexity[type] + coreComplexity[val] + coreComplexity[body]
coreComplexity[projection[_, _, inner_]] := 1 + coreComplexity[inner]
coreComplexity[_] := 1


(* Check whether Decidable[coreStatement] synthesizes in environment *)
decidableInstanceQ[environment_, coreStatement_, universeParameters_List] := If[
	! constantDeclaredQ[environment, HoldComplete[Decidable]],
	False,

	TrueQ @ Quiet @ catchKernelFailure[
		withElaborationState[{environment, <||>, <||>, universeParameters},
			With[{decType = Construct[application, coreConstant[HoldComplete[Decidable]], coreStatement]},
				! FailureQ[findInstance[decType]]
			]
		]
	]
]


(* Extract axiom closure and constructivity boolean from a verified proof *)
proofAxiomSummary[proof_TypeTheoryProof] := Module[{axioms, nonConstructive},
	axioms = Quiet[TypeTheoryAxiomClosure[proof]];
	If[ AssociationQ[axioms],
		nonConstructive = {"choice", "propositionalExtensionality", "quotientSoundness", "excludedMiddle", "functionExtensionality"};
		<|
			"Axioms" -> axioms,
			"Constructive" -> ! AnyTrue[Keys[axioms], Function[key, MemberQ[nonConstructive, key]]]
		|>,

		<|"Axioms" -> <||>, "Constructive" -> True|>
	]
]


(* Convert a core value literal to a plain Wolfram Language value *)
coreLiteralToValue[naturalLiteral[n_Integer]] := n
coreLiteralToValue[constantReference[HoldComplete["zero"], _]] := 0
coreLiteralToValue[application[constantReference[HoldComplete["successor"], _], inner_]] := Replace[coreLiteralToValue[inner], n_Integer :> n + 1]
coreLiteralToValue[application[constantReference[HoldComplete["integerOfNatural"], _], inner_]] := coreLiteralToValue[inner]
coreLiteralToValue[application[constantReference[HoldComplete["integerNegation"], _], inner_]] := Replace[coreLiteralToValue[inner], n_Integer :> -n]
coreLiteralToValue[constantReference[HoldComplete["true"], _]] := True
coreLiteralToValue[constantReference[HoldComplete["false"], _]] := False
coreLiteralToValue[other_] := other

nameToKey[HoldComplete[name_Symbol]] := SymbolName[Unevaluated[name]]
nameToKey[HoldComplete[name_String]] := name
nameToKey[other_] := ToString[other]


(* Extract counterexample values from a kernel-checked proof of Not[ForAll[xs, body]] *)
extractCounterexampleFromProof[environment_, universalCore_, proof_TypeTheoryProof] := Module[
	{term, body, spine, arguments, binderNames, pairs},
	term = Quiet @ catchKernelFailure[betaNormalize[completedProofTerm[proof]]];
	If[ FailureQ[term],
		None,

		body = Replace[term, {
			lambdaAbstraction[_, _, inner_, _] :> inner,
			_ :> None
		}];
		If[ body === None,
			None,

			(* Find application of boundVariable[0] inside the negation proof body *)
			spine = Cases[body, app_application /; First[applicationSpine[app]] === boundVariable[0] :> Last[applicationSpine[app]], {0, Infinity}];
			If[ spine === {},
				None,

				arguments = First[SortBy[spine, -Length[#] &]];
				binderNames = universalBinderNames[environment, <||>, universalCore];
				pairs = MapThread[
					Function[{name, arg}, If[ MatchQ[coreLiteralToValue[arg], _Integer | True | False], name -> coreLiteralToValue[arg], Nothing]],
					{Take[binderNames, Min[Length[binderNames], Length[arguments]]], Take[arguments, Min[Length[binderNames], Length[arguments]]]}
				];
				If[pairs === {}, None, Association[pairs]]
			]
		]
	]
]

universalBinderNames[environment_, context_, term_] := Replace[weakHeadNormalForm[environment, context, term], {
	dependentFunctionType[name_, domain_, codomain_, binder_] :> With[{id = freshFreeVariable[]},
		If[ ! propositionQ[environment, context, domain],
			Prepend[
				universalBinderNames[environment, extendContext[context, id, name, domain, binder], betaNormalize[instantiateBoundVariable[codomain, freeVariable[id]]]],
				nameToKey[name]
			],
			{}
		]
	],
	_ :> {}
}]


(* Extract witness values from a kernel-checked proof of Exists[xs, body] *)
extractWitnessFromProof[environment_, existentialCore_, proof_TypeTheoryProof] := Module[{term, values, names},
	term = Quiet @ catchKernelFailure[betaNormalize[completedProofTerm[proof]]];
	If[ FailureQ[term],
		None,

		values = extractExistsWitnessValues[term];
		names = existentialBinderNames[environment, <||>, existentialCore];
		If[ values === {} || Length[values] > Length[names],
			None,

			AssociationThread[Take[names, Length[values]], values]
		]
	]
]

extractExistsWitnessValues[term_] := Replace[applicationSpine[term], {
	{constantReference[HoldComplete["existsIntroduction"], _], {_, _, witness_, rest_}} :>
		Prepend[extractExistsWitnessValues[rest], coreLiteralToValue[witness]],
	_ :> {}
}]

existentialBinderNames[environment_, context_, term_] := Replace[weakHeadNormalForm[environment, context, term], {
	application[application[constantReference[HoldComplete[Exists], _], type_], predicate_] :> With[
		{name = Replace[predicate, {lambdaAbstraction[n_, _, _, _] :> nameToKey[n], _ :> "x"}], id = freshFreeVariable[]},
		Prepend[
			existentialBinderNames[
				environment,
				extendContext[context, id, HoldComplete[x], type, "Explicit"],
				betaNormalize[Construct[application, predicate, freeVariable[id]]]
			],
			name
		]
	],
	_ :> {}
}]


(* ::Section:: *)
(*Enhanced Untrusted Prover (All Outputs Strictly Kernel-Verified)*)


(* Start a proof directly from a core statement *)
proveFromCore[environment_, coreStatement_, universeParameters_List, tactics_List] := Module[{state, finished},
	state = newProofState[environment, coreStatement, universeParameters];
	finished = Quiet @ catchKernelFailure[runTactics[state, tactics]];
	verifyProofInKernel[environment, coreStatement, universeParameters, finished]
]

makeHeldName[prefix_String, id_Integer] := With[{s = prefix <> IntegerString[id]}, HoldComplete[s]]

(* Run tacticFn on remaining open goals, stopping immediately if a step makes no progress *)
closeAllGoalsWith[state_TypeTheoryProof, tacticFn_] := Module[{cur = state, next, step = 0},
	While[ ! FailureQ[cur] && cur["Goals"] =!= {} && step < 40,
		next = tacticFn[cur];
		If[ FailureQ[next] || next === cur,
			cur = If[FailureQ[next], next, Failure["NoProgress", <||>]];
			Break[],
			cur = next
		];
		step = step + 1
	];
	cur
]

closeGoalBasic[proof_TypeTheoryProof] := Module[{prepared, attempt},
	attempt = Quiet @ catchKernelFailure[TypeTheoryTactic[Automatic][proof]];
	If[ ! FailureQ[attempt],
		attempt,

		attempt = Quiet @ catchKernelFailure[closeContradictoryDisequalityInState[proof]];
		If[ ! FailureQ[attempt],
			attempt,

			prepared = Quiet @ catchKernelFailure[applyEasyImplicationHypotheses[proof]];
			If[ MatchQ[prepared, _TypeTheoryProof] && prepared =!= proof,
				attempt = Quiet @ catchKernelFailure[TypeTheoryTactic[Automatic][prepared]];
				If[ ! FailureQ[attempt],
					attempt,
					trySpecializedBasicTactics[prepared]
				],
				trySpecializedBasicTactics[proof]
			]
		]
	]
]

(* Unfold Power[base, successor[exp]] -> Power[base, exp] * base inside goal (definitionally equal in Prelude) *)
unfoldPowerSuccessorInGoal[proof_TypeTheoryProof] := Module[{d = First[proof], g, cur, env, newType, newG},
	If[ d["Goals"] === {},
		proof,

		g = First[d["Goals"]];
		cur = currentGoal[d, g];
		env = d["Environment"];
		newType = ReplaceAll[
			cur["Type"],
			application[application[constantReference[HoldComplete[Power], _], base_], application[constantReference[HoldComplete["successor"], _], exp_]] :>
				With[{rew = coreNaturalTimes[coreNaturalPower[base, exp], base]}, rew /; True]
		];
		If[ newType === cur["Type"],
			proof,

			newG = freshMetavariableId[];
			proofState @ solveGoal[
				d,
				g,
				metavariable[newG],
				{newG -> <|"Context" -> cur["Context"], "Type" -> newType, "Case" -> None|>}
			]
		]
	]
]

(* Prove natural inequality a <= b by contradiction via lessEqualTotality (handles x^2 + y^2 == 25 |- x <= 5 via NonlinearArithmetic!) *)
proveNaturalBoundByContradictionInState[proof_TypeTheoryProof] := Module[{d = First[proof], g, cur, env, aTerm, bTerm, totApplied, orType, idL, idR, gL, gR, ctxL, ctxR, motive, elimTerm, splitSt, closed},
	g = First[d["Goals"]];
	cur = currentGoal[d, g];
	env = d["Environment"];
	If[ ! constantDeclaredQ[env, HoldComplete["lessEqualTotality"]] || ! constantDeclaredQ[env, HoldComplete["falseElimination"]],
		Failure["Unavailable", <||>],

		Replace[weakHeadNormalForm[env, cur["Context"], cur["Type"]], {
			application[application[constantReference[HoldComplete[LessEqual], _], a_], b_] :> (
				aTerm = a;
				bTerm = b;
				totApplied = makeApplication[coreConstant[HoldComplete["lessEqualTotality"]], {aTerm, bTerm}];
				orType = weakHeadNormalForm[env, cur["Context"], inferType[env, cur["Context"], totApplied]];
				If[ ! MatchQ[orType, application[application[constantReference[HoldComplete[Or], _], _], _]],
					Failure["NotTotalityOr", <||>],

					With[{leftType = Last[First[orType]], rightType = Last[orType]},
						idL = freshFreeVariable[];
						idR = freshFreeVariable[];
						gR = freshMetavariableId[];
						ctxL = extendContext[cur["Context"], idL, makeHeldName["hLe", idL], leftType, "Explicit"];
						ctxR = extendContext[cur["Context"], idR, makeHeldName["hGt", idR], rightType, "Explicit"];
						motive = Construct[lambdaAbstraction, HoldComplete["tot"], orType, liftBoundVariables[cur["Type"], 1, 0], "Explicit"];
						elimTerm = makeApplication[
							coreConstant[recursorName[HoldComplete[Or]], {}],
							{
								leftType,
								rightType,
								motive,
								makeLambda[ctxL, {idL}, freeVariable[idL]],
								pendingAbstraction[ctxR, {idR}, makeApplication[coreConstant[HoldComplete["falseElimination"]], {cur["Type"], metavariable[gR]}]],
								totApplied
							}
						];
						splitSt = proofState @ solveGoal[d, g, elimTerm, {gR -> <|"Context" -> ctxR, "Type" -> coreFalse[], "Case" -> None|>}];
						closed = Quiet @ catchKernelFailure[TypeTheoryTactic["NonlinearArithmetic"][splitSt]];
						If[! FailureQ[closed] && closed["Goals"] === {}, closed, Failure["ContradictionFailed", <||>]]
					]
				]
			),
			_ :> Failure["NotNaturalLessEqual", <||>]
		}]
	]
]

trySpecializedBasicTactics[proof_TypeTheoryProof] := Module[{attempt, powUnfolded},
	powUnfolded = unfoldPowerSuccessorInGoal[proof];
	If[ powUnfolded =!= proof,
		attempt = Quiet @ catchKernelFailure[TypeTheoryTactic[Automatic][powUnfolded]];
		If[! FailureQ[attempt], attempt, trySpecializedBasicTacticsInner[powUnfolded]],
		trySpecializedBasicTacticsInner[proof]
	]
]

trySpecializedBasicTacticsInner[proof_TypeTheoryProof] := Module[{attempt},
	attempt = Quiet @ catchKernelFailure[proveIntegerLinearInState[proof]];
	If[ ! FailureQ[attempt],
		attempt,

		attempt = Quiet @ catchKernelFailure[proveNaturalBoundByContradictionInState[proof]];
		If[ ! FailureQ[attempt],
			attempt,

			attempt = Quiet @ catchKernelFailure[proveNaturalSubtractionInState[proof]];
			If[ ! FailureQ[attempt],
				attempt,

				attempt = Quiet @ catchKernelFailure[proveMultiplicationCancellationInState[proof]];
				If[ ! FailureQ[attempt],
					attempt,

					attempt = Quiet @ catchKernelFailure[proveEquationalWithConjunctionsInState[proof]];
					If[ ! FailureQ[attempt],
						attempt,

						proveFromExcludedMiddleInState[proof]
					]
				]
			]
		]
	]
]

(* Close any goal when context contains h : Not[P] where P is provable by Reflexivity, Decide, or LinearArithmetic (e.g. 0 != 0) *)
closeContradictoryDisequalityInState[proof_TypeTheoryProof] := Module[{data, goal, current, env, ctx, negId, hit},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	ctx = current["Context"];
	If[ ! constantDeclaredQ[env, HoldComplete["falseElimination"]],
		Failure["Unavailable", <||>],

		hit = SelectFirst[
			Keys[ctx],
			Function[id,
				Replace[weakHeadNormalForm[env, ctx, ctx[id]["Type"]], {
					dependentFunctionType[_, inner_, constantReference[HoldComplete[False], _], _] :>
						With[{sub = proofSubgoalInContext[env, data["UniverseParameters"], ctx, inner]},
							! FailureQ[sub]
						],
					_ :> False
				}]
			],
			None
		];
		If[ hit === None,
			Failure["NoContradictoryNegation", <||>],

			With[{inner = First[Rest[weakHeadNormalForm[env, ctx, ctx[hit]["Type"]]]]},
				{pInner = proofSubgoalInContext[env, data["UniverseParameters"], ctx, inner]},
				{falseTerm = Construct[application, freeVariable[hit], pInner]},
				{elimTerm = makeApplication[coreConstant[HoldComplete["falseElimination"]], {current["Type"], falseTerm}]},
				proofState @ solveGoal[data, goal, elimTerm, {}]
			]
		]
	]
]

(* Prove a small proposition 'target' in local context 'ctx' using Reflexivity, Decide, or LinearArithmetic; returns core proof term or Failure *)
proofSubgoalInContext[env_, uParams_List, ctx_Association, target_] := Module[{root, st, res},
	root = freshMetavariableId[];
	st = proofState[<|
		"Environment" -> env,
		"Statement" -> target,
		"UniverseParameters" -> uParams,
		"Root" -> root,
		"Goals" -> {root},
		"Metavariables" -> <|root -> <|"Context" -> ctx, "Type" -> target, "Case" -> None|>|>,
		"Assignments" -> <||>
	|>];
	res = SelectFirst[
		{
			Quiet @ catchKernelFailure[TypeTheoryTactic["Reflexivity"][st]],
			Quiet @ catchKernelFailure[TypeTheoryTactic["Decide"][st]],
			Quiet @ catchKernelFailure[TypeTheoryTactic["LinearArithmetic"][st]]
		},
		Function[r, MatchQ[r, _TypeTheoryProof] && r["Goals"] === {}],
		Failure["NotClosed", <||>]
	];
	If[ FailureQ[res],
		res,
		instantiateProofTerm[First[res], metavariable[root]]
	]
]

(* Specialize implication hypotheses ih : H => C in context when H is immediately provable (e.g. 4 <= k + 4 in shifted induction) *)
applyEasyImplicationHypotheses[proof_TypeTheoryProof] := Module[{data, goal, current, env, ctx, existingTypes, hit},
	data = First[proof];
	If[ data["Goals"] === {},
		proof,

		goal = First[data["Goals"]];
		current = currentGoal[data, goal];
		env = data["Environment"];
		ctx = current["Context"];
		existingTypes = Lookup[Values[ctx], "Type"];
		hit = SelectFirst[
			Keys[ctx],
			Function[id,
				Replace[weakHeadNormalForm[env, ctx, ctx[id]["Type"]], {
					dependentFunctionType[_, premise_, conclusion_, _] /;
						looseBoundRange[conclusion] == 0 &&
						conclusion =!= coreFalse[] &&
						! MemberQ[existingTypes, conclusion] &&
						TrueQ[Quiet @ propositionQ[env, ctx, premise]] :>
							! FailureQ[proofSubgoalInContext[env, data["UniverseParameters"], ctx, premise]],
					_ :> False
				}]
			],
			None
		];
		If[ hit === None,
			proof,

			With[{hType = weakHeadNormalForm[env, ctx, ctx[hit]["Type"]]},
				{premise = First[Rest[hType]], conclusion = First[Drop[hType, 2]]},
				{pPrem = proofSubgoalInContext[env, data["UniverseParameters"], ctx, premise]},
				{
					cId = freshFreeVariable[],
					newGoal = freshMetavariableId[],
					conclProof = Construct[application, freeVariable[hit], pPrem]
				},
				{ctx2 = extendContext[ctx, cId, makeHeldName["hMP", cId], conclusion, "Explicit"]},
				{
					stepState = proofState @ solveGoal[
						data,
						goal,
						Construct[application, pendingAbstraction[ctx2, {cId}, metavariable[newGoal]], conclProof],
						{newGoal -> <|"Context" -> ctx2, "Type" -> current["Type"], "Case" -> None|>}
					]
				},
				applyEasyImplicationHypotheses[stepState]
			]
		]
	]
]


(* Main enhanced prover: tries Automatic first, then specialized untrusted tactics, always kernel-verified. Running out of
   timeLimit gives Failure["TimedOut", ...] however the time limit's abort arrives: code inside the search can catch it
   and abort again, and that plain abort passes TimeConstrained to the CheckAbort here (4 <= n => n^2 <= 2^n, 2026-11-26),
   so an abort that comes once the time is up counts as the time limit's. *)
enhancedProveCore[environment_, coreStatement_, universeParameters_List, timeLimit_ : 5] := With[{started = AbsoluteTime[]}, CheckAbort[
	TimeConstrained[
		Module[{state, result},
			state = newProofState[environment, coreStatement, universeParameters];

			(* 1. Standard portfolio *)
			result = verifyProofInKernel[environment, coreStatement, universeParameters, Quiet @ catchKernelFailure[TypeTheoryTactic[Automatic][state]]];
			If[! FailureQ[result], result,

			(* 2. Boolean domain universal/existential decision and Boolean counterexample *)
			result = verifyProofInKernel[environment, coreStatement, universeParameters, Quiet @ catchKernelFailure[tryBooleanProof[state]]];
			If[! FailureQ[result], result,

			result = verifyProofInKernel[environment, coreStatement, universeParameters, Quiet @ catchKernelFailure[tryNegatedBooleanUniversalProof[environment, coreStatement, universeParameters]]];
			If[! FailureQ[result], result,

			(* 3. Specialized single-goal strategies after introducing binders *)
			result = verifyProofInKernel[environment, coreStatement, universeParameters, Quiet @ catchKernelFailure[trySpecializedSingleGoal[state]]];
			If[! FailureQ[result], result,

			(* 4. Existential witness over algebraic/equational premises (e.g. Surjective from involution) *)
			result = verifyProofInKernel[environment, coreStatement, universeParameters, Quiet @ catchKernelFailure[tryAlgebraicWitnessProof[state]]];
			If[! FailureQ[result], result,

			(* 5. Induction and shifted-induction / finite-case unrolling on NonNegativeIntegers *)
			result = verifyProofInKernel[environment, coreStatement, universeParameters, Quiet @ catchKernelFailure[tryNaturalInductionProof[state]]];
			If[! FailureQ[result], result,

			Failure["NoProofFound", <|
				"MessageTemplate" -> "No kernel-verified proof was found for `1`.",
				"MessageParameters" -> {coreToTypeTheoryTerm[environment, <||>, coreStatement]}
			|>]
			]]]]]]
		],
		timeLimit,
		proofTimedOut[timeLimit]
	],
	If[ AbsoluteTime[] - started >= 0.95 * timeLimit,
		proofTimedOut[timeLimit],
		Failure["Aborted", <|"MessageTemplate" -> "Proof search aborted.", "MessageParameters" -> {}|>]
	]
]]

proofTimedOut[timeLimit_] := Failure["TimedOut", <|"MessageTemplate" -> "Proof search timed out after `1` seconds.", "MessageParameters" -> {timeLimit}|>]


(* Refute a negated Boolean universal Not[ForAll[{b1 : Booleans, ...}, body]] directly inside enhancedProveCore *)
tryNegatedBooleanUniversalProof[environment_, coreStmt_, uParams_List] := Replace[weakHeadNormalForm[environment, <||>, coreStmt], {
	dependentFunctionType[_, universal_, constantReference[HoldComplete[False], _], _] :>
		tryBooleanCounterexample[environment, universal, coreStmt, uParams],
	_ :> Failure["NotNegatedUniversal", <||>]
}]

(* Introduce all leading binders of a proof state *)
introduceAll[TypeTheoryProof[data_Association]] := If[ data["Goals"] === {},
	TypeTheoryProof[data],
	proofState[introducedHypotheses[data, First[data["Goals"]], 0]]
]


(* Strategy 2: Depth-first case-split of all Boolean variables in each goal, closing leaves with Reflexivity/Decide/Automatic *)
tryBooleanProof[state_TypeTheoryProof] := Module[{introduced, data, goal, current, boolIds},
	introduced = introduceAll[state];
	data = First[introduced];
	If[ data["Goals"] === {},
		introduced,

		goal = First[data["Goals"]];
		current = currentGoal[data, goal];
		boolIds = Select[Keys[current["Context"]], Function[id,
			weakHeadNormalForm[data["Environment"], current["Context"], current["Context"][id]["Type"]] === coreBooleans[]
		]];
		If[ boolIds === {} || Length[boolIds] > 3,
			Failure["NoBooleanVariables", <||>],
			splitAndCloseBooleansDF[introduced, 32]
		]
	]
]

splitAndCloseBooleansDF[proof_TypeTheoryProof, 0] := Failure["BooleanSplitLimit", <||>]
splitAndCloseBooleansDF[proof_TypeTheoryProof, fuel_Integer] := If[ proof["Goals"] === {},
	proof,
	Module[{d = First[proof], g, ctx, boolId, next},
		g = First[d["Goals"]];
		ctx = currentGoal[d, g]["Context"];
		boolId = SelectFirst[Keys[ctx], Function[id, weakHeadNormalForm[d["Environment"], ctx, ctx[id]["Type"]] === coreBooleans[]], None];
		If[ boolId =!= None,
			With[{nm = ctx[boolId]["Name"]},
				next = Quiet @ catchKernelFailure[Replace[nm, HoldComplete[sym_] :> TypeTheoryTactic["Cases", sym][proof]]];
				If[FailureQ[next], next, splitAndCloseBooleansDF[next, fuel - 1]]
			],
			next = Quiet @ catchKernelFailure[TypeTheoryTactic["Reflexivity"][proof]];
			If[ FailureQ[next],
				next = Quiet @ catchKernelFailure[TypeTheoryTactic["Decide"][proof]]
			];
			If[ FailureQ[next],
				next = Quiet @ catchKernelFailure[closeGoalBasic[proof]]
			];
			If[FailureQ[next], next, splitAndCloseBooleansDF[next, fuel - 1]]
		]
	]
]


(* Strategy 3: Introduce all variables/hypotheses and run specialized single-goal tactics *)
trySpecializedSingleGoal[state_TypeTheoryProof] := Module[{introduced},
	introduced = introduceAll[state];
	If[ FailureQ[introduced] || introduced["Goals"] === {},
		introduced,
		closeAllGoalsWith[introduced, closeGoalBasic]
	]
]


(* Helper: unpack conjunction hypotheses And[A, B] in context into separate hypotheses *)
unpackConjunctionHypotheses[proof_TypeTheoryProof] := Module[{data, goal, current, env, andEntry, id, lhs, rhs, name1, name2, p1, p2, p3},
	data = First[proof];
	If[ data["Goals"] === {},
		proof,

		goal = First[data["Goals"]];
		current = currentGoal[data, goal];
		env = data["Environment"];
		andEntry = SelectFirst[
			Keys[current["Context"]],
			Function[k, MatchQ[weakHeadNormalForm[env, current["Context"], current["Context"][k]["Type"]], application[application[constantReference[HoldComplete[And], _], _], _]]],
			None
		];
		If[ andEntry === None || ! constantDeclaredQ[env, HoldComplete["andEliminationLeft"]],
			proof,

			With[{andType = weakHeadNormalForm[env, current["Context"], current["Context"][andEntry]["Type"]]},
				{leftType = Last[First[andType]], rightType = Last[andType]},
				(* Avoid infinite unpacking if both conjuncts already exist in context *)
				With[{existingTypes = Lookup[Values[current["Context"]], "Type"]},
					If[ MemberQ[existingTypes, leftType] && MemberQ[existingTypes, rightType],
						proof,

						With[{id1 = freshFreeVariable[], id2 = freshFreeVariable[], newGoal = freshMetavariableId[], hTerm = freeVariable[andEntry]},
							{
								pLeft = makeApplication[coreConstant[HoldComplete["andEliminationLeft"]], {leftType, rightType, hTerm}],
								pRight = makeApplication[coreConstant[HoldComplete["andEliminationRight"]], {leftType, rightType, hTerm}]
							},
							{
								ctx1 = extendContext[current["Context"], id1, makeHeldName["hLeft", id1], leftType, "Explicit"]
							},
							{
								ctx2 = extendContext[ctx1, id2, makeHeldName["hRight", id2], rightType, "Explicit"]
							},
							{
								solved = solveGoal[
									data,
									goal,
									makeApplication[pendingAbstraction[ctx2, {id1, id2}, metavariable[newGoal]], {pLeft, pRight}],
									{newGoal -> <|"Context" -> ctx2, "Type" -> current["Type"], "Case" -> None|>}
								]
							},
							unpackConjunctionHypotheses[proofState[solved]]
						]
					]
				]
			]
		]
	]
]


(* Specialized tactic A: Unpack conjunction hypotheses, then run Automatic / FindEquationalProof / LinearArithmetic *)
proveEquationalWithConjunctionsInState[proof_TypeTheoryProof] := Module[{unpacked, attempt},
	unpacked = Quiet @ catchKernelFailure[unpackConjunctionHypotheses[proof]];
	If[ FailureQ[unpacked] || unpacked === proof,
		Failure["NoConjunctions", <||>],

		attempt = Quiet @ catchKernelFailure[TypeTheoryTactic[Automatic][unpacked]];
		If[ ! FailureQ[attempt] && attempt["Goals"] === {},
			attempt,
			Failure["NotClosedAfterUnpack", <||>]
		]
	]
]


(* Specialized tactic B: Natural number Subtract[a, b] elimination using b <= a *)
proveNaturalSubtractionInState[proof_TypeTheoryProof] := Module[
	{data, goal, current, env, subTerms, subTerm, aTerm, bTerm, leHypId, kId, eqId, newGoalId, leType, existsType, eqType, witnessProof, subProof},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	If[ ! AllTrue[HoldComplete /@ {Subtract, LessEqual, Exists, "additionSubtractionCancellation", "additionCommutativity", "existsIntroduction"}, Function[c, constantDeclaredQ[env, c]]],
		Failure["Unavailable", <||>],

		subTerms = Cases[current["Type"], application[application[constantReference[HoldComplete[Subtract], _], a_], b_] :> {a, b}, {0, Infinity}];
		If[ subTerms === {},
			Failure["NoSubtraction", <||>],

			{aTerm, bTerm} = First[subTerms];
			leType = coreNaturalLessEqual[bTerm, aTerm];
			leHypId = SelectFirst[Keys[current["Context"]], Function[id, withKernelCaches[definitionallyEqualQ[env, current["Context"], current["Context"][id]["Type"], leType]]], None];
			If[ leHypId === None,
				Failure["NoOrderHypothesis", <||>],

				(* Build proof of Exists[{Typed[k, NonNegativeIntegers]}, a == k + b] from h : b <= a by LessEqual recursor *)
				witnessProof = buildLessEqualAdditionWitness[env, current["Context"], bTerm, aTerm, freeVariable[leHypId]];
				If[ FailureQ[witnessProof],
					witnessProof,

					kId = freshFreeVariable[];
					eqId = freshFreeVariable[];
					newGoalId = freshMetavariableId[];
					With[
						{
							kName = makeHeldName["kSub", kId],
							eqName = makeHeldName["hSubEq", eqId]
						},
						{
							eqBody = coreEquality[coreNaturals[], aTerm, coreNaturalPlus[freeVariable[kId], bTerm], {1}],
							ctx1 = extendContext[current["Context"], kId, kName, coreNaturals[], "Explicit"]
						},
						{
							ctx2 = extendContext[ctx1, eqId, eqName, eqBody, "Explicit"],
							existsPred = makeLambda[ctx1, {kId}, eqBody],
							motive = Construct[lambdaAbstraction, HoldComplete["w"], coreExists[coreNaturals[], kName, abstractFreeVariable[eqBody, kId]], liftBoundVariables[current["Type"], 1, 0], "Explicit"]
						},
						{
							minor = pendingAbstraction[ctx2, {kId, eqId}, metavariable[newGoalId]]
						},
						{
							elimTerm = makeApplication[
								coreConstant[recursorName[HoldComplete[Exists]], {1}],
								{coreNaturals[], existsPred, motive, minor, witnessProof}
							]
						},
						{
							stepState = proofState @ solveGoal[
								data,
								goal,
								elimTerm,
								{newGoalId -> <|"Context" -> ctx2, "Type" -> current["Type"], "Case" -> None|>}
							]
						},
						(* Rewrite a -> k + b, then Subtract[k + b, b] -> k; stop as soon as Goals === {}! *)
						subProof = Quiet @ catchKernelFailure[
							With[{s1 = Replace[eqName, HoldComplete[sym_] :> TypeTheoryTactic["Rewrite", sym][stepState]]},
								If[ FailureQ[s1] || s1["Goals"] === {},
									s1,
									With[{s2 = TypeTheoryTactic["Rewrite", "additionSubtractionCancellation"][s1]},
										If[ FailureQ[s2] || s2["Goals"] === {},
											s2,
											TypeTheoryTactic[Automatic][s2]
										]
									]
								]
							]
						];
						If[ ! FailureQ[subProof] && subProof["Goals"] === {},
							subProof,
							Failure["SubtractionEliminationFailed", <||>]
						]
					]
				]
			]
		]
	]
]

(* Prove Exists[{Typed[k, NonNegativeIntegers]}, a == k + b] from leProof : b <= a using InductiveRecursor[LessEqual] *)
buildLessEqualAdditionWitness[env_, context_, bTerm_, aTerm_, leProof_] := Module[
	{nId, kId, wId, hId, pId, motive, baseCase, stepCase, recTerm, existsType},
	nId = freshFreeVariable[];
	kId = freshFreeVariable[];
	wId = freshFreeVariable[];
	hId = freshFreeVariable[];
	pId = freshFreeVariable[];
	With[{eqFn = Function[{rhs, kVar}, coreEquality[coreNaturals[], rhs, coreNaturalPlus[kVar, bTerm], {1}]]},
		existsType = Function[rhs,
			With[{tmpId = freshFreeVariable[]},
				With[{tmpCtx = extendContext[context, tmpId, HoldComplete["k"], coreNaturals[], "Explicit"]},
					coreExists[coreNaturals[], HoldComplete["k"], abstractFreeVariable[eqFn[rhs, freeVariable[tmpId]], tmpId], {1}]
				]
			]
		];
		(* Base case: Exists[k, b == k + b], witness 0, proof 0 + b == b by equalitySymmetry[additionZeroLeft[b]] *)
		If[ ! constantDeclaredQ[env, HoldComplete["additionZeroLeft"]] || ! constantDeclaredQ[env, HoldComplete["additionSuccessorLeft"]],
			Failure["MissingPreludeLemmas", <||>],

			With[
				{
					ctxN = extendContext[context, nId, HoldComplete["n"], coreNaturals[], "Explicit"],
					ctxK = extendContext[context, kId, HoldComplete["k"], coreNaturals[], "Explicit"]
				},
				{
					motiveBody = existsType[freeVariable[nId]],
					basePred = makeLambda[ctxK, {kId}, eqFn[bTerm, freeVariable[kId]]],
					baseEqProof = makeApplication[
						coreConstant[HoldComplete["equalitySymmetry"], {1}],
						{coreNaturals[], coreNaturalPlus[naturalLiteral[0], bTerm], bTerm, makeApplication[coreConstant[HoldComplete["additionZeroLeft"]], {bTerm}]}
					]
				},
				{
					baseCase = makeApplication[
						coreConstant[HoldComplete["existsIntroduction"], {1}],
						{coreNaturals[], basePred, naturalLiteral[0], baseEqProof}
					],
					ctxM = extendContext[context, nId, HoldComplete["m"], coreNaturals[], "Explicit"]
				},
				{
					ctxML = extendContext[ctxM, hId, HoldComplete["hle"], coreNaturalLessEqual[bTerm, freeVariable[nId]], "Explicit"]
				},
				{
					ctxMIH = extendContext[ctxML, pId, HoldComplete["ih"], existsType[freeVariable[nId]], "Explicit"]
				},
				{
					ctxStepK = extendContext[ctxMIH, wId, HoldComplete["w"], coreNaturals[], "Explicit"]
				},
				{
					succN = Construct[application, coreConstant[HoldComplete["successor"]], freeVariable[nId]],
					succW = Construct[application, coreConstant[HoldComplete["successor"]], freeVariable[wId]]
				},
				{
					ctxStepEq = extendContext[ctxStepK, kId, HoldComplete["heq"], eqFn[freeVariable[nId], freeVariable[wId]], "Explicit"],
					succPred = makeLambda[ctxStepK, {wId}, eqFn[succN, freeVariable[wId]]],
					innerPred = makeLambda[ctxStepK, {wId}, eqFn[freeVariable[nId], freeVariable[wId]]]
				},
				{
					(* m + 1 == (w + b) + 1 == (w + 1) + b *)
					congStep = makeApplication[
						coreConstant[HoldComplete["equalityCongruence"], {1, 1}],
						{coreNaturals[], coreNaturals[], freeVariable[nId], coreNaturalPlus[freeVariable[wId], bTerm], coreConstant[HoldComplete["successor"]], freeVariable[kId]}
					],
					succLeftSym = makeApplication[
						coreConstant[HoldComplete["equalitySymmetry"], {1}],
						{
							coreNaturals[],
							coreNaturalPlus[succW, bTerm],
							Construct[application, coreConstant[HoldComplete["successor"]], coreNaturalPlus[freeVariable[wId], bTerm]],
							makeApplication[coreConstant[HoldComplete["additionSuccessorLeft"]], {freeVariable[wId], bTerm}]
						}
					]
				},
				{
					stepEqProof = makeApplication[
						coreConstant[HoldComplete["equalityTransitivity"], {1}],
						{
							coreNaturals[],
							succN,
							Construct[application, coreConstant[HoldComplete["successor"]], coreNaturalPlus[freeVariable[wId], bTerm]],
							coreNaturalPlus[succW, bTerm],
							congStep,
							succLeftSym
						}
					]
				},
				{
					stepWitness = makeApplication[
						coreConstant[HoldComplete["existsIntroduction"], {1}],
						{coreNaturals[], succPred, succW, stepEqProof}
					],
					existsMotive = Construct[lambdaAbstraction, HoldComplete["ex"], existsType[freeVariable[nId]], liftBoundVariables[existsType[succN], 1, 0], "Explicit"]
				},
				{
					stepBody = makeApplication[
						coreConstant[recursorName[HoldComplete[Exists]], {1}],
						{coreNaturals[], innerPred, existsMotive, makeLambda[ctxStepEq, {wId, kId}, stepWitness], freeVariable[pId]}
					]
				},
				{
					motiveFinal = makeLambda[ctxML, {nId, hId}, existsType[freeVariable[nId]]],
					stepFinal = makeLambda[ctxMIH, {nId, hId, pId}, stepBody]
				},
				recTerm = makeApplication[
					coreConstant[recursorName[HoldComplete[LessEqual]], {}],
					{bTerm, motiveFinal, baseCase, stepFinal, aTerm, leProof}
				];
				recTerm
			]
		]
	]
]


(* Specialized tactic C: Multiplication cancellation over NonNegativeIntegers (c != 0 or 1 <= c and a * c == b * c |- a == b) *)
proveMultiplicationCancellationInState[proof_TypeTheoryProof] := Module[
	{data, goal, current, env, eqType, aTerm, bTerm, mulHyp, cVarId, cName, splitState, closed},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	If[ ! constantDeclaredQ[env, HoldComplete["multiplicationCancellation"]],
		Failure["Unavailable", <||>],

		eqType = weakHeadNormalForm[env, current["Context"], current["Type"]];
		If[ ! MatchQ[eqType, application[application[application[constantReference[HoldComplete[Equal], _], type_], _], _] /; naturalNumberTypeQ[env, current["Context"], type]],
			Failure["NotNaturalEquation", <||>],

			{aTerm, bTerm} = {Last[First[eqType]], Last[eqType]};
			(* Find an equation hypothesis of the form a * c == b * c or c * a == c * b *)
			mulHyp = SelectFirst[
				Keys[current["Context"]],
				Function[id, MatchQ[
					weakHeadNormalForm[env, current["Context"], current["Context"][id]["Type"]],
					application[application[application[constantReference[HoldComplete[Equal], _], type_],
						application[application[constantReference[HoldComplete[Times], _], _], _]],
						application[application[constantReference[HoldComplete[Times], _], _], _]] /; naturalNumberTypeQ[env, current["Context"], type]
				]],
				None
			];
			If[ mulHyp === None,
				Failure["NoProductEquation", <||>],

				With[{hType = weakHeadNormalForm[env, current["Context"], current["Context"][mulHyp]["Type"]]},
					{lhs = Last[First[hType]], rhs = Last[hType]},
					{l1 = Last[First[lhs]], l2 = Last[lhs], r1 = Last[First[rhs]], r2 = Last[rhs]},
					cVarId = Which[
						l2 === r2 && MatchQ[l2, freeVariable[_]], First[l2],
						l1 === r1 && MatchQ[l1, freeVariable[_]], First[l1],
						True, None
					];
					If[ cVarId === None || ! KeyExistsQ[current["Context"], cVarId],
						Failure["NoCommonFactorVariable", <||>],

						cName = current["Context"][cVarId]["Name"];
						splitState = Quiet @ catchKernelFailure[Replace[cName, HoldComplete[sym_] :> TypeTheoryTactic["Cases", sym][proof]]];
						If[ FailureQ[splitState],
							splitState,

							closed = closeAllGoalsWith[splitState, Function[cur,
								With[{auto = Quiet @ catchKernelFailure[TypeTheoryTactic[Automatic][cur]]},
									If[ ! FailureQ[auto],
										auto,
										With[{intro = introduceAll[cur]},
											With[{contra = Quiet @ catchKernelFailure[closeContradictoryDisequalityInState[intro]]},
												If[ ! FailureQ[contra],
													contra,
													applyMultiplicationCancellationStep[intro]
												]
											]
										]
									]
								]
							]];
							If[! FailureQ[closed] && closed["Goals"] === {}, closed, Failure["CancellationFailed", <||>]]
						]
					]
				]
			]
		]
	]
]

applyMultiplicationCancellationStep[proof_TypeTheoryProof] := Module[
	{data, goal, current, env, eqType, aTerm, bTerm, mulHypId, kTerm, prodEq, commProof},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	eqType = weakHeadNormalForm[env, current["Context"], current["Type"]];
	If[ ! MatchQ[eqType, application[application[application[constantReference[HoldComplete[Equal], _], _], _], _]],
		Failure["NotEquation", <||>],

		{aTerm, bTerm} = {Last[First[eqType]], Last[eqType]};
		mulHypId = SelectFirst[
			Keys[current["Context"]],
			Function[id, MatchQ[
				weakHeadNormalForm[env, current["Context"], current["Context"][id]["Type"]],
				application[application[application[constantReference[HoldComplete[Equal], _], _],
					application[application[constantReference[HoldComplete[Times], _], _], _]],
					application[application[constantReference[HoldComplete[Times], _], _], _]]
			]],
			None
		];
		If[ mulHypId === None,
			Failure["NoMulHyp", <||>],

			With[{hType = weakHeadNormalForm[env, current["Context"], current["Context"][mulHypId]["Type"]]},
				{lhs = Last[First[hType]], rhs = Last[hType]},
				{l1 = Last[First[lhs]], l2 = Last[lhs], r1 = Last[First[rhs]], r2 = Last[rhs]},
				kTerm = Replace[{l1, l2, r1, r2}, {
					{a_, application[constantReference[HoldComplete["successor"], _], k_], b_, application[constantReference[HoldComplete["successor"], _], k_]} :> k,
					{application[constantReference[HoldComplete["successor"], _], k_], a_, application[constantReference[HoldComplete["successor"], _], k_], b_} :> k,
					_ :> None
				}];
				If[ kTerm === None,
					Failure["NotSuccessorFactor", <||>],

					(* Build proof of (k + 1) * a == (k + 1) * b via PolynomialReduce / Ring from mulHypId *)
					prodEq = coreEquality[
						coreNaturals[],
						coreNaturalTimes[Construct[application, coreConstant[HoldComplete["successor"]], kTerm], aTerm],
						coreNaturalTimes[Construct[application, coreConstant[HoldComplete["successor"]], kTerm], bTerm],
						{1}
					];
					With[{eqGoalId = freshMetavariableId[]},
						{
							stepState = proofState @ solveGoal[
								data,
								goal,
								makeApplication[coreConstant[HoldComplete["multiplicationCancellation"]], {kTerm, aTerm, bTerm, metavariable[eqGoalId]}],
								{eqGoalId -> <|"Context" -> current["Context"], "Type" -> prodEq, "Case" -> None|>}
							]
						},
						Quiet @ catchKernelFailure[TypeTheoryTactic["PolynomialReduce"][stepState]]
					]
				]
			]
		]
	]
]


(* Specialized tactic D: Kernel-checked linear arithmetic over Integers (in TypeTheoryEnvironment["Integers"]) *)
proveIntegerLinearInState[proof_TypeTheoryProof] := Module[
	{data, goal, current, env, goalType, goalSides, isStrict, ineqHyps},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	If[ ! constantDeclaredQ[env, HoldComplete["integerLessEqual"]] || ! constantDeclaredQ[env, HoldComplete["integerAddition"]],
		Failure["IntegersUnavailable", <||>],

		goalType = current["Type"];
		goalSides = extractIntegerOrderGoal[env, current["Context"], goalType];
		If[ goalSides === None,
			Failure["NotIntegerInequality", <||>],

			(* Unpack every integerLessEqual / integerLess hypothesis via Exists elimination, then prove goal *)
			unpackIntegerInequalitiesAndSolve[proof, goalSides]
		]
	]
]

extractIntegerOrderGoal[env_, context_, type_] := Replace[type, {
	application[application[constantReference[HoldComplete["integerLessEqual"], _], a_], b_] :> {a, b, False},
	application[application[constantReference[HoldComplete["integerLess"], _], a_], b_] :> {coreIntegerAddition[a, coreIntegerLiteral[1]], b, True},
	application[application[constantReference[HoldComplete["integerGreaterEqual"], _], a_], b_] :> {b, a, False},
	application[application[constantReference[HoldComplete["integerGreater"], _], a_], b_] :> {coreIntegerAddition[b, coreIntegerLiteral[1]], a, True},
	constantReference[HoldComplete[False], _] :> "Contradiction",
	_ :> None
}]

unpackIntegerInequalitiesAndSolve[proof_TypeTheoryProof, goalInfo_] := Module[
	{data, goal, current, env, intIneqIds, unpackedState, slackIds},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	intIneqIds = Select[Keys[current["Context"]], Function[id,
		MatchQ[extractIntegerOrderGoal[env, current["Context"], current["Context"][id]["Type"]], {_, _, _}]
	]];
	(* Unpack each integer inequality hypothesis into (k_i : NonNegativeIntegers, eq_i : b == a + k_i) *)
	{unpackedState, slackIds} = Fold[
		Function[{acc, id},
			With[{st = First[acc], slacks = Last[acc]},
				If[ FailureQ[st],
					acc,
					unpackOneIntegerIneq[st, id, slacks]
				]
			]
		],
		{proof, {}},
		intIneqIds
	];
	If[ FailureQ[unpackedState],
		unpackedState,
		solveUnpackedIntegerLinearGoal[unpackedState, slackIds, goalInfo]
	]
]

unpackOneIntegerIneq[proof_TypeTheoryProof, hypId_Integer, slacks_List] := Module[
	{data, goal, current, env, sides, aTerm, bTerm, kId, eqId, newGoalId, eqBody, ctx1, ctx2, existsPred, existsType, motive, minor, elimTerm},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	sides = extractIntegerOrderGoal[env, current["Context"], current["Context"][hypId]["Type"]];
	If[ ! MatchQ[sides, {_, _, _}],
		{proof, slacks},

		{aTerm, bTerm} = Take[sides, 2];
		kId = freshFreeVariable[];
		eqId = freshFreeVariable[];
		newGoalId = freshMetavariableId[];
		ctx1 = extendContext[current["Context"], kId, makeHeldName["kInt", kId], coreNaturals[], "Explicit"];
		eqBody = coreEquality[coreIntegers[], bTerm, coreIntegerAddition[aTerm, coreIntegerOfNatural[freeVariable[kId]]], {1}];
		ctx2 = extendContext[ctx1, eqId, makeHeldName["hIntEq", eqId], eqBody, "Explicit"];
		existsPred = makeLambda[ctx1, {kId}, eqBody];
		existsType = makeApplication[coreConstant[HoldComplete[Exists], {1}], {coreNaturals[], existsPred}];
		motive = Construct[lambdaAbstraction, HoldComplete["w"], existsType, liftBoundVariables[current["Type"], 1, 0], "Explicit"];
		minor = pendingAbstraction[ctx2, {kId, eqId}, metavariable[newGoalId]];
		elimTerm = makeApplication[
			coreConstant[recursorName[HoldComplete[Exists]], {1}],
			{coreNaturals[], existsPred, motive, minor, freeVariable[hypId]}
		];
		{
			proofState @ solveGoal[
				data,
				goal,
				elimTerm,
				{newGoalId -> <|"Context" -> ctx2, "Type" -> current["Type"], "Case" -> None|>}
			],
			Append[slacks, {kId, eqId, aTerm, bTerm}]
		}
	]
]

solveUnpackedIntegerLinearGoal[proof_TypeTheoryProof, slacks_List, "Contradiction"] := Failure["IntegerContradictionUnsupported", <||>]
solveUnpackedIntegerLinearGoal[proof_TypeTheoryProof, slacks_List, {goalA_, goalB_, _}] := Module[
	{data, goal, current, env, allEqHyps, goalDiffPoly, hypDiffPolys, atoms, wlVars, atomRules, goalWl, hypWls, multVars, cConst, expr, coeffs, sol, multVals, constVal, witnessNatTerm, eqGoalId, eqBody, existsPred, stepState, closed},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];

	(* Collect integer equation hypotheses (both original and unpacked) *)
	allEqHyps = KeyValueMap[
		Function[{id, entry}, Replace[weakHeadNormalForm[env, current["Context"], entry["Type"]], {
			application[application[application[constantReference[HoldComplete[Equal], _], type_], l_], r_] /; integerTypeQ[env, type] :> {id, l, r},
			_ :> Nothing
		}]],
		current["Context"]
	];
	(* Express goalB - goalA and each slack (b_i - a_i == k_i) as linear polynomials in atoms *)
	goalDiffPoly = integerLinearPoly[goalB] - integerLinearPoly[goalA];
	hypDiffPolys = Function[entry, integerLinearPoly[Last[entry]] - integerLinearPoly[First[Rest[entry]]]] /@ allEqHyps;
	(* Also track slack variables k_i *)
	atoms = DeleteDuplicates[Cases[{goalDiffPoly, hypDiffPolys, Function[s, integerAtom[coreIntegerOfNatural[freeVariable[First[s]]]]] /@ slacks}, integerAtom[atom_] :> atom, {0, Infinity}]];
	wlVars = Table[Subscript[\[FormalV], j], {j, Length[atoms]}];
	atomRules = Thread[(integerAtom /@ atoms) -> wlVars];
	goalWl = Expand[ReplaceAll[goalDiffPoly, atomRules]];
	hypWls = Expand[ReplaceAll[#, atomRules]] & /@ hypDiffPolys;

	(* Find nonnegative integer coefficients m_j for slack variables k_j, unrestricted integer coefficients for eq hypotheses, and constant c >= 0 such that
	   goalB - goalA == c + Sum[m_j * k_j] + Sum[r_i * (eqLhs_i - eqRhs_i)] identically in all atoms! *)
	With[
		{
			slackWlVars = Function[s, ReplaceAll[integerAtom[coreIntegerOfNatural[freeVariable[First[s]]]], atomRules]] /@ slacks,
			mVars = Table[Subscript[\[FormalM], j], {j, Length[slacks]}],
			rVars = Table[Subscript[\[FormalR], i], {i, Length[allEqHyps]}]
		},
		cConst = \[FormalC];
		expr = Expand[goalWl - cConst - Total[MapThread[Times, {mVars, slackWlVars}]] - Total[MapThread[Times, {rVars, hypWls}]]];
		coeffs = If[ wlVars === {},
			{expr == 0},
			Thread[Values[CoefficientRules[expr, wlVars]] == 0]
		];
		sol = TimeConstrained[
			Quiet @ FindInstance[
				And @@ Join[coeffs, {cConst >= 0}, Thread[mVars >= 0]],
				Join[{cConst}, mVars, rVars],
				Integers
			],
			3,
			{}
		];
		If[ ! MatchQ[sol, {_List, ___}],
			Failure["NoIntegerLinearCertificate", <||>],

			With[{inst = First[sol]},
				constVal = ReplaceAll[cConst, inst];
				multVals = ReplaceAll[mVars, inst];
				If[ ! IntegerQ[constVal] || constVal < 0 || ! AllTrue[multVals, IntegerQ[#] && # >= 0 &],
					Failure["InvalidIntegerLinearCertificate", <||>],

					witnessNatTerm = buildNaturalLinearCombination[constVal, MapThread[{#1, freeVariable[First[#2]]} &, {multVals, slacks}]];
					eqGoalId = freshMetavariableId[];
					With[{kTmp = freshFreeVariable[]},
						{ctxTmp = extendContext[current["Context"], kTmp, HoldComplete["k"], coreNaturals[], "Explicit"]},
						{
							existsPred = makeLambda[ctxTmp, {kTmp}, coreEquality[coreIntegers[], goalB, coreIntegerAddition[goalA, coreIntegerOfNatural[freeVariable[kTmp]]], {1}]],
							eqBody = coreEquality[coreIntegers[], goalB, coreIntegerAddition[goalA, coreIntegerOfNatural[witnessNatTerm]], {1}]
						},
						stepState = proofState @ solveGoal[
							data,
							goal,
							makeApplication[coreConstant[HoldComplete["existsIntroduction"], {1}], {coreNaturals[], existsPred, witnessNatTerm, metavariable[eqGoalId]}],
							{eqGoalId -> <|"Context" -> current["Context"], "Type" -> eqBody, "Case" -> None|>}
						];
						(* Prove goalB == goalA + integerOfNatural[witnessNatTerm] by rewriting integerOfNatural over +/* then PolynomialReduce / Ring *)
						closed = Quiet @ catchKernelFailure[closeIntegerWitnessEquation[stepState]];
						If[ ! FailureQ[closed] && closed["Goals"] === {},
							closed,
							Failure["IntegerWitnessEquationFailed", <||>]
						]
					]
				]
			]
		]
	]
]

closeIntegerWitnessEquation[state_TypeTheoryProof] := Module[{rewritten, attempt},
	attempt = Quiet @ catchKernelFailure[TypeTheoryTactic["Ring"][state]];
	If[! FailureQ[attempt] && attempt["Goals"] === {}, attempt,
		attempt = Quiet @ catchKernelFailure[TypeTheoryTactic["PolynomialReduce"][state]];
		If[! FailureQ[attempt] && attempt["Goals"] === {}, attempt,
			rewritten = Quiet @ catchKernelFailure[
				TypeTheoryTactic["RewriteRepeated", "integerOfNaturalAddition", "integerOfNaturalMultiplication"][state]
			];
			If[ FailureQ[rewritten],
				rewritten = state
			];
			If[ rewritten["Goals"] === {},
				rewritten,
				attempt = Quiet @ catchKernelFailure[TypeTheoryTactic["PolynomialReduce"][rewritten]];
				If[! FailureQ[attempt] && attempt["Goals"] === {}, attempt,
					Quiet @ catchKernelFailure[TypeTheoryTactic["Ring"][rewritten]]
				]
			]
		]
	]
]

buildNaturalLinearCombination[constVal_Integer, terms_List] := Module[{parts},
	parts = DeleteCases[
		Prepend[
			Function[pair, Replace[pair, {
				{0, _} :> Nothing,
				{1, var_} :> var,
				{c_Integer, var_} :> coreNaturalTimes[naturalLiteral[c], var]
			}]] /@ terms,
			If[constVal === 0, Nothing, naturalLiteral[constVal]]
		],
		Nothing
	];
	If[parts === {}, naturalLiteral[0], Fold[coreNaturalPlus, parts]]
]

integerLinearPoly[term_] := Replace[term, {
	application[application[constantReference[HoldComplete["integerAddition"], _], a_], b_] :> integerLinearPoly[a] + integerLinearPoly[b],
	application[application[constantReference[HoldComplete["integerSubtraction"], _], a_], b_] :> integerLinearPoly[a] - integerLinearPoly[b],
	application[application[constantReference[HoldComplete["integerMultiplication"], _], a_], b_] :> integerLinearPoly[a] * integerLinearPoly[b],
	application[constantReference[HoldComplete["integerNegation"], _], a_] :> -integerLinearPoly[a],
	application[constantReference[HoldComplete["integerOfNatural"], _], naturalLiteral[n_Integer]] :> n,
	application[constantReference[HoldComplete["integerOfNatural"], _], constantReference[HoldComplete["zero"], _]] :> 0,
	application[constantReference[HoldComplete["integerOfNatural"], _], application[constantReference[HoldComplete["successor"], _], a_]] :>
		integerLinearPoly[coreIntegerOfNatural[a]] + 1,
	other_ :> integerAtom[other]
}]


(* Specialized tactic E: Prove classical propositional goals in Constructive when excludedMiddle is a local hypothesis *)
proveFromExcludedMiddleInState[proof_TypeTheoryProof] := Module[
	{data, goal, current, env, emHypId, atoms, splitState},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	emHypId = SelectFirst[
		Keys[current["Context"]],
		Function[id, excludedMiddleTypeQ[env, current["Context"], current["Context"][id]["Type"]]],
		None
	];
	If[ emHypId === None,
		Failure["NoExcludedMiddleHypothesis", <||>],

		(* Collect propositional free variables occurring in goal or hypotheses *)
		atoms = Select[
			Keys[current["Context"]],
			Function[id, id =!= emHypId && weakHeadNormalForm[env, current["Context"], current["Context"][id]["Type"]] === universeSort[0]]
		];
		If[ atoms === {},
			Failure["NoPropAtoms", <||>],

			splitState = Fold[
				Function[{st, atomId},
					If[ FailureQ[st] || st["Goals"] === {},
						st,
						splitAllOpenGoalsOnAtom[st, emHypId, freeVariable[atomId]]
					]
				],
				proof,
				Take[atoms, Min[Length[atoms], 3]]
			];
			closeAllGoalsWith[splitState, Function[cur, Quiet @ catchKernelFailure[TypeTheoryTactic["Intuitionistic"][cur]]]]
		]
	]
]

(* Split each currently open goal at most once on atomTerm (closing with Intuitionistic first when possible) *)
splitAllOpenGoalsOnAtom[proof_TypeTheoryProof, emHypId_Integer, atomTerm_] := Module[{cur = proof, nGoals, step},
	nGoals = Length[proof["Goals"]];
	Do[
		If[ FailureQ[cur] || cur["Goals"] === {},
			Break[]
		];
		With[{intu = Quiet @ catchKernelFailure[TypeTheoryTactic["Intuitionistic"][cur]]},
			If[ ! FailureQ[intu],
				cur = intu,
				With[{d = First[cur]},
					{g = First[d["Goals"]]},
					{ctx = currentGoal[d, g]["Context"]},
					{existing = Lookup[Values[ctx], "Type"]},
					If[ MemberQ[existing, atomTerm] || MemberQ[existing, coreNegation[d["Environment"], atomTerm]],
						(* Already split on this atom in this goal; stop looping *)
						Break[],
						cur = splitByExcludedMiddleHypothesis[cur, emHypId, atomTerm]
					]
				]
			]
		],
		{step, nGoals}
	];
	cur
]

excludedMiddleTypeQ[env_, context_, type_] := MatchQ[
	weakHeadNormalForm[env, context, type],
	dependentFunctionType[_, universeSort[0],
		application[application[constantReference[HoldComplete[Or], _], boundVariable[0]],
			application[constantReference[HoldComplete[Not], _], boundVariable[0]] |
			dependentFunctionType[_, boundVariable[0], constantReference[HoldComplete[False], _], _]
		], _]
]

splitByExcludedMiddleHypothesis[proof_TypeTheoryProof, emHypId_Integer, atomTerm_] := Module[
	{data, goal, current, env, emApplied, orType, leftType, rightType, idL, idR, goalL, goalR, ctxL, ctxR, motive, elimTerm},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	env = data["Environment"];
	emApplied = Construct[application, freeVariable[emHypId], atomTerm];
	orType = weakHeadNormalForm[env, current["Context"], inferType[env, current["Context"], emApplied]];
	If[ ! MatchQ[orType, application[application[constantReference[HoldComplete[Or], _], _], _]],
		Failure["NotOr", <||>],

		leftType = Last[First[orType]];
		rightType = Last[orType];
		idL = freshFreeVariable[];
		idR = freshFreeVariable[];
		goalL = freshMetavariableId[];
		goalR = freshMetavariableId[];
		ctxL = extendContext[current["Context"], idL, makeHeldName["hPos", idL], leftType, "Explicit"];
		ctxR = extendContext[current["Context"], idR, makeHeldName["hNeg", idR], rightType, "Explicit"];
		motive = Construct[lambdaAbstraction, HoldComplete["disj"], orType, liftBoundVariables[current["Type"], 1, 0], "Explicit"];
		elimTerm = makeApplication[
			coreConstant[recursorName[HoldComplete[Or]], {}],
			{leftType, rightType, motive, pendingAbstraction[ctxL, {idL}, metavariable[goalL]], pendingAbstraction[ctxR, {idR}, metavariable[goalR]], emApplied}
		];
		proofState @ solveGoal[
			data,
			goal,
			elimTerm,
			{
				goalL -> <|"Context" -> ctxL, "Type" -> current["Type"], "Case" -> None|>,
				goalR -> <|"Context" -> ctxR, "Type" -> current["Type"], "Case" -> None|>
			}
		]
	]
]


(* Strategy 4: Existential witness proof over algebraic/equational premises (e.g. f[f[x]] == x => Exists[x, f[x] == y]) *)
tryAlgebraicWitnessProof[state_TypeTheoryProof] := Module[
	{introduced, data, goal, current, env, target, type, pred, candidateTerms, tryTerm},
	introduced = introduceAll[state];
	data = First[introduced];
	If[ data["Goals"] === {},
		introduced,

		goal = First[data["Goals"]];
		current = currentGoal[data, goal];
		env = data["Environment"];
		target = weakHeadNormalForm[env, current["Context"], current["Type"]];
		If[ ! MatchQ[target, application[application[constantReference[HoldComplete[Exists], _], _], _]] || ! constantDeclaredQ[env, HoldComplete["existsIntroduction"]],
			Failure["NotExistential", <||>],

			type = Last[First[target]];
			pred = Last[target];
			(* Candidate witnesses: context variables of type, and unary applications f[v] where f : type -> type *)
			candidateTerms = buildAlgebraicWitnessCandidates[env, current["Context"], type];
			tryTerm = SelectFirst[
				candidateTerms,
				Function[witness,
					With[{newGoal = freshMetavariableId[], instBody = betaNormalize[Construct[application, pred, witness]]},
						{
							step = proofState @ solveGoal[
								data,
								goal,
								makeApplication[coreConstant[HoldComplete["existsIntroduction"], Last[First[First[target]]]], {type, pred, witness, metavariable[newGoal]}],
								{newGoal -> <|"Context" -> current["Context"], "Type" -> instBody, "Case" -> None|>}
							]
						},
						With[{closed = Quiet @ catchKernelFailure[closeGoalBasic[step]]},
							! FailureQ[closed] && closed["Goals"] === {}
						]
					]
				],
				None
			];
			If[ tryTerm === None,
				Failure["NoAlgebraicWitness", <||>],

				With[{newGoal = freshMetavariableId[], instBody = betaNormalize[Construct[application, pred, tryTerm]]},
					closeGoalBasic[
						proofState @ solveGoal[
							data,
							goal,
							makeApplication[coreConstant[HoldComplete["existsIntroduction"], Last[First[First[target]]]], {type, pred, tryTerm, metavariable[newGoal]}],
							{newGoal -> <|"Context" -> current["Context"], "Type" -> instBody, "Case" -> None|>}
						]
					]
				]
			]
		]
	]
]

buildAlgebraicWitnessCandidates[env_, context_, targetType_] := Module[{varsOfType, unaryFns, apps},
	varsOfType = Select[Keys[context], Function[id, withKernelCaches[definitionallyEqualQ[env, context, context[id]["Type"], targetType]]]];
	unaryFns = Select[
		environmentNames[env],
		Function[name,
			With[{rec = constantRecord[env, name]},
				MatchQ[rec["Kind"], "Axiom" | "Definition"] &&
				MatchQ[rec["Type"], dependentFunctionType[_, dom_, cod_, _] /; looseBoundRange[cod] == 0 &&
					withKernelCaches[definitionallyEqualQ[env, context, dom, targetType]] &&
					withKernelCaches[definitionallyEqualQ[env, context, cod, targetType]]]
			]
		]
	];
	apps = Flatten @ Outer[
		Function[{fn, id}, Construct[application, coreConstant[fn], freeVariable[id]]],
		Take[unaryFns, Min[Length[unaryFns], 6]],
		varsOfType
	];
	Join[freeVariable /@ varsOfType, apps]
]


(* Strategy 5: 1-step induction and bounded case-unrolling + shifted induction on NonNegativeIntegers *)
tryNaturalInductionProof[state_TypeTheoryProof] := Module[
	{introduced, data, goal, current, env, natVars, attempt, shiftCount},
	introduced = introduceAll[state];
	data = First[introduced];
	If[ data["Goals"] === {},
		introduced,

		goal = First[data["Goals"]];
		current = currentGoal[data, goal];
		env = data["Environment"];
		natVars = Select[Keys[current["Context"]], Function[id, naturalNumberTypeQ[env, current["Context"], current["Context"][id]["Type"]]]];
		If[ natVars === {},
			Failure["NoNaturalVariables", <||>],

			(* 5a. Standard 1-step induction on each natural variable *)
			attempt = SelectFirst[
				Take[natVars, Min[Length[natVars], 3]],
				Function[id,
					With[{res = runInductionOnVar[introduced, id]},
						! FailureQ[res] && res["Goals"] === {}
					]
				],
				None
			];
			If[ attempt =!= None,
				runInductionOnVar[introduced, attempt],

				(* 5b. Bounded case-unrolling + induction (handles 4 <= n => n^2 <= 2^n and n != 3 => n^2 <= 2^n) *)
				shiftCount = detectNaturalCaseShift[env, current["Context"], First[natVars]];
				If[ shiftCount > 0 && shiftCount <= 8,
					runUnrolledNaturalInduction[introduced, First[natVars], shiftCount],
					Failure["InductionFailed", <||>]
				]
			]
		]
	]
]

runInductionOnVar[proof_TypeTheoryProof, varId_Integer] := Module[{data, goal, current, varName, indState},
	data = First[proof];
	goal = First[data["Goals"]];
	current = currentGoal[data, goal];
	varName = current["Context"][varId]["Name"];
	indState = Quiet @ catchKernelFailure[Replace[varName, HoldComplete[sym_] :> TypeTheoryTactic["Induction", sym][proof]]];
	If[ FailureQ[indState],
		indState,

		closeAllGoalsWith[indState, Function[cur,
			With[{sub = introduceAll[cur]},
				closeGoalBasic[sub]
			]
		]]
	]
]

(* Detect if context has a bound like k <= n or n != k suggesting k or k+1 case splits before induction *)
detectNaturalCaseShift[env_, context_, varId_Integer] := Module[{shifts},
	shifts = KeyValueMap[
		Function[{id, entry}, Replace[weakHeadNormalForm[env, context, entry["Type"]], {
			application[application[constantReference[HoldComplete[LessEqual], _], naturalLiteral[k_Integer]], freeVariable[v_]] /; v === varId && k >= 1 && k <= 8 :> k,
			dependentFunctionType[_, application[application[application[constantReference[HoldComplete[Equal], _], _], freeVariable[v_]], naturalLiteral[k_Integer]], constantReference[HoldComplete[False], _], _] /; v === varId && k >= 0 && k <= 7 :> k + 1,
			dependentFunctionType[_, application[application[application[constantReference[HoldComplete[Equal], _], _], naturalLiteral[k_Integer]], freeVariable[v_]], constantReference[HoldComplete[False], _], _] /; v === varId && k >= 0 && k <= 7 :> k + 1,
			_ :> 0
		}]],
		context
	];
	Max[Prepend[shifts, 0]]
]

(* Unroll 'shift' Cases steps on varId, closing finite branches 0..shift-1, then run Induction on the remainder *)
runUnrolledNaturalInduction[proof_TypeTheoryProof, varId_Integer, shift_Integer] := Module[{currentState, currentVarId},
	currentState = proof;
	currentVarId = varId;
	Do[
		If[ FailureQ[currentState] || currentState["Goals"] === {},
			Break[]
		];
		With[{d = First[currentState]},
			{g = First[d["Goals"]]},
			{ctx = currentGoal[d, g]["Context"]},
			If[ ! KeyExistsQ[ctx, currentVarId],
				currentState = Failure["VarLost", <||>];
				Break[]
			];
			With[{nm = ctx[currentVarId]["Name"]},
				currentState = Quiet @ catchKernelFailure[Replace[nm, HoldComplete[sym_] :> TypeTheoryTactic["Cases", sym][currentState]]];
				If[ FailureQ[currentState],
					Break[]
				];
				(* First subgoal is the 0 case — close it immediately *)
				currentState = Quiet @ catchKernelFailure[closeGoalBasic[introduceAll[currentState]]];
				If[ FailureQ[currentState] || currentState["Goals"] === {},
					Break[]
				];
				(* Second subgoal starts with ForAll[{Typed[k, NonNegativeIntegers]}, ...] — introduce k and track its id *)
				currentState = Quiet @ catchKernelFailure[TypeTheoryTactic["Introduce"][currentState]];
				If[ FailureQ[currentState],
					Break[]
				];
				With[{d2 = First[currentState]},
					{ctx2 = currentGoal[d2, First[d2["Goals"]]]["Context"]},
					currentVarId = Last[Keys[ctx2]];
					currentState = introduceAll[currentState]
				]
			]
		],
		{step, shift}
	];
	If[ FailureQ[currentState],
		currentState,
		If[ currentState["Goals"] === {},
			currentState,
			(* Now run induction on the shifted variable! *)
			runInductionOnVar[currentState, currentVarId]
		]
	]
]


(* ::Section:: *)
(*Superfunction 1: TypeTheoryDetermine*)


TypeTheoryDetermine[proposition_, opts : OptionsPattern[]] /; statementQ[Unevaluated[proposition]] :=
	catchKernelFailure @ determineProposition[HoldComplete[proposition], Automatic, Hold[opts]]

TypeTheoryDetermine[proposition_, environment : Except[_Rule | _RuleDelayed], opts : OptionsPattern[]] /; statementQ[Unevaluated[proposition]] :=
	catchKernelFailure @ determineProposition[HoldComplete[proposition], environment, Hold[opts]]

SetAttributes[determineProposition, HoldFirst]
determineProposition[HoldComplete[proposition_], environmentSpec_, Hold[opts___]] := Module[
	{resolved, environment, coreStmt, uParams, surfaceTerm, methodOpt, timeBudget, maxModelSize, llmEval, progressOpt,
	 compDecidable, negStmt},
	resolved = resolveProposition[proposition, environmentSpec];
	If[ FailureQ[resolved],
		resolved,

		environment = resolved["Environment"];
		coreStmt = resolved["CoreStatement"];
		uParams = resolved["UniverseParameters"];
		surfaceTerm = resolved["SurfaceTerm"];
		methodOpt = OptionValue[TypeTheoryDetermine, {opts}, Method];
		timeBudget = Replace[OptionValue[TypeTheoryDetermine, {opts}, TimeConstraint], Except[_?Positive] -> 15];
		maxModelSize = Replace[OptionValue[TypeTheoryDetermine, {opts}, "MaxModelSize"], Except[_Integer?Positive] -> 3];
		llmEval = OptionValue[TypeTheoryDetermine, {opts}, "LLMEvaluator"];
		progressOpt = OptionValue[TypeTheoryDetermine, {opts}, ProgressReporting];
		withSuperfunctionProgress["TypeTheoryDetermine", progressOpt, timeBudget,
			reportProgress["Checking decidability...", 0.08];
			compDecidable = decidableInstanceQ[environment, coreStmt, uParams];
			negStmt = coreNegation[environment, coreStmt];
			determinePipeline[environment, coreStmt, negStmt, uParams, surfaceTerm, compDecidable, methodOpt, timeBudget, maxModelSize, llmEval]
		]
	]
]

(* Clean Return-free determination pipeline *)
determinePipeline[environment_, coreStmt_, negStmt_, uParams_List, surfaceTerm_, compDecidable_, methodOpt_, timeBudget_, maxModelSize_Integer, llmEval_] := Module[
	{result},
	(* 1. Closed decision fast-path *)
	result = If[ compDecidable && ! MatchQ[weakHeadNormalForm[environment, <||>, coreStmt], _dependentFunctionType],
		reportProgress["Deciding closed proposition...", 0.15];
		tryDecideBoth[environment, coreStmt, negStmt, uParams, surfaceTerm, compDecidable],
		None
	];
	If[ AssociationQ[result],
		result,

		(* 2. Quick counterexample probe on universal statements *)
		result = If[ useHeuristicQ[methodOpt] && ! deadlineExceededQ[] && MatchQ[weakHeadNormalForm[environment, <||>, coreStmt], _dependentFunctionType],
			reportProgress["Probing for counterexamples...", 0.25];
			tryQuickCounterexample[environment, coreStmt, negStmt, uParams, surfaceTerm, compDecidable, remainingBudget[Min[2, timeBudget / 4]]],
			None
		];
		If[ AssociationQ[result],
			result,

			(* 3. Positive proof portfolio *)
			result = If[ useHeuristicQ[methodOpt] && ! deadlineExceededQ[],
				reportProgress["Running proof portfolio...", 0.45];
				With[{pos = enhancedProveCore[environment, coreStmt, uParams, remainingBudget[Min[6, timeBudget / 2]]]},
					If[ ! FailureQ[pos],
						determineResult["Proved", surfaceTerm, pos, None, extractWitnessFromProof[environment, coreStmt, pos], None, compDecidable, "Portfolio", <||>],
						None
					]
				],
				None
			];
			If[ AssociationQ[result],
				result,

				(* 4. Negative proof portfolio *)
				result = If[ useHeuristicQ[methodOpt] && ! deadlineExceededQ[],
					reportProgress["Running refutation portfolio...", 0.62];
					With[{neg = enhancedProveCore[environment, negStmt, uParams, remainingBudget[Min[5, timeBudget / 3]]]},
						If[ ! FailureQ[neg],
							determineResult["Refuted", surfaceTerm, neg, extractCounterexampleFromProof[environment, coreStmt, neg], None, None, compDecidable, "NegationPortfolio", <||>],
							None
						]
					],
					None
				];
				If[ AssociationQ[result],
					result,

					(* 5. Certified finite/concrete model independence for opaque signatures *)
					result = If[ useHeuristicQ[methodOpt] && ! deadlineExceededQ[],
						reportProgress["Searching concrete and finite independence models...", 0.78];
						tryModelIndependence[environment, coreStmt, negStmt, uParams, surfaceTerm, compDecidable, maxModelSize],
						None
					];
					If[ AssociationQ[result],
						result,

						(* 6. Optional LLM tactic hint if Method includes "LLM" *)
						result = If[ useLLMQ[methodOpt],
							reportProgress["Querying LLMFunction for proof tactics...", 0.88];
							tryLLMDetermination[environment, coreStmt, negStmt, uParams, surfaceTerm, compDecidable, llmEval, remainingBudget[timeBudget]],
							None
						];
						If[ AssociationQ[result],
							result,

							(* 7. Axiom-sensitivity check (e.g. Constructive vs Prelude) + honest Undetermined *)
							reportProgress["Checking classical axiom sensitivity...", 0.95];
							buildUndeterminedResult[environment, coreStmt, uParams, surfaceTerm, compDecidable]
						]
					]
				]
			]
		]
	]
]

determineResult[status_String, surfaceTerm_, proof_, counterexample_, witness_, models_, compDecidable_, method_String, details_Association] := Module[{axInfo},
	axInfo = If[MatchQ[proof, _TypeTheoryProof], proofAxiomSummary[proof], <|"Axioms" -> None, "Constructive" -> None|>];
	<|
		"Status" -> status,
		"Statement" -> surfaceTerm,
		"Proof" -> proof,
		"Counterexample" -> counterexample,
		"Witness" -> witness,
		"Models" -> models,
		"Axioms" -> axInfo["Axioms"],
		"Constructive" -> axInfo["Constructive"],
		"ComputationallyDecidable" -> compDecidable,
		"Method" -> method,
		"Details" -> details
	|>
]

tryDecideBoth[environment_, coreStmt_, negStmt_, uParams_List, surfaceTerm_, compDecidable_] := Module[{pPos, pNeg},
	pPos = proveFromCore[environment, coreStmt, uParams, {TypeTheoryTactic["Decide"]}];
	If[ ! FailureQ[pPos],
		determineResult["Proved", surfaceTerm, pPos, None, None, None, compDecidable, "Decide", <||>],

		pNeg = proveFromCore[environment, negStmt, uParams, {TypeTheoryTactic["Decide"]}];
		If[ ! FailureQ[pNeg],
			determineResult["Refuted", surfaceTerm, pNeg, None, None, None, compDecidable, "Decide", <||>],
			None
		]
	]
]

tryQuickCounterexample[environment_, coreStmt_, negStmt_, uParams_List, surfaceTerm_, compDecidable_, timeLimit_] := TimeConstrained[
	Module[{pNeg},
		pNeg = proveFromCore[environment, negStmt, uParams, {TypeTheoryTactic["Counterexample"]}];
		If[ ! FailureQ[pNeg],
			determineResult["Refuted", surfaceTerm, pNeg, extractCounterexampleFromProof[environment, coreStmt, pNeg], None, None, compDecidable, "Counterexample", <||>],

			(* Also probe Boolean universal counterexample *)
			pNeg = tryBooleanCounterexample[environment, coreStmt, negStmt, uParams];
			If[ ! FailureQ[pNeg],
				determineResult["Refuted", surfaceTerm, pNeg, extractCounterexampleFromProof[environment, coreStmt, pNeg], None, None, compDecidable, "BooleanCounterexample", <||>],
				None
			]
		]
	],
	timeLimit,
	None
]

(* Refute ForAll[{Typed[b1, Booleans], ...}, body] by enumerating {false, true}^k *)
tryBooleanCounterexample[environment_, universalCore_, negStmt_, uParams_List] := Module[{binders, tuples, found},
	binders = collectBooleanUniversalBinders[environment, <||>, universalCore];
	If[ binders === {} || Length[binders] > 4,
		Failure["NotBooleanUniversal", <||>],

		tuples = Tuples[{coreConstant[HoldComplete["false"]], coreConstant[HoldComplete["true"]]}, Length[binders]];
		found = SelectFirst[
			tuples,
			Function[vals,
				With[{inst = instantiateUniversalCore[environment, universalCore, vals]},
					! FailureQ[proveFromCore[environment, coreNegation[environment, inst], uParams, {TypeTheoryTactic["Decide"]}]]
				]
			],
			None
		];
		If[ found === None,
			Failure["NoBooleanCounterexample", <||>],

			With[{inst = instantiateUniversalCore[environment, universalCore, found]},
				{negInstProof = proveFromCore[environment, coreNegation[environment, inst], uParams, {TypeTheoryTactic["Decide"]}]},
				If[ FailureQ[negInstProof],
					negInstProof,
					With[{hId = freshFreeVariable[], negTerm = completedProofTerm[negInstProof]},
						{
							ctx = extendContext[<||>, hId, HoldComplete["h"], universalCore, "Explicit"],
							body = Construct[application, negTerm, makeApplication[freeVariable[hId], found]]
						},
						{proofTerm = makeLambda[ctx, {hId}, body]},
						{
							st = newProofState[environment, negStmt, uParams]
						},
						verifyProofInKernel[
							environment,
							negStmt,
							uParams,
							proofState @ solveGoal[First[st], First[First[st]["Goals"]], proofTerm, {}]
						]
					]
				]
			]
		]
	]
]

collectBooleanUniversalBinders[environment_, context_, term_] := Replace[weakHeadNormalForm[environment, context, term], {
	dependentFunctionType[name_, domain_, codomain_, binder_] /; weakHeadNormalForm[environment, context, domain] === coreBooleans[] :> With[{id = freshFreeVariable[]},
		Prepend[
			collectBooleanUniversalBinders[environment, extendContext[context, id, name, domain, binder], betaNormalize[instantiateBoundVariable[codomain, freeVariable[id]]]],
			name
		]
	],
	_ :> {}
}]

instantiateUniversalCore[environment_, term_, {}] := term
instantiateUniversalCore[environment_, term_, {val_, rest___}] := Replace[weakHeadNormalForm[environment, <||>, term], {
	dependentFunctionType[_, _, codomain_, _] :> instantiateUniversalCore[environment, betaNormalize[instantiateBoundVariable[codomain, val]], {rest}],
	_ :> term
}]


(* Certified Model Independence:
   Detects opaque signature axioms in coreStmt (e.g. opaque f : N -> N, c : N, or opaque type T with operations).
   Substitutes candidate concrete interpretations, verifies all constraining axioms of environment hold in each
   interpretation, and kernel-proves P in M_true and Not[P] in M_false! *)
tryModelIndependence[environment_, coreStmt_, negStmt_, uParams_List, surfaceTerm_, compDecidable_, maxModelSize_Integer] := Module[
	{mentioned, opaqueAxioms, opaqueTypes, opaqueValues, propAxioms, candidates, trueModel, falseModel},
	mentioned = DeleteDuplicates[Cases[coreStmt, constantReference[name_, _] :> name, {0, Infinity}]];
	opaqueAxioms = Select[mentioned, Function[name,
		With[{rec = constantRecord[environment, name]},
			rec["Kind"] === "Axiom" && ! MemberQ[$standardAxiomNames, name] && ! TrueQ[Quiet @ propositionQ[environment, <||>, rec["Type"]]]
		]
	]];
	If[ opaqueAxioms === {},
		None,

		(* Any propositional axioms in environment that mention these opaque symbols must also hold in any valid model! *)
		propAxioms = Select[environmentNames[environment], Function[name,
			With[{rec = constantRecord[environment, name]},
				rec["Kind"] === "Axiom" &&
				! MemberQ[$standardAxiomNames, name] &&
				TrueQ[Quiet @ propositionQ[environment, <||>, rec["Type"]]] &&
				! FreeQ[rec["Type"], constantReference[Alternatives @@ opaqueAxioms, _]]
			]
		]];
		opaqueTypes = Select[opaqueAxioms, Function[name, MatchQ[weakHeadNormalForm[environment, <||>, constantRecord[environment, name]["Type"]], _universeSort]]];
		opaqueValues = Complement[opaqueAxioms, opaqueTypes];

		candidates = Which[
			opaqueTypes === {} && Length[opaqueValues] <= 3,
				generateConcreteValueModels[environment, opaqueValues],
			Length[opaqueTypes] === 1 && Length[opaqueValues] <= 2,
				generateFiniteCarrierModels[environment, First[opaqueTypes], opaqueValues, maxModelSize],
			True,
				{}
		];
		If[ candidates === {},
			None,

			trueModel = None;
			falseModel = None;
			Scan[
				Function[model,
					If[ trueModel === None || falseModel === None,
						If[ modelSatisfiesAxiomsQ[environment, model["Substitution"], propAxioms, uParams],
							With[{instP = betaNormalize[substituteConstantsCore[coreStmt, model["Substitution"]]]},
								If[ trueModel === None,
									With[{pTrue = enhancedProveCore[environment, instP, uParams, 1.5]},
										If[ ! FailureQ[pTrue],
											trueModel = Append[model, "Proof" -> pTrue]
										]
									]
								];
								If[ falseModel === None,
									With[{pFalse = enhancedProveCore[environment, coreNegation[environment, instP], uParams, 1.5]},
										If[ ! FailureQ[pFalse],
											falseModel = Append[model, "Proof" -> pFalse]
										]
									]
								]
							]
						]
					]
				],
				candidates
			];
			If[ trueModel =!= None && falseModel =!= None,
				determineResult[
					"Independent",
					surfaceTerm,
					None,
					None,
					None,
					<|
						"TrueModel" -> KeyDrop[trueModel, "Substitution"],
						"FalseModel" -> KeyDrop[falseModel, "Substitution"]
					|>,
					compDecidable,
					"CertifiedModelIndependence",
					<|"IndependenceKind" -> "CertifiedModelIndependence", "OpaqueConstants" -> (nameToKey /@ opaqueAxioms)|>
				],
				None
			]
		]
	]
]

$standardAxiomNames = HoldComplete /@ {"choice", "propositionalExtensionality", "quotientSoundness", ExpressionEvaluate}

substituteConstantsCore[term_, rules_Association] := ReplaceAll[
	term,
	constantReference[name_, _] /; KeyExistsQ[rules, name] :> With[{val = rules[name]}, val /; True]
]

modelSatisfiesAxiomsQ[environment_, sub_Association, propAxioms_List, uParams_List] := AllTrue[
	propAxioms,
	Function[axName,
		With[{axType = betaNormalize[substituteConstantsCore[constantRecord[environment, axName]["Type"], sub]]},
			! FailureQ[enhancedProveCore[environment, axType, uParams, 1.0]]
		]
	]
]

(* Concrete interpretations for opaque constants/functions over Naturals, Integers, Booleans, Prop *)
generateConcreteValueModels[environment_, opaqueValues_List] := Module[{perSymbolOptions, combos},
	perSymbolOptions = Function[name, concreteInterpretationsForType[environment, name, constantRecord[environment, name]["Type"]]] /@ opaqueValues;
	If[ MemberQ[perSymbolOptions, {}],
		{},

		combos = Take[Tuples[perSymbolOptions], UpTo[24]];
		Function[combo,
			<|
				"Interpretation" -> Association[First /@ combo],
				"Substitution" -> Association[Last /@ combo]
			|>
		] /@ combos
	]
]

concreteInterpretationsForType[environment_, name_HoldComplete, type_] := Module[{key = nameToKey[name], whnf = weakHeadNormalForm[environment, <||>, type]},
	Which[
		(* Constant of NonNegativeIntegers *)
		whnf === coreNaturals[],
			{
				{key -> 0, name -> naturalLiteral[0]},
				{key -> 1, name -> naturalLiteral[1]},
				{key -> 2, name -> naturalLiteral[2]},
				{key -> 3, name -> naturalLiteral[3]},
				{key -> 4, name -> naturalLiteral[4]},
				{key -> 5, name -> naturalLiteral[5]}
			},

		(* Constant of Booleans *)
		whnf === coreBooleans[],
			{
				{key -> True, name -> coreConstant[HoldComplete["true"]]},
				{key -> False, name -> coreConstant[HoldComplete["false"]]}
			},

		(* Constant of Prop *)
		whnf === universeSort[0],
			{
				{key -> True, name -> coreTrue[]},
				{key -> False, name -> coreFalse[]}
			},

		(* Unary function N -> N *)
		MatchQ[whnf, dependentFunctionType[_, dom_, cod_, _] /; dom === coreNaturals[] && cod === coreNaturals[]],
			{
				{key -> "Identity", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], boundVariable[0], "Explicit"]},
				{key -> "Zero", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], naturalLiteral[0], "Explicit"]},
				{key -> "Successor", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], Construct[application, coreConstant[HoldComplete["successor"]], boundVariable[0]], "Explicit"]}
			},

		(* Binary function N -> N -> N *)
		MatchQ[whnf, dependentFunctionType[_, d1_, dependentFunctionType[_, d2_, c_, _], _] /; d1 === coreNaturals[] && d2 === coreNaturals[] && c === coreNaturals[]],
			{
				{key -> "Plus", name -> coreConstant[HoldComplete[Plus]]},
				{key -> "Times", name -> coreConstant[HoldComplete[Times]]},
				{key -> "FirstProjection", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], Construct[lambdaAbstraction, HoldComplete["y"], coreNaturals[], boundVariable[1], "Explicit"], "Explicit"]},
				{key -> "SecondProjection", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], Construct[lambdaAbstraction, HoldComplete["y"], coreNaturals[], boundVariable[0], "Explicit"], "Explicit"]}
			},

		(* Unary predicate N -> Prop *)
		MatchQ[whnf, dependentFunctionType[_, dom_, universeSort[0], _] /; dom === coreNaturals[]],
			{
				{key -> "AlwaysTrue", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], coreTrue[], "Explicit"]},
				{key -> "AlwaysFalse", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], coreFalse[], "Explicit"]},
				{key -> "EqualsZero", name -> Construct[lambdaAbstraction, HoldComplete["x"], coreNaturals[], coreEquality[coreNaturals[], boundVariable[0], naturalLiteral[0], {1}], "Explicit"]}
			},

		(* Constant of Integers *)
		integerTypeQ[environment, whnf],
			{
				{key -> 0, name -> coreIntegerLiteral[0]},
				{key -> 1, name -> coreIntegerLiteral[1]},
				{key -> -1, name -> coreIntegerLiteral[-1]}
			},

		True,
			{}
	]
]

(* Finite carrier models: interpret opaque carrier type T as Booleans (size 2) or Unit (True? no, True is Prop; use Booleans!) *)
generateFiniteCarrierModels[environment_, carrierName_HoldComplete, opaqueValues_List, maxModelSize_Integer] := Module[
	{carrierKey = nameToKey[carrierName], boolCarrier = coreBooleans[], perSymbol, combos},
	If[ ! constantDeclaredQ[environment, HoldComplete[Booleans]],
		{},

		perSymbol = Function[name,
			finiteCarrierInterpretations[environment, carrierName, boolCarrier, name, constantRecord[environment, name]["Type"]]
		] /@ opaqueValues;
		If[ MemberQ[perSymbol, {}],
			{},

			combos = Take[Tuples[perSymbol], UpTo[24]];
			Function[combo,
				<|
					"Interpretation" -> Prepend[Association[First /@ combo], carrierKey -> "Booleans (size 2)"],
					"Substitution" -> Prepend[Association[Last /@ combo], carrierName -> boolCarrier]
				|>
			] /@ combos
		]
	]
]

finiteCarrierInterpretations[environment_, carrierName_HoldComplete, carrierTerm_, name_HoldComplete, type_] := Module[
	{key = nameToKey[name], subType = substituteConstantsCore[type, <|carrierName -> carrierTerm|>]},
	Which[
		(* Constant e : T *)
		subType === carrierTerm,
			{
				{key -> False, name -> coreConstant[HoldComplete["false"]]},
				{key -> True, name -> coreConstant[HoldComplete["true"]]}
			},

		(* Unary op f : T -> T *)
		MatchQ[subType, dependentFunctionType[_, d_, c_, _] /; d === carrierTerm && c === carrierTerm],
			{
				{key -> "Identity", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, boundVariable[0], "Explicit"]},
				{key -> "Not", name -> coreConstant[HoldComplete["not"]]},
				{key -> "ConstFalse", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, coreConstant[HoldComplete["false"]], "Explicit"]},
				{key -> "ConstTrue", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, coreConstant[HoldComplete["true"]], "Explicit"]}
			},

		(* Binary op f : T -> T -> T *)
		MatchQ[subType, dependentFunctionType[_, d1_, dependentFunctionType[_, d2_, c_, _], _] /; d1 === carrierTerm && d2 === carrierTerm && c === carrierTerm],
			{
				{key -> "And", name -> coreConstant[HoldComplete["and"]]},
				{key -> "Or", name -> coreConstant[HoldComplete["or"]]},
				{key -> "FirstProjection", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, Construct[lambdaAbstraction, HoldComplete["y"], carrierTerm, boundVariable[1], "Explicit"], "Explicit"]},
				{key -> "SecondProjection", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, Construct[lambdaAbstraction, HoldComplete["y"], carrierTerm, boundVariable[0], "Explicit"], "Explicit"]},
				{key -> "ImpliesNotLeft", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, Construct[lambdaAbstraction, HoldComplete["y"], carrierTerm, makeApplication[coreConstant[HoldComplete["and"]], {Construct[application, coreConstant[HoldComplete["not"]], boundVariable[1]], boundVariable[0]}], "Explicit"], "Explicit"]}
			},

		(* Binary relation R : T -> T -> Prop *)
		MatchQ[subType, dependentFunctionType[_, d1_, dependentFunctionType[_, d2_, universeSort[0], _], _] /; d1 === carrierTerm && d2 === carrierTerm],
			{
				{key -> "Equal", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, Construct[lambdaAbstraction, HoldComplete["y"], carrierTerm, coreEquality[carrierTerm, boundVariable[1], boundVariable[0], {1}], "Explicit"], "Explicit"]},
				{key -> "AlwaysTrue", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, Construct[lambdaAbstraction, HoldComplete["y"], carrierTerm, coreTrue[], "Explicit"], "Explicit"]},
				{key -> "AlwaysFalse", name -> Construct[lambdaAbstraction, HoldComplete["x"], carrierTerm, Construct[lambdaAbstraction, HoldComplete["y"], carrierTerm, coreFalse[], "Explicit"], "Explicit"]}
			},

		True,
			{}
	]
]


(* Honest Undetermined result, enriched with classical-provability / axiom sensitivity info when constructive *)
buildUndeterminedResult[environment_, coreStmt_, uParams_List, surfaceTerm_, compDecidable_] := Module[{details = <||>, prelude, classicalProof, axSummary},
	If[ ! constantDeclaredQ[environment, HoldComplete["excludedMiddle"]],
		prelude = TypeTheoryEnvironment["Prelude"];
		If[ AllTrue[DeleteDuplicates[Cases[coreStmt, constantReference[n_, _] :> n, {0, Infinity}]], Function[n, constantDeclaredQ[prelude, n]]],
			classicalProof = enhancedProveCore[prelude, coreStmt, uParams, 2.0];
			If[ ! FailureQ[classicalProof],
				axSummary = proofAxiomSummary[classicalProof];
				details = <|
					"ClassicallyProvable" -> True,
					"RequiredAxioms" -> axSummary["Axioms"],
					"ClassicalProof" -> classicalProof
				|>
			]
		]
	];
	determineResult["Undetermined", surfaceTerm, None, None, None, None, compDecidable, "SearchExhausted", details]
]


(* ::Section:: *)
(*Superfunction 2: TypeTheoryAssumptions*)


(* Open TypeTheoryProof input (literal or held in a symbol): extract & simplify open goals as hole-filling assumptions *)
SetAttributes[openProofExpressionQ, HoldFirst]
openProofExpressionQ[_TypeTheoryProof] := True
openProofExpressionQ[symbol_Symbol] := MatchQ[symbol, _TypeTheoryProof] /; ValueQ[symbol]
openProofExpressionQ[_] := False

TypeTheoryAssumptions[openProof_, opts : OptionsPattern[]] /; openProofExpressionQ[openProof] :=
	catchKernelFailure @ assumptionsFromOpenProof[openProof, Hold[opts]]

TypeTheoryAssumptions[proposition_, opts : OptionsPattern[]] /; statementQ[Unevaluated[proposition]] :=
	catchKernelFailure @ findAssumptions[HoldComplete[proposition], Automatic, Hold[opts]]

TypeTheoryAssumptions[proposition_, environment : Except[_Rule | _RuleDelayed], opts : OptionsPattern[]] /; statementQ[Unevaluated[proposition]] :=
	catchKernelFailure @ findAssumptions[HoldComplete[proposition], environment, Hold[opts]]


assumptionsFromOpenProof[TypeTheoryProof[data_Association], Hold[opts___]] := Module[
	{environment = data["Environment"], uParams = data["UniverseParameters"], goals = data["Goals"], maxItems},
	maxItems = Replace[OptionValue[TypeTheoryAssumptions, {opts}, MaxItems], Except[_Integer?Positive] -> 5];
	If[ goals === {},
		{},

		Take[
			Function[goalId,
				With[{current = currentGoal[data, goalId]},
					{needed = neededContext[current["Context"], current["Type"]]},
					{abstracted = makeDependentFunctionType[needed, Keys[needed], current["Type"]]},
					{
						(* Verify that abstracted closes this goal when applied to the needed local variables *)
						hId = freshFreeVariable[],
						implicationCore = coreImplication[abstracted, makeDependentFunctionType[needed, Keys[needed], current["Type"]]]
					},
					{
						proof = proveFromCore[environment, implicationCore, uParams, {TypeTheoryTactic["Introduce"], TypeTheoryTactic["Assumption"]}]
					},
					<|
						"Assumption" -> coreToTypeTheoryTerm[environment, <||>, abstracted],
						"Statement" -> coreToTypeTheoryTerm[environment, <||>, implicationCore],
						"Proof" -> proof,
						"Scope" -> "GoalHole",
						"Witness" -> None,
						"Method" -> "OpenGoalAbstraction",
						"Verified" -> ! FailureQ[proof]
					|>
				]
			] /@ goals,
			UpTo[maxItems]
		]
	]
]


SetAttributes[findAssumptions, HoldFirst]
findAssumptions[HoldComplete[proposition_], environmentSpec_, Hold[opts___]] := Module[
	{resolved, environment, coreStmt, uParams, methodOpt, timeBudget, maxItems, allowEquiv, includeOpen, llmEval, progressOpt,
	 alreadyProved, unpacked, varContext, varIds, bodyCore, rawCandidates = {}, deduped, totalCands, verified = {}, timedOut = {}, ranked},
	resolved = resolveProposition[proposition, environmentSpec];
	If[ FailureQ[resolved],
		resolved,

		environment = resolved["Environment"];
		coreStmt = resolved["CoreStatement"];
		uParams = resolved["UniverseParameters"];
		methodOpt = OptionValue[TypeTheoryAssumptions, {opts}, Method];
		timeBudget = Replace[OptionValue[TypeTheoryAssumptions, {opts}, TimeConstraint], Except[_?Positive] -> 15];
		maxItems = Replace[OptionValue[TypeTheoryAssumptions, {opts}, MaxItems], Except[_Integer?Positive] -> 5];
		allowEquiv = TrueQ[OptionValue[TypeTheoryAssumptions, {opts}, "EquivalentConditions"]];
		includeOpen = TrueQ[OptionValue[TypeTheoryAssumptions, {opts}, "IncludeOpen"]];
		llmEval = OptionValue[TypeTheoryAssumptions, {opts}, "LLMEvaluator"];
		progressOpt = OptionValue[TypeTheoryAssumptions, {opts}, ProgressReporting];

		Block[{$superfunctionScale = superfunctionScale[timeBudget]}, withSuperfunctionProgress["TypeTheoryAssumptions", progressOpt, timeBudget,
			(* If already provable, no extra assumptions are needed *)
			reportProgress["Checking whether proposition is already provable...", 0.08];
			alreadyProved = enhancedProveCore[environment, coreStmt, uParams, remainingBudget[budgetScaled[1.5]]];
			If[ ! FailureQ[alreadyProved],
				{},

				unpacked = peelLeadingDataBinders[environment, <||>, coreStmt];
				varContext = unpacked["Context"];
				varIds = unpacked["VariableIds"];
				bodyCore = unpacked["Body"];

				If[ useHeuristicQ[methodOpt] && ! deadlineExceededQ[],
					reportProgress["Running symbolic domain abduction...", 0.18];
					rawCandidates = Join[rawCandidates, abduceSymbolicDomain[environment, varContext, varIds, bodyCore, uParams]];
					If[ ! deadlineExceededQ[],
						reportProgress["Running tactic-residual and axiom-diff abduction...", 0.30];
						rawCandidates = Join[
							rawCandidates,
							abduceLemmaResiduals[environment, varContext, varIds, bodyCore, uParams],
							abduceAxiomDiff[environment, coreStmt, uParams]
						]
					];
					If[ ! deadlineExceededQ[],
						reportProgress["Running counterexample refinement and algebraic catalog...", 0.42];
						rawCandidates = Join[
							rawCandidates,
							abduceCounterexampleGuards[environment, varContext, varIds, bodyCore, coreStmt, uParams],
							abduceAlgebraicProperties[environment, coreStmt, uParams]
						]
					]
				];

				If[ useLLMQ[methodOpt],
					reportProgress["Querying LLMFunction for candidate assumptions...", 0.50];
					rawCandidates = Join[rawCandidates, abduceViaLLM[environment, coreStmt, varContext, varIds, bodyCore, uParams, llmEval, remainingBudget[timeBudget]]]
				];

				(* Gate 1-3: Kernel proof, non-vacuity, non-triviality with progress & deadline guard *)
				deduped = SortBy[deduplicateRawAssumptionCandidates[rawCandidates], coreComplexity[#["CoreAssumption"]] &];
				totalCands = Length[deduped];
				MapIndexed[
					Function[{cand, idx},
						If[ ! deadlineExceededQ[] || verified === {},
							reportProgress[
								"Verifying assumption candidate " <> IntegerString[First[idx]] <> "/" <> IntegerString[totalCands] <> " in kernel...",
								0.55 + 0.35 * (First[idx] / Max[1, totalCands])
							];
							With[{res = verifyAndFilterAssumption[environment, coreStmt, varContext, varIds, bodyCore, uParams, cand, allowEquiv, includeOpen, Function[budgetScaled[2.5]]]},
								Which[
									AssociationQ[res], AppendTo[verified, res],
									MatchQ[res, Missing["TimedOut"]], AppendTo[timedOut, cand]
								]
							]
						]
					],
					deduped
				];

				(* Second pass: a candidate whose sufficiency proof ran out of time tries again with what is left of the budget *)
				MapIndexed[
					Function[{cand, idx},
						With[{left = Length[timedOut] - First[idx] + 1},
							If[ ! deadlineExceededQ[] && retryProofBudget[budgetScaled[2.5], left] > budgetScaled[2.5],
								reportProgress[
									"Retrying assumption candidate " <> IntegerString[First[idx]] <> "/" <> IntegerString[Length[timedOut]] <> " with more time...",
									0.90 + 0.05 * (First[idx] / Max[1, Length[timedOut]])
								];
								With[{res = verifyAndFilterAssumption[environment, coreStmt, varContext, varIds, bodyCore, uParams, cand, allowEquiv, includeOpen, Function[retryProofBudget[budgetScaled[2.5], left]]]},
									If[ AssociationQ[res],
										AppendTo[verified, res]
									]
								]
							]
						]
					],
					timedOut
				];

				(* Gate 4: Deduplication & Pareto weakness ranking *)
				reportProgress["Pruning and ranking verified assumptions...", 0.95];
				ranked = rankAndDeduplicateAssumptions[environment, varContext, varIds, uParams, verified];
				Take[ranked, UpTo[maxItems]]
			]
		]]
	]
]


(* Peel leading non-propositional universal binders (e.g. ForAll[{Typed[a, N], Typed[b, N]}, body]) *)
peelLeadingDataBinders[environment_, context_, term_] := Replace[weakHeadNormalForm[environment, context, term], {
	dependentFunctionType[name_, domain_, codomain_, binder_] /; ! TrueQ[Quiet @ propositionQ[environment, context, domain]] :> With[
		{id = freshFreeVariable[]},
		{extCtx = extendContext[context, id, name, domain, binder]},
		{rest = peelLeadingDataBinders[environment, extCtx, betaNormalize[instantiateBoundVariable[codomain, freeVariable[id]]]]},
		<|
			"Context" -> rest["Context"],
			"VariableIds" -> Prepend[rest["VariableIds"], id],
			"Body" -> rest["Body"]
		|>
	],
	_ :> <|"Context" -> context, "VariableIds" -> {}, "Body" -> term|>
}]


(* Split bodyCore into existing propositional premises and final consequent *)
splitPropositionalImplication[environment_, context_, term_] := Replace[weakHeadNormalForm[environment, context, term], {
	dependentFunctionType[name_, domain_, codomain_, binder_] /; TrueQ[Quiet @ propositionQ[environment, context, domain]] && looseBoundRange[codomain] == 0 :> With[
		{rest = splitPropositionalImplication[environment, context, codomain]},
		<|"Premises" -> Prepend[rest["Premises"], domain], "Consequent" -> rest["Consequent"]|>
	],
	_ :> <|"Premises" -> {}, "Consequent" -> term|>
}]


deduplicateRawAssumptionCandidates[candidates_List] := DeleteDuplicatesBy[candidates, Function[c, {c["Scope"], c["CoreAssumption"]}]]


(* Gates 1, 2, 3 for a single assumption candidate: the verified item, None when a gate rejects it, or
   Missing["TimedOut"] when its sufficiency proof ran out of time. proofBudget[] is that proof's time, reckoned when
   the proof starts. *)
verifyAndFilterAssumption[environment_, coreStmt_, varContext_, varIds_List, bodyCore_, uParams_List, cand_Association, allowEquiv_, includeOpen_, proofBudget_] := Module[
	{scope = cand["Scope"], coreA = cand["CoreAssumption"], method = cand["Method"],
	 targetBody, implCore, splitBody, proof, witness = None, isVacuous = False, isTrivial = False, equivCheck},

	(* Reject literal False or syntactically identical to body / whole statement *)
	If[ coreA === coreFalse[] || coreA === coreTrue[],
		None,

		targetBody = If[scope === "Local", bodyCore, coreStmt];
		If[ TrueQ[Quiet @ withKernelCaches[definitionallyEqualQ[environment, If[scope === "Local", varContext, <||>], coreA, targetBody]]],
			None,

			(* Reject if coreA contains targetBody as a top-level conjunct *)
			If[ MemberQ[flattenConjunctions[coreA], targetBody],
				None,

				(* Reject if bodyCore is H => C and coreA is literally C or implies C without using H *)
				splitBody = If[scope === "Local", splitPropositionalImplication[environment, varContext, bodyCore], <|"Premises" -> {}, "Consequent" -> coreStmt|>];
				If[ splitBody["Premises"] =!= {},
					With[{directCheck = makeDependentFunctionType[varContext, varIds, coreImplication[coreA, splitBody["Consequent"]]]},
						If[ coreA === splitBody["Consequent"] || ! FailureQ[enhancedProveCore[environment, directCheck, uParams, budgetScaled[0.4]]],
							isTrivial = True
						]
					]
				];
				If[ isTrivial,
					None,

					(* Build implication statement *)
					implCore = If[ scope === "Local",
						makeDependentFunctionType[varContext, varIds, coreImplication[coreA, bodyCore]],
						coreImplication[coreA, coreStmt]
					];

					(* Gate 2: Non-vacuity check *)
					{isVacuous, witness} = checkAssumptionNonVacuity[environment, varContext, varIds, coreA, scope, uParams];
					If[ isVacuous,
						None,

						(* Gate 1: Sufficiency (kernel proof of implication) *)
						proof = enhancedProveCore[environment, implCore, uParams, proofBudget[]];
						If[ FailureQ[proof] && ! includeOpen,
							If[ MatchQ[proof, Failure["TimedOut", _]], Missing["TimedOut"], None ],

							(* Gate 3: Non-triviality against semantic equivalence *)
							If[ ! FailureQ[proof],
								With[
									{
										revImpl = If[ scope === "Local",
											makeDependentFunctionType[varContext, varIds, coreImplication[bodyCore, coreA]],
											coreImplication[coreStmt, coreA]
										]
									},
									equivCheck = ! FailureQ[enhancedProveCore[environment, revImpl, uParams, budgetScaled[0.5]]];
									If[ equivCheck && (! allowEquiv || coreComplexity[coreA] >= coreComplexity[targetBody]),
										isTrivial = True
									]
								]
							];
							If[ isTrivial,
								None,

								<|
									"Assumption" -> coreToTypeTheoryTerm[environment, If[scope === "Local", varContext, <||>], coreA],
									"Statement" -> coreToTypeTheoryTerm[environment, <||>, implCore],
									"Proof" -> If[FailureQ[proof], None, proof],
									"Witness" -> witness,
									"Scope" -> scope,
									"Method" -> method,
									"Verified" -> ! FailureQ[proof],
									"CoreAssumption" -> coreA,
									"Complexity" -> coreComplexity[coreA],
									"Extra" -> Lookup[cand, "Extra", <||>]
								|>
							]
						]
					]
				]
			]
		]
	]
]

flattenConjunctions[application[application[constantReference[HoldComplete[And], _], a_], b_]] := Join[flattenConjunctions[a], flattenConjunctions[b]]
flattenConjunctions[other_] := {other}

(* Check non-vacuity: reject if Not[Exists[xs, A]] (or Not[A]) is provable; certify witness if possible *)
checkAssumptionNonVacuity[environment_, varContext_, varIds_List, coreA_, "Local", uParams_List] := Module[{exCore, witProof, refProof},
	If[ varIds === {},
		checkAssumptionNonVacuity[environment, <||>, {}, coreA, "Global", uParams],

		exCore = wrapExistentialsCore[varContext, varIds, coreA];
		If[ exCore === None,
			{False, None},

			witProof = enhancedProveCore[environment, exCore, uParams, budgetScaled[0.8]];
			If[ ! FailureQ[witProof],
				{False, extractWitnessFromProof[environment, exCore, witProof]},

				refProof = enhancedProveCore[environment, coreNegation[environment, exCore], uParams, budgetScaled[0.5]];
				{! FailureQ[refProof], None}
			]
		]
	]
]
checkAssumptionNonVacuity[environment_, _, _, coreA_, "Global", uParams_List] := Module[{refProof},
	refProof = enhancedProveCore[environment, coreNegation[environment, coreA], uParams, budgetScaled[0.6]];
	{! FailureQ[refProof], None}
]

wrapExistentialsCore[context_, {}, body_] := body
wrapExistentialsCore[context_, {id_, rest___}, body_] := Module[{inner, entry = context[id]},
	inner = wrapExistentialsCore[context, {rest}, body];
	If[ inner === None,
		None,
		coreExists[entry["Type"], entry["Name"], abstractFreeVariable[inner, id], {1}]
	]
]


(* Gate 4: Deduplication and Pareto weakness ranking *)
rankAndDeduplicateAssumptions[environment_, varContext_, varIds_List, uParams_List, items_List] := Module[
	{localItems, globalItems, rankedLocal, rankedGlobal},
	localItems = Select[items, #["Scope"] === "Local" &];
	globalItems = Select[items, #["Scope"] =!= "Local" &];
	rankedLocal = paretoRankGroup[environment, varContext, varIds, uParams, localItems, True];
	rankedGlobal = paretoRankGroup[environment, <||>, {}, uParams, globalItems, False];
	KeyDrop[#, {"CoreAssumption", "Complexity", "Extra"}] & /@ Join[rankedLocal, rankedGlobal]
]

paretoRankGroup[environment_, varContext_, varIds_List, uParams_List, items_List, isLocal_] := Module[
	{n = Length[items], impliesMatrix, dedupIndices, dominatedCounts, kept},
	If[ n <= 1,
		items,

		impliesMatrix = Table[
			If[ i === j,
				True,
				With[
					{
						aI = First[Drop[items, i - 1]]["CoreAssumption"],
						aJ = First[Drop[items, j - 1]]["CoreAssumption"]
					},
					With[
						{
							impl = If[ isLocal,
								makeDependentFunctionType[varContext, varIds, coreImplication[aI, aJ]],
								coreImplication[aI, aJ]
							]
						},
						! FailureQ[enhancedProveCore[environment, impl, uParams, budgetScaled[0.8]]]
					]
				]
			],
			{i, n},
			{j, n}
		];
		(* Deduplicate mutually equivalent items, keeping the syntactically simplest *)
		dedupIndices = Fold[
			Function[{chosen, idx},
				With[
					{
						equivIdx = SelectFirst[chosen, Function[c,
							First[Drop[First[Drop[impliesMatrix, idx - 1]], c - 1]] &&
							First[Drop[First[Drop[impliesMatrix, c - 1]], idx - 1]]
						], None]
					},
					If[ equivIdx === None,
						Append[chosen, idx],
						If[ First[Drop[items, idx - 1]]["Complexity"] < First[Drop[items, equivIdx - 1]]["Complexity"],
							Append[DeleteCases[chosen, equivIdx], idx],
							chosen
						]
					]
				]
			],
			{},
			Range[n]
		];
		(* Score each survivor by how many other survivors strictly dominate (are strictly weaker than) it; a tie goes to
		   the earlier candidate, as SortBy would otherwise order tied items by their whole expressions, whose proofs name
		   environment stores by counters that differ from session to session *)
		kept = Function[idx,
			With[
				{
					item = First[Drop[items, idx - 1]],
					domCount = Count[dedupIndices, Function[other,
						other =!= idx &&
						First[Drop[First[Drop[impliesMatrix, idx - 1]], other - 1]] &&
						! First[Drop[First[Drop[impliesMatrix, other - 1]], idx - 1]]
					]]
				},
				{domCount, item["Complexity"], If[item["Witness"] =!= None, 0, 1], idx, item}
			]
		] /@ dedupIndices;
		Last /@ SortBy[kept, Most]
	]
]


(* --- Assumption Engine E1: Symbolic Domain Abduction (Reduce / Resolve + finite-failure tail scan) --- *)
abduceSymbolicDomain[environment_, varContext_, varIds_List, bodyCore_, uParams_List] := Module[
	{domains, wlVars, wlVarMap, wlCond, domCond, reduced, rawWlCandidates = {}, badVals, maxBad, nVar},
	If[ varIds === {},
		{},

		domains = AssociationMap[Function[id, numberDomainExtended[environment, varContext, varContext[id]["Type"]]], varIds];
		If[ ! AllTrue[Values[domains], # =!= None &],
			{},

			wlVars = Table[Subscript[\[FormalX], k], {k, Length[varIds]}];
			wlVarMap = AssociationThread[varIds, wlVars];
			wlCond = corePropToWolfram[environment, varContext, wlVarMap, bodyCore];
			If[ wlCond === $Failed,
				{},

				domCond = And @@ MapThread[Function[{v, d}, If[d === NonNegativeIntegers, v >= 0, True]], {wlVars, Values[domains]}];
				With[{wlDomain = If[MemberQ[Values[domains], Rationals], Reals, Integers]},
					reduced = TimeConstrained[Quiet @ Reduce[domCond && wlCond, wlVars, wlDomain], budgetScaled[2], $Aborted];
					If[ (reduced === $Aborted || MatchQ[reduced, _Reduce] || ! FreeQ[reduced, _C]) && wlDomain === Integers,
						reduced = TimeConstrained[Quiet @ Reduce[domCond && wlCond, wlVars, Reals], budgetScaled[2], $Aborted]
					]
				];
				If[ reduced =!= $Aborted && reduced =!= False && reduced =!= True && ! MatchQ[reduced, _Reduce],
					With[{simplified = TimeConstrained[Quiet @ Simplify[reduced, domCond], budgetScaled[1.5], reduced]},
						rawWlCandidates = Join[
							rawWlCandidates,
							If[simplified =!= reduced && simplified =!= True && simplified =!= False, {simplified}, {}],
							extractRegionsFromReduce[reduced, wlVars, Values[domains]]
						]
					]
				];

				(* Also handle 1-variable non-algebraic/exponential predicates over NonNegativeIntegers (e.g. n^2 <= 2^n) *)
				If[ Length[varIds] === 1 && First[Values[domains]] === NonNegativeIntegers,
					nVar = First[wlVars];
					badVals = Select[Range[0, 20], Function[k, ! TrueQ[Quiet[ReplaceAll[wlCond, nVar -> k]]]]];
					If[ badVals =!= {} && Length[badVals] <= 5,
						maxBad = Max[badVals];
						If[ AllTrue[Range[maxBad + 1, maxBad + 10], Function[k, TrueQ[Quiet[ReplaceAll[wlCond, nVar -> k]]]]],
							rawWlCandidates = Join[rawWlCandidates, {
								And @@ ((nVar != #) & /@ badVals),
								(maxBad + 1) <= nVar
							}]
						]
					]
				];

				(* Convert candidate WL formulas back into core TypeTheory terms *)
				DeleteCases[
					Function[wlFormula,
						With[{coreCand = wolframCondToCore[environment, varContext, AssociationThread[wlVars, varIds], domains, wlFormula]},
							If[ coreCand === $Failed,
								None,
								<|"Scope" -> "Local", "CoreAssumption" -> coreCand, "Method" -> "SymbolicDomain"|>
							]
						]
					] /@ DeleteDuplicates[rawWlCandidates],
					None
				]
			]
		]
	]
]

numberDomainExtended[environment_, context_, type_] := Which[
	naturalNumberTypeQ[environment, context, type], NonNegativeIntegers,
	integerTypeQ[environment, type], Integers,
	rationalTypeQ[environment, type], Rationals,
	True, None
]

(* Extract clean candidate conditions from Reduce output, stripping redundant nonnegativity domain guards *)
extractRegionsFromReduce[reduced_, wlVars_List, domains_List] := Module[{expanded, cleaned, disjuncts, candidates = {}},
	expanded = Quiet[LogicalExpand[reduced]];
	cleaned = stripDomainGuards[expanded, wlVars, domains];
	If[ cleaned =!= True && cleaned =!= False,
		AppendTo[candidates, cleaned]
	];
	disjuncts = If[MatchQ[cleaned, _Or], List @@ cleaned, {cleaned}];
	Scan[
		Function[branch,
			With[{simp = stripDomainGuards[branch, wlVars, domains]},
				If[ simp =!= True && simp =!= False,
					AppendTo[candidates, simp];
					(* Also try each individual conjunct of a branch (e.g. b <= a from a > 0 && b <= a) *)
					If[ MatchQ[simp, _And],
						Scan[
							Function[conj,
								If[conj =!= True && conj =!= False, AppendTo[candidates, conj]]
							],
							List @@ simp
						]
					];
					(* Also generate clean variants like c != 0 alongside c >= 1 over NonNegativeIntegers *)
					Replace[simp, {
						(v_ >= 1 | 1 <= v_ | v_ > 0 | 0 < v_) /; MemberQ[wlVars, v] :> (AppendTo[candidates, v != 0]; AppendTo[candidates, 1 <= v]),
						(v_ != 0) /; MemberQ[wlVars, v] :> AppendTo[candidates, 1 <= v]
					}]
				]
			]
		],
		disjuncts
	];
	DeleteDuplicates[candidates]
]

stripDomainGuards[expr_, wlVars_List, domains_List] := stripDomainGuardsStep[expr, Pick[wlVars, domains, NonNegativeIntegers]]

stripDomainGuardsStep[And[parts__], natVars_List] := With[
	{kept = Select[stripDomainGuardsStep[#, natVars] & /@ {parts}, Function[p, p =!= True && ! redundantNatGuardQ[p, natVars]]]},
	Replace[kept, {{} -> True, {one_} :> one, many_ :> And @@ many}]
]
stripDomainGuardsStep[Or[parts__], natVars_List] := Or @@ (stripDomainGuardsStep[#, natVars] & /@ {parts})
stripDomainGuardsStep[Inequality[0, LessEqual, v_, LessEqual, hi_], natVars_List] /; MemberQ[natVars, v] := (v <= hi)
stripDomainGuardsStep[Inequality[0, LessEqual, v_, Less, hi_], natVars_List] /; MemberQ[natVars, v] := (v < hi)
stripDomainGuardsStep[Inequality[lo_, LessEqual, v_, LessEqual, hi_], _] := (lo <= v && v <= hi)
stripDomainGuardsStep[Inequality[lo_, Less, v_, LessEqual, hi_], _] := (lo < v && v <= hi)
stripDomainGuardsStep[Inequality[lo_, LessEqual, v_, Less, hi_], _] := (lo <= v && v < hi)
stripDomainGuardsStep[Inequality[lo_, Less, v_, Less, hi_], _] := (lo < v && v < hi)
stripDomainGuardsStep[other_, natVars_List] := If[redundantNatGuardQ[other, natVars], True, other]

redundantNatGuardQ[v_ >= 0, natVars_List] := MemberQ[natVars, v]
redundantNatGuardQ[0 <= v_, natVars_List] := MemberQ[natVars, v]
redundantNatGuardQ[Element[_, Integers | Reals], _] := True
redundantNatGuardQ[_, _] := False


(* Core proposition -> Wolfram Language expression (extended over N, Z, Q) *)
corePropToWolfram[environment_, context_, varMap_Association, term_] := Replace[term, {
	application[application[application[constantReference[HoldComplete[Equal], _], type_], l_], r_] /; numberDomainExtended[environment, context, type] =!= None :>
		With[{wlL = coreExprToWolfram[environment, context, varMap, l], wlR = coreExprToWolfram[environment, context, varMap, r]},
			If[wlL === $Failed || wlR === $Failed, $Failed, wlL == wlR]
		],
	application[application[constantReference[HoldComplete[LessEqual], _], l_], r_] :>
		With[{wlL = coreExprToWolfram[environment, context, varMap, l], wlR = coreExprToWolfram[environment, context, varMap, r]},
			If[wlL === $Failed || wlR === $Failed, $Failed, wlL <= wlR]
		],
	application[application[constantReference[HoldComplete[Less], _], l_], r_] :>
		With[{wlL = coreExprToWolfram[environment, context, varMap, l], wlR = coreExprToWolfram[environment, context, varMap, r]},
			If[wlL === $Failed || wlR === $Failed, $Failed, wlL < wlR]
		],
	application[application[constantReference[HoldComplete[rel : "integerLessEqual" | "integerLess" | "integerGreaterEqual" | "integerGreater" | "rationalLessEqual" | "rationalLess"], _], l_], r_] :>
		With[{wlL = coreExprToWolfram[environment, context, varMap, l], wlR = coreExprToWolfram[environment, context, varMap, r]},
			If[ wlL === $Failed || wlR === $Failed,
				$Failed,
				Replace[rel, {
					"integerLessEqual" | "rationalLessEqual" :> wlL <= wlR,
					"integerLess" | "rationalLess" :> wlL < wlR,
					"integerGreaterEqual" :> wlL >= wlR,
					"integerGreater" :> wlL > wlR
				}]
			]
		],
	application[application[constantReference[HoldComplete[And], _], l_], r_] :>
		With[{wlL = corePropToWolfram[environment, context, varMap, l], wlR = corePropToWolfram[environment, context, varMap, r]},
			If[wlL === $Failed || wlR === $Failed, $Failed, wlL && wlR]
		],
	application[application[constantReference[HoldComplete[Or], _], l_], r_] :>
		With[{wlL = corePropToWolfram[environment, context, varMap, l], wlR = corePropToWolfram[environment, context, varMap, r]},
			If[wlL === $Failed || wlR === $Failed, $Failed, wlL || wlR]
		],
	constantReference[HoldComplete[True], _] :> True,
	constantReference[HoldComplete[False], _] :> False,
	dependentFunctionType[_, premise_, constantReference[HoldComplete[False], _], _] :>
		With[{wlP = corePropToWolfram[environment, context, varMap, premise]},
			If[wlP === $Failed, $Failed, Not[wlP]]
		],
	dependentFunctionType[_, premise_, codomain_, _] /; looseBoundRange[codomain] == 0 :>
		With[{wlP = corePropToWolfram[environment, context, varMap, premise], wlC = corePropToWolfram[environment, context, varMap, codomain]},
			If[wlP === $Failed || wlC === $Failed, $Failed, Implies[wlP, wlC]]
		],
	other_ :> With[{reduced = weakHeadNormalForm[environment, context, other]},
		If[reduced =!= other, corePropToWolfram[environment, context, varMap, reduced], $Failed]
	]
}]

coreExprToWolfram[environment_, context_, varMap_Association, term_] := Replace[term, {
	freeVariable[id_] /; KeyExistsQ[varMap, id] :> varMap[id],
	constantReference[name_, _] /; KeyExistsQ[varMap, name] :> varMap[name],
	naturalLiteral[n_Integer] :> n,
	constantReference[HoldComplete["zero"], _] :> 0,
	application[constantReference[HoldComplete["successor"], _], a_] :>
		With[{w = coreExprToWolfram[environment, context, varMap, a]}, If[w === $Failed, $Failed, w + 1]],
	application[application[constantReference[HoldComplete[op : Plus | Times | Power | Subtract], _], l_], r_] :>
		With[{wlL = coreExprToWolfram[environment, context, varMap, l], wlR = coreExprToWolfram[environment, context, varMap, r]},
			If[ wlL === $Failed || wlR === $Failed,
				$Failed,
				Replace[op, {Plus :> wlL + wlR, Times :> wlL * wlR, Power :> wlL ^ wlR, Subtract :> Max[wlL - wlR, 0]}]
			]
		],
	application[application[constantReference[HoldComplete[op : "integerAddition" | "integerMultiplication" | "integerSubtraction" | "integerPower" | "rationalAddition" | "rationalMultiplication" | "rationalSubtraction" | "rationalDivision"], _], l_], r_] :>
		With[{wlL = coreExprToWolfram[environment, context, varMap, l], wlR = coreExprToWolfram[environment, context, varMap, r]},
			If[ wlL === $Failed || wlR === $Failed,
				$Failed,
				Replace[op, {
					"integerAddition" | "rationalAddition" :> wlL + wlR,
					"integerMultiplication" | "rationalMultiplication" :> wlL * wlR,
					"integerSubtraction" | "rationalSubtraction" :> wlL - wlR,
					"integerPower" :> wlL ^ wlR,
					"rationalDivision" :> wlL / wlR
				}]
			]
		],
	application[constantReference[HoldComplete["integerNegation" | "rationalNegation"], _], a_] :>
		With[{w = coreExprToWolfram[environment, context, varMap, a]}, If[w === $Failed, $Failed, -w]],
	application[constantReference[HoldComplete["integerOfNatural" | "rationalOfInteger"], _], a_] :>
		coreExprToWolfram[environment, context, varMap, a],
	_ :> $Failed
}]


(* Wolfram Language condition -> core TypeTheory proposition *)
wolframCondToCore[environment_, context_, revVarMap_Association, domains_Association, cond_] := Module[{primaryDomain},
	primaryDomain = If[ MemberQ[Values[domains], Rationals],
		Rationals,
		If[MemberQ[Values[domains], Integers], Integers, NonNegativeIntegers]
	];
	wlCondToCoreIn[environment, revVarMap, primaryDomain, cond]
]

wlCondToCoreIn[environment_, revVarMap_, domain_, True] := coreTrue[]
wlCondToCoreIn[environment_, revVarMap_, domain_, False] := coreFalse[]
wlCondToCoreIn[environment_, revVarMap_, domain_, Not[p_]] := With[{cp = wlCondToCoreIn[environment, revVarMap, domain, p]},
	If[cp === $Failed, $Failed, coreNegation[environment, cp]]
]
wlCondToCoreIn[environment_, revVarMap_, domain_, And[a_, b__]] := With[
	{parts = wlCondToCoreIn[environment, revVarMap, domain, #] & /@ {a, b}},
	If[MemberQ[parts, $Failed], $Failed, Fold[coreConjunction, parts]]
]
wlCondToCoreIn[environment_, revVarMap_, domain_, Or[a_, b__]] := With[
	{parts = wlCondToCoreIn[environment, revVarMap, domain, #] & /@ {a, b}},
	If[MemberQ[parts, $Failed], $Failed, Fold[coreDisjunction, parts]]
]
wlCondToCoreIn[environment_, revVarMap_, domain_, Equal[a_, b_]] := With[
	{ca = wlExprToCoreIn[environment, revVarMap, domain, a], cb = wlExprToCoreIn[environment, revVarMap, domain, b]},
	If[ca === $Failed || cb === $Failed, $Failed, coreEquality[domainTypeCore[domain], ca, cb, {1}]]
]
wlCondToCoreIn[environment_, revVarMap_, domain_, Unequal[a_, b_]] := With[
	{eq = wlCondToCoreIn[environment, revVarMap, domain, Equal[a, b]]},
	If[eq === $Failed, $Failed, coreNegation[environment, eq]]
]
wlCondToCoreIn[environment_, revVarMap_, domain_, LessEqual[a_, b_]] := With[
	{ca = wlExprToCoreIn[environment, revVarMap, domain, a], cb = wlExprToCoreIn[environment, revVarMap, domain, b]},
	If[ca === $Failed || cb === $Failed, $Failed, domainLessEqualCore[domain, ca, cb]]
]
wlCondToCoreIn[environment_, revVarMap_, domain_, GreaterEqual[a_, b_]] := wlCondToCoreIn[environment, revVarMap, domain, LessEqual[b, a]]
wlCondToCoreIn[environment_, revVarMap_, domain_, Less[a_, b_]] := With[
	{ca = wlExprToCoreIn[environment, revVarMap, domain, a], cb = wlExprToCoreIn[environment, revVarMap, domain, b]},
	If[ca === $Failed || cb === $Failed, $Failed, domainLessCore[domain, ca, cb]]
]
wlCondToCoreIn[environment_, revVarMap_, domain_, Greater[a_, b_]] := wlCondToCoreIn[environment, revVarMap, domain, Less[b, a]]
wlCondToCoreIn[_, _, _, _] := $Failed

domainTypeCore[NonNegativeIntegers] := coreNaturals[]
domainTypeCore[Integers] := coreIntegers[]
domainTypeCore[Rationals] := coreRationals[]

domainLessEqualCore[NonNegativeIntegers, a_, b_] := coreNaturalLessEqual[a, b]
domainLessEqualCore[Integers, a_, b_] := coreIntegerLessEqual[a, b]
domainLessEqualCore[Rationals, a_, b_] := makeApplication[coreConstant[HoldComplete["rationalLessEqual"]], {a, b}]

domainLessCore[NonNegativeIntegers, a_, b_] := coreNaturalLessEqual[coreNaturalPlus[a, naturalLiteral[1]], b]
domainLessCore[Integers, a_, b_] := coreIntegerLess[a, b]
domainLessCore[Rationals, a_, b_] := makeApplication[coreConstant[HoldComplete["rationalLess"]], {a, b}]

wlExprToCoreIn[environment_, revVarMap_Association, domain_, v_] /; KeyExistsQ[revVarMap, v] := Replace[revVarMap[v], {
	id_Integer :> freeVariable[id],
	name_HoldComplete :> coreConstant[name]
}]
wlExprToCoreIn[_, _, NonNegativeIntegers, n_Integer?NonNegative] := naturalLiteral[n]
wlExprToCoreIn[_, _, Integers, n_Integer] := coreIntegerLiteral[n]
wlExprToCoreIn[_, _, Rationals, n_Integer] := Construct[application, coreConstant[HoldComplete["rationalOfInteger"]], coreIntegerLiteral[n]]
wlExprToCoreIn[environment_, revVarMap_, NonNegativeIntegers, Plus[a_, b__]] := Module[{terms, pos, neg},
	terms = {a, b};
	If[ AllTrue[terms, ! MatchQ[#, _Integer?Negative | Times[_Integer?Negative, __]] &],
		With[{parts = wlExprToCoreIn[environment, revVarMap, NonNegativeIntegers, #] & /@ terms},
			If[MemberQ[parts, $Failed], $Failed, Fold[coreNaturalPlus, parts]]
		],
		$Failed
	]
]
wlExprToCoreIn[environment_, revVarMap_, Integers, Plus[a_, b__]] := With[
	{parts = wlExprToCoreIn[environment, revVarMap, Integers, #] & /@ {a, b}},
	If[MemberQ[parts, $Failed], $Failed, Fold[coreIntegerAddition, parts]]
]
wlExprToCoreIn[environment_, revVarMap_, NonNegativeIntegers, Times[a_, b__]] := With[
	{parts = wlExprToCoreIn[environment, revVarMap, NonNegativeIntegers, #] & /@ {a, b}},
	If[MemberQ[parts, $Failed], $Failed, Fold[coreNaturalTimes, parts]]
]
wlExprToCoreIn[environment_, revVarMap_, Integers, Times[-1, x_]] := With[
	{cx = wlExprToCoreIn[environment, revVarMap, Integers, x]},
	If[cx === $Failed, $Failed, coreIntegerNegation[cx]]
]
wlExprToCoreIn[environment_, revVarMap_, Integers, Times[a_, b__]] := With[
	{parts = wlExprToCoreIn[environment, revVarMap, Integers, #] & /@ {a, b}},
	If[MemberQ[parts, $Failed], $Failed, Fold[coreIntegerMultiplication, parts]]
]
wlExprToCoreIn[environment_, revVarMap_, NonNegativeIntegers, Power[a_, k_Integer?NonNegative]] := With[
	{ca = wlExprToCoreIn[environment, revVarMap, NonNegativeIntegers, a]},
	If[ca === $Failed, $Failed, coreNaturalPower[ca, naturalLiteral[k]]]
]
wlExprToCoreIn[_, _, _, _] := $Failed


(* --- Assumption Engine E2: Tactic-Residual & Environment Lemma Abduction --- *)
abduceLemmaResiduals[environment_, varContext_, varIds_List, bodyCore_, uParams_List] := Module[
	{initProof, introduced, data, goal, current, goalHead, matchingLemmas, results = {}},
	initProof = newProofState[environment, makeDependentFunctionType[varContext, varIds, bodyCore], uParams];
	introduced = introduceAll[initProof];
	If[ FailureQ[introduced] || introduced["Goals"] === {},
		{},

		data = First[introduced];
		goal = First[data["Goals"]];
		current = currentGoal[data, goal];
		goalHead = conclusionName[weakHeadNormalForm[environment, current["Context"], current["Type"]]];
		matchingLemmas = Select[
			environmentNames[environment],
			Function[name,
				With[{rec = constantRecord[environment, name]},
					rec["Kind"] === "Theorem" && conclusionName[rec["Type"]] === goalHead
				]
			]
		];
		(* Try applying up to 12 matching theorems within 2s; collect single simpler remaining subgoals *)
		TimeConstrained[
			Scan[
				Function[lemmaName,
					With[{applied = Quiet @ catchKernelFailure[Replace[lemmaName, HoldComplete[sym_] :> TypeTheoryTactic["Apply", sym][introduced]]]},
						If[ MatchQ[applied, _TypeTheoryProof] && applied["Goals"] =!= {},
							With[{remaining = dischargeEasySubgoals[applied]},
								If[ MatchQ[remaining, _TypeTheoryProof] && Length[remaining["Goals"]] === 1,
									With[{remData = First[remaining]},
										{remGoal = currentGoal[remData, First[remData["Goals"]]]},
										If[ SubsetQ[varIds, mentionedFreeVariables[remGoal["Type"]]] && coreComplexity[remGoal["Type"]] < coreComplexity[bodyCore],
											AppendTo[results, <|"Scope" -> "Local", "CoreAssumption" -> remGoal["Type"], "Method" -> "LemmaResidual", "Extra" -> <|"Lemma" -> nameToKey[lemmaName]|>|>]
										]
									]
								]
							]
						]
					]
				],
				Take[Reverse[matchingLemmas], UpTo[12]]
			],
			budgetScaled[2.0]
		];
		results
	]
]

dischargeEasySubgoals[proof_TypeTheoryProof] := Module[{data = First[proof], currentProof = proof},
	(* Try closing each goal with Assumption or Reflexivity or Decide; keep unsolved ones *)
	Do[
		If[ ! MatchQ[currentProof, _TypeTheoryProof] || currentProof["Goals"] === {},
			Break[]
		];
		With[
			{
				attempt = SelectFirst[
					{
						Quiet @ catchKernelFailure[TypeTheoryTactic["Assumption"][currentProof]],
						Quiet @ catchKernelFailure[TypeTheoryTactic["Reflexivity"][currentProof]],
						Quiet @ catchKernelFailure[TypeTheoryTactic["Decide"][currentProof]]
					},
					Function[r, MatchQ[r, _TypeTheoryProof]],
					Failure["None", <||>]
				]
			},
			If[ MatchQ[attempt, _TypeTheoryProof],
				currentProof = attempt,
				Break[]
			]
		],
		{Length[data["Goals"]]}
	];
	currentProof
]


(* --- Assumption Engine E3: Axiom Diff (e.g. excludedMiddle in Constructive) --- *)
abduceAxiomDiff[environment_, coreStmt_, uParams_List] := Module[{results = {}, emCore, pId, pCtx},
	If[ ! constantDeclaredQ[environment, HoldComplete["excludedMiddle"]] && constantDeclaredQ[environment, HoldComplete[Or]] && constantDeclaredQ[environment, HoldComplete[Not]],
		pId = freshFreeVariable[];
		pCtx = extendContext[<||>, pId, HoldComplete["p"], universeSort[0], "Explicit"];
		emCore = makeDependentFunctionType[pCtx, {pId}, coreDisjunction[freeVariable[pId], coreNegation[environment, freeVariable[pId]]]];
		AppendTo[results, <|
			"Scope" -> "Global",
			"CoreAssumption" -> emCore,
			"Method" -> "AxiomDiff",
			"Extra" -> <|"AxiomName" -> "excludedMiddle"|>
		|>]
	];
	results
]


(* --- Assumption Engine E4: Counterexample-Guided Refinement (CEGAR) --- *)
abduceCounterexampleGuards[environment_, varContext_, varIds_List, bodyCore_, coreStmt_, uParams_List] := Module[
	{negCore, ceProof, ceAssoc, results = {}},
	If[ varIds === {},
		{},

		negCore = coreNegation[environment, coreStmt];
		ceProof = Quiet @ catchKernelFailure[proveFromCore[environment, negCore, uParams, {TypeTheoryTactic["Counterexample"]}]];
		If[ FailureQ[ceProof],
			{},

			ceAssoc = extractCounterexampleFromProof[environment, coreStmt, ceProof];
			If[ ! AssociationQ[ceAssoc],
				{},

				(* For each variable in the counterexample, propose x != val and (if N) val + 1 <= x *)
				KeyValueMap[
					Function[{vName, val},
						With[{id = SelectFirst[varIds, Function[k, nameToKey[varContext[k]["Name"]] === vName], None]},
							If[ id =!= None && IntegerQ[val],
								With[{dom = numberDomainExtended[environment, varContext, varContext[id]["Type"]]},
									If[ dom === NonNegativeIntegers && val >= 0,
										AppendTo[results, <|
											"Scope" -> "Local",
											"CoreAssumption" -> coreNegation[environment, coreEquality[coreNaturals[], freeVariable[id], naturalLiteral[val], {1}]],
											"Method" -> "CounterexampleRefinement"
										|>];
										AppendTo[results, <|
											"Scope" -> "Local",
											"CoreAssumption" -> coreNaturalLessEqual[naturalLiteral[val + 1], freeVariable[id]],
											"Method" -> "CounterexampleRefinement"
										|>]
									];
									If[ dom === Integers,
										AppendTo[results, <|
											"Scope" -> "Local",
											"CoreAssumption" -> coreNegation[environment, coreEquality[coreIntegers[], freeVariable[id], coreIntegerLiteral[val], {1}]],
											"Method" -> "CounterexampleRefinement"
										|>];
										AppendTo[results, <|
											"Scope" -> "Local",
											"CoreAssumption" -> coreIntegerLessEqual[coreIntegerLiteral[val + 1], freeVariable[id]],
											"Method" -> "CounterexampleRefinement"
										|>]
									]
								]
							]
						]
					],
					ceAssoc
				];
				results
			]
		]
	]
]


(* --- Assumption Engine E5: Algebraic Property Catalog Abduction --- *)
abduceAlgebraicProperties[environment_, coreStmt_, uParams_List] := Module[
	{mentioned, opAxioms, singletons = {}, pairs = {}, workingSingletons},
	mentioned = DeleteDuplicates[Cases[coreStmt, constantReference[name_, _] :> name, {0, Infinity}]];
	opAxioms = Select[mentioned, Function[name,
		With[{rec = constantRecord[environment, name]},
			rec["Kind"] === "Axiom" && ! MemberQ[$standardAxiomNames, name] && ! MatchQ[weakHeadNormalForm[environment, <||>, rec["Type"]], _universeSort]
		]
	]];
	If[ opAxioms === {},
		{},

		singletons = Catenate[algebraicPropertiesForConstant[environment, #] & /@ opAxioms];
		(* Check if any singleton already proves coreStmt; if not, also generate pairs *)
		workingSingletons = Select[singletons, Function[cand,
			! FailureQ[enhancedProveCore[environment, coreImplication[cand["CoreAssumption"], coreStmt], uParams, budgetScaled[0.8]]]
		]];
		If[ workingSingletons =!= {},
			workingSingletons,

			pairs = If[ Length[singletons] >= 2,
				Function[pair,
					<|
						"Scope" -> "Global",
						"CoreAssumption" -> coreConjunction[First[pair]["CoreAssumption"], Last[pair]["CoreAssumption"]],
						"Method" -> "AlgebraicCatalog"
					|>
				] /@ Take[Subsets[singletons, {2}], UpTo[15]],
				{}
			];
			Join[singletons, pairs]
		]
	]
]

algebraicPropertiesForConstant[environment_, name_HoldComplete] := Module[{type = weakHeadNormalForm[environment, <||>, constantRecord[environment, name]["Type"]], fRef = coreConstant[name]},
	Which[
		(* Unary operation f : T -> T *)
		MatchQ[type, dependentFunctionType[_, t_, t_, _] /; looseBoundRange[t] == 0],
			With[{t = First[Rest[type]], x = freshFreeVariable[], y = freshFreeVariable[]},
				{ctx1 = extendContext[<||>, x, HoldComplete["x"], t, "Explicit"]},
				{ctx2 = extendContext[ctx1, y, HoldComplete["y"], t, "Explicit"]},
				{fx = Construct[application, fRef, freeVariable[x]], fy = Construct[application, fRef, freeVariable[y]]},
				{ffx = Construct[application, fRef, fx]},
				{
					(* Identity: ForAll[x, f[x] == x] *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, fx, freeVariable[x], {1}]], "Method" -> "AlgebraicCatalog"|>,
					(* Involution: ForAll[x, f[f[x]] == x] *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, ffx, freeVariable[x], {1}]], "Method" -> "AlgebraicCatalog"|>,
					(* Idempotent: ForAll[x, f[f[x]] == f[x]] *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, ffx, fx, {1}]], "Method" -> "AlgebraicCatalog"|>,
					(* Injective: ForAll[x, y, f[x] == f[y] => x == y] *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx2, {x, y}, coreImplication[coreEquality[t, fx, fy, {1}], coreEquality[t, freeVariable[x], freeVariable[y], {1}]]], "Method" -> "AlgebraicCatalog"|>
				}
			],

		(* Binary operation f : T -> T -> T *)
		MatchQ[type, dependentFunctionType[_, t_, dependentFunctionType[_, t_, t_, _], _] /; looseBoundRange[t] == 0],
			With[{t = First[Rest[type]], x = freshFreeVariable[], y = freshFreeVariable[], z = freshFreeVariable[]},
				{ctx1 = extendContext[<||>, x, HoldComplete["x"], t, "Explicit"]},
				{ctx2 = extendContext[ctx1, y, HoldComplete["y"], t, "Explicit"]},
				{ctx3 = extendContext[ctx2, z, HoldComplete["z"], t, "Explicit"]},
				{
					fxy = makeApplication[fRef, {freeVariable[x], freeVariable[y]}],
					fyx = makeApplication[fRef, {freeVariable[y], freeVariable[x]}],
					fxx = makeApplication[fRef, {freeVariable[x], freeVariable[x]}],
					fxyzL = makeApplication[fRef, {makeApplication[fRef, {freeVariable[x], freeVariable[y]}], freeVariable[z]}],
					fxyzR = makeApplication[fRef, {freeVariable[x], makeApplication[fRef, {freeVariable[y], freeVariable[z]}]}]
				},
				{
					(* Commutative *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx2, {x, y}, coreEquality[t, fxy, fyx, {1}]], "Method" -> "AlgebraicCatalog"|>,
					(* Associative *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx3, {x, y, z}, coreEquality[t, fxyzL, fxyzR, {1}]], "Method" -> "AlgebraicCatalog"|>,
					(* Idempotent *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, fxx, freeVariable[x], {1}]], "Method" -> "AlgebraicCatalog"|>
				}
			],

		(* Binary relation R : T -> T -> Prop *)
		MatchQ[type, dependentFunctionType[_, t_, dependentFunctionType[_, t_, universeSort[0], _], _] /; looseBoundRange[t] == 0],
			With[{t = First[Rest[type]], x = freshFreeVariable[], y = freshFreeVariable[], z = freshFreeVariable[]},
				{ctx1 = extendContext[<||>, x, HoldComplete["x"], t, "Explicit"]},
				{ctx2 = extendContext[ctx1, y, HoldComplete["y"], t, "Explicit"]},
				{ctx3 = extendContext[ctx2, z, HoldComplete["z"], t, "Explicit"]},
				{
					rxx = makeApplication[fRef, {freeVariable[x], freeVariable[x]}],
					rxy = makeApplication[fRef, {freeVariable[x], freeVariable[y]}],
					ryx = makeApplication[fRef, {freeVariable[y], freeVariable[x]}],
					ryz = makeApplication[fRef, {freeVariable[y], freeVariable[z]}],
					rxz = makeApplication[fRef, {freeVariable[x], freeVariable[z]}]
				},
				{
					(* Reflexive *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx1, {x}, rxx], "Method" -> "AlgebraicCatalog"|>,
					(* Symmetric *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx2, {x, y}, coreImplication[rxy, ryx]], "Method" -> "AlgebraicCatalog"|>,
					(* Transitive *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx3, {x, y, z}, coreImplication[rxy, coreImplication[ryz, rxz]]], "Method" -> "AlgebraicCatalog"|>,
					(* Antisymmetric *)
					<|"Scope" -> "Global", "CoreAssumption" -> makeDependentFunctionType[ctx2, {x, y}, coreImplication[rxy, coreImplication[ryx, coreEquality[t, freeVariable[x], freeVariable[y], {1}]]]], "Method" -> "AlgebraicCatalog"|>
				}
			],

		True,
			{}
	]
]


(* ::Section:: *)
(*Superfunction 3: TypeTheoryConsequences*)


TypeTheoryConsequences[proposition_, opts : OptionsPattern[]] /; statementQ[Unevaluated[proposition]] :=
	catchKernelFailure @ findConsequences[HoldComplete[proposition], Automatic, Hold[opts]]

TypeTheoryConsequences[proposition_, environment : Except[_Rule | _RuleDelayed], opts : OptionsPattern[]] /; statementQ[Unevaluated[proposition]] :=
	catchKernelFailure @ findConsequences[HoldComplete[proposition], environment, Hold[opts]]


SetAttributes[findConsequences, HoldFirst]
findConsequences[HoldComplete[proposition_], environmentSpec_, Hold[opts___]] := Module[
	{resolved, environment, coreStmt, uParams, methodOpt, timeBudget, maxItems, includeEquiv, llmEval, progressOpt,
	 negStmt, refProof, rawCandidates = {}, deduped, totalCands, verified = {}, pruned},
	resolved = resolveProposition[proposition, environmentSpec];
	If[ FailureQ[resolved],
		resolved,

		environment = resolved["Environment"];
		coreStmt = resolved["CoreStatement"];
		uParams = resolved["UniverseParameters"];
		methodOpt = OptionValue[TypeTheoryConsequences, {opts}, Method];
		timeBudget = Replace[OptionValue[TypeTheoryConsequences, {opts}, TimeConstraint], Except[_?Positive] -> 15];
		maxItems = Replace[OptionValue[TypeTheoryConsequences, {opts}, MaxItems], Except[_Integer?Positive] -> 8];
		includeEquiv = TrueQ[OptionValue[TypeTheoryConsequences, {opts}, "IncludeEquivalents"]];
		llmEval = OptionValue[TypeTheoryConsequences, {opts}, "LLMEvaluator"];
		progressOpt = OptionValue[TypeTheoryConsequences, {opts}, ProgressReporting];

		withSuperfunctionProgress["TypeTheoryConsequences", progressOpt, timeBudget,
			(* Special case: Inconsistency short-circuit *)
			reportProgress["Checking proposition consistency...", 0.08];
			negStmt = coreNegation[environment, coreStmt];
			refProof = enhancedProveCore[environment, negStmt, uParams, remainingBudget[Min[2.0, timeBudget / 5]]];
			If[ ! FailureQ[refProof],
				{<|
					"Consequence" -> coreToTypeTheoryTerm[environment, <||>, coreFalse[]],
					"Statement" -> coreToTypeTheoryTerm[environment, <||>, coreImplication[coreStmt, coreFalse[]]],
					"Proof" -> refProof,
					"Inconsistent" -> True,
					"Method" -> "InconsistencyShortCircuit",
					"Verified" -> True
				|>},

				(* Gather candidate consequences from heuristic engines *)
				If[ useHeuristicQ[methodOpt] && ! deadlineExceededQ[],
					reportProgress["Generating structural and forward-chaining consequences...", 0.22];
					rawCandidates = Join[
						rawCandidates,
						deriveStructuralConsequences[environment, coreStmt, uParams],
						deriveLemmaForwardConsequences[environment, coreStmt, uParams]
					];
					If[ ! deadlineExceededQ[],
						reportProgress["Running symbolic projection and equational discovery...", 0.38];
						rawCandidates = Join[
							rawCandidates,
							deriveSymbolicProjections[environment, coreStmt, uParams],
							deriveEquationalConsequences[environment, coreStmt, uParams]
						]
					]
				];

				If[ useLLMQ[methodOpt],
					reportProgress["Querying LLMFunction for candidate consequences...", 0.48];
					rawCandidates = Join[rawCandidates, deriveConsequencesViaLLM[environment, coreStmt, uParams, llmEval, remainingBudget[timeBudget]]]
				];

				(* Gates 1-4: Kernel proof, proof-term relevance, non-background novelty, non-triviality *)
				deduped = SortBy[DeleteDuplicatesBy[rawCandidates, #["CoreConsequence"] &], coreComplexity[#["CoreConsequence"]] &];
				totalCands = Length[deduped];
				MapIndexed[
					Function[{cand, idx},
						If[ ! deadlineExceededQ[] || verified === {},
							reportProgress[
								"Verifying consequence candidate " <> IntegerString[First[idx]] <> "/" <> IntegerString[totalCands] <> " in kernel...",
								0.52 + 0.38 * (First[idx] / Max[1, totalCands])
							];
							With[{res = verifyAndFilterConsequence[environment, coreStmt, uParams, cand, includeEquiv]},
								If[ res =!= None,
									AppendTo[verified, res]
								]
							]
						]
					],
					deduped
				];

				(* Gate 5: Subsumption pruning (Hasse frontier) *)
				reportProgress["Pruning subsumed consequences...", 0.95];
				pruned = pruneSubsumedConsequences[environment, uParams, verified];
				Take[pruned, UpTo[maxItems]]
			]
		]
	]
]


(* Gates 1-4 for a single consequence candidate C *)
verifyAndFilterConsequence[environment_, coreP_, uParams_List, cand_Association, includeEquiv_] := Module[
	{coreC = cand["CoreConsequence"], method = cand["Method"], implCore, proof, proofTerm, isRelevant, bgProved, isTrivial},
	If[ coreC === coreTrue[] || coreC === coreFalse[],
		None,

		(* Gate 4a: Syntactic triviality filter *)
		isTrivial = Or[
			TrueQ[Quiet @ withKernelCaches[definitionallyEqualQ[environment, <||>, coreC, coreP]]],
			MatchQ[coreC, application[application[constantReference[HoldComplete[Or], _], p_], _] /; p === coreP],
			MatchQ[coreC, application[application[constantReference[HoldComplete[Or], _], _], p_] /; p === coreP],
			MatchQ[coreC, application[application[constantReference[HoldComplete[And], _], p_], p_] /; p === coreP],
			MatchQ[coreC, dependentFunctionType[_, _, p_, _] /; looseBoundRange[p] == 0 && p === coreP],
			MatchQ[coreC, application[constantReference[HoldComplete[Not], _], application[constantReference[HoldComplete[Not], _], p_]] /; p === coreP]
		];
		If[ isTrivial,
			None,

			(* Gate 3: Non-background novelty (reject if provable without P) *)
			bgProved = ! FailureQ[enhancedProveCore[environment, coreC, uParams, 0.35]];
			If[ bgProved,
				None,

				(* Gate 1: Kernel-checked derivation P => C *)
				implCore = coreImplication[coreP, coreC];
				proof = enhancedProveCore[environment, implCore, uParams, remainingBudget[5.0]];
				If[ FailureQ[proof],
					None,

					(* Gate 2: Exact proof-term relevance — bound variable h : P must occur free in normalized proof body! *)
					proofTerm = Quiet @ catchKernelFailure[betaNormalize[completedProofTerm[proof]]];
					isRelevant = MatchQ[proofTerm, lambdaAbstraction[_, _, body_, _] /; boundVariableOccursQ[body, 0]];
					If[ ! isRelevant,
						None,

						(* Optional equivalence filter *)
						If[ ! includeEquiv && coreComplexity[coreC] >= coreComplexity[coreP] &&
							! FailureQ[enhancedProveCore[environment, coreImplication[coreC, coreP], uParams, 0.35]],
							None,

							<|
								"Consequence" -> coreToTypeTheoryTerm[environment, <||>, coreC],
								"Statement" -> coreToTypeTheoryTerm[environment, <||>, implCore],
								"Proof" -> proof,
								"Inconsistent" -> False,
								"Method" -> method,
								"Verified" -> True,
								"CoreConsequence" -> coreC,
								"Complexity" -> coreComplexity[coreC]
							|>
						]
					]
				]
			]
		]
	]
]


(* Gate 5: Subsumption pruning (Hasse frontier keeping strongest concise consequences) *)
pruneSubsumedConsequences[environment_, uParams_List, items_List] := Module[{n = Length[items], impliesMat, dedup, survivors},
	If[ n <= 1,
		KeyDrop[#, {"CoreConsequence", "Complexity"}] & /@ items,

		impliesMat = Table[
			If[ i === j,
				True,
				With[
					{
						cI = First[Drop[items, i - 1]]["CoreConsequence"],
						cJ = First[Drop[items, j - 1]]["CoreConsequence"]
					},
					! FailureQ[enhancedProveCore[environment, coreImplication[cI, cJ], uParams, 0.35]]
				]
			],
			{i, n},
			{j, n}
		];
		(* Deduplicate mutually equivalent consequences, keeping simplest *)
		dedup = Fold[
			Function[{chosen, idx},
				With[
					{
						eqIdx = SelectFirst[chosen, Function[c,
							First[Drop[First[Drop[impliesMat, idx - 1]], c - 1]] &&
							First[Drop[First[Drop[impliesMat, c - 1]], idx - 1]]
						], None]
					},
					If[ eqIdx === None,
						Append[chosen, idx],
						If[ First[Drop[items, idx - 1]]["Complexity"] < First[Drop[items, eqIdx - 1]]["Complexity"],
							Append[DeleteCases[chosen, eqIdx], idx],
							chosen
						]
					]
				]
			],
			{},
			Range[n]
		];
		(* Drop C_j if some other C_i strictly implies C_j and is not significantly larger *)
		survivors = Select[dedup, Function[j,
			! AnyTrue[dedup, Function[i,
				i =!= j &&
				First[Drop[First[Drop[impliesMat, i - 1]], j - 1]] &&
				! First[Drop[First[Drop[impliesMat, j - 1]], i - 1]] &&
				First[Drop[items, i - 1]]["Complexity"] <= First[Drop[items, j - 1]]["Complexity"] + 4
			]]
		]];
		(* simplest first, a tie to the earlier candidate rather than to the order of the whole items, which name
		   environment stores by session counters *)
		KeyDrop[#, {"CoreConsequence", "Complexity"}] & /@ Map[
			Function[idx, First[Drop[items, idx - 1]]],
			SortBy[survivors, Function[idx, {First[Drop[items, idx - 1]]["Complexity"], idx}]]
		]
	]
]


(* --- Consequence Engine F1: Structural Decomposition & Canonical Specialization --- *)
deriveStructuralConsequences[environment_, coreP_, uParams_List] := Module[{whnf = weakHeadNormalForm[environment, <||>, coreP], results = {}},
	(* Conjunction projections *)
	If[ MatchQ[whnf, application[application[constantReference[HoldComplete[And], _], _], _]],
		results = Join[results, Function[c, <|"CoreConsequence" -> c, "Method" -> "StructuralDecomposition"|>] /@ flattenConjunctions[whnf]]
	];

	(* Equivalence projections *)
	If[ MatchQ[whnf, application[application[constantReference[HoldComplete[Equivalent], _], _], _]],
		With[{a = Last[First[whnf]], b = Last[whnf]},
			results = Join[results, {
				<|"CoreConsequence" -> coreImplication[a, b], "Method" -> "StructuralDecomposition"|>,
				<|"CoreConsequence" -> coreImplication[b, a], "Method" -> "StructuralDecomposition"|>
			}]
		]
	];

	(* Canonical specialization of universal statements over N / Booleans *)
	If[ MatchQ[whnf, dependentFunctionType[_, dom_, _, _] /; ! TrueQ[Quiet @ propositionQ[environment, <||>, dom]]],
		With[{dom = First[Rest[whnf]], cod = First[Drop[whnf, 2]]},
			With[{canonVals = Which[
				dom === coreNaturals[], {naturalLiteral[0], naturalLiteral[1]},
				dom === coreBooleans[], {coreConstant[HoldComplete["false"]], coreConstant[HoldComplete["true"]]},
				integerTypeQ[environment, dom], {coreIntegerLiteral[0], coreIntegerLiteral[1]},
				True, {}
			]},
				results = Join[results, Function[v,
					<|"CoreConsequence" -> betaNormalize[instantiateBoundVariable[cod, v]], "Method" -> "CanonicalSpecialization"|>
				] /@ canonVals]
			];
			(* Diagonal specialization ForAll[x, y, Q[x, y]] -> ForAll[x, Q[x, x]] *)
			If[ MatchQ[cod, dependentFunctionType[_, d2_, _, _] /; d2 === dom],
				With[{xId = freshFreeVariable[]},
					{ctx = extendContext[<||>, xId, HoldComplete["x"], dom, "Explicit"]},
					{diagBody = betaNormalize[instantiateBoundVariable[instantiateBoundVariable[First[Drop[cod, 2]], freeVariable[xId]], freeVariable[xId]]]},
					AppendTo[results, <|"CoreConsequence" -> makeDependentFunctionType[ctx, {xId}, diagBody], "Method" -> "DiagonalSpecialization"|>]
				]
			]
		]
	];

	(* Existential conjunction projections *)
	If[ MatchQ[whnf, application[application[constantReference[HoldComplete[Exists], _], _], lambdaAbstraction[_, _, application[application[constantReference[HoldComplete[And], _], _], _], _]]],
		With[{type = Last[First[whnf]], lam = Last[whnf]},
			{name = First[lam], andBody = First[Drop[lam, 2]]},
			{a = Last[First[andBody]], b = Last[andBody]},
			results = Join[results, {
				<|"CoreConsequence" -> coreExists[type, name, a, Last[First[First[whnf]]]], "Method" -> "StructuralDecomposition"|>,
				<|"CoreConsequence" -> coreExists[type, name, b, Last[First[First[whnf]]]], "Method" -> "StructuralDecomposition"|>
			}]
		]
	];

	results
]


(* --- Consequence Engine F2: Environment Lemma Forward-Chaining & Classical Corollaries --- *)
deriveLemmaForwardConsequences[environment_, coreP_, uParams_List] := Module[{results = {}, conjuncts},
	(* Classical corollaries if coreP is ExcludedMiddle in a constructive environment *)
	If[ excludedMiddleTypeQ[environment, <||>, coreP],
		With[{pId = freshFreeVariable[], qId = freshFreeVariable[]},
			{ctxP = extendContext[<||>, pId, HoldComplete["p"], universeSort[0], "Explicit"]},
			{ctxPQ = extendContext[ctxP, qId, HoldComplete["q"], universeSort[0], "Explicit"]},
			{p = freeVariable[pId], q = freeVariable[qId]},
			results = Join[results, {
				(* Double Negation Elimination: ForAll[p, Not[Not[p]] => p] *)
				<|"CoreConsequence" -> makeDependentFunctionType[ctxP, {pId}, coreImplication[coreNegation[environment, coreNegation[environment, p]], p]], "Method" -> "ClassicalCorollary"|>,
				(* Peirce's Law: ForAll[p, q, ((p => q) => p) => p] *)
				<|"CoreConsequence" -> makeDependentFunctionType[ctxPQ, {pId, qId}, coreImplication[coreImplication[coreImplication[p, q], p], p]], "Method" -> "ClassicalCorollary"|>,
				(* Contraposition: ForAll[p, q, (Not[q] => Not[p]) => (p => q)] *)
				<|"CoreConsequence" -> makeDependentFunctionType[ctxPQ, {pId, qId}, coreImplication[coreImplication[coreNegation[environment, q], coreNegation[environment, p]], coreImplication[p, q]]], "Method" -> "ClassicalCorollary"|>
			}]
		]
	];

	(* Direct forward rules on equations & inequalities *)
	conjuncts = flattenConjunctions[weakHeadNormalForm[environment, <||>, coreP]];

	(* Symmetry of equality a == b -> b == a; successor injectivity a + 1 == b + 1 -> a == b; addition cancellation a + c == b + c -> a == b *)
	Scan[
		Function[c,
			Replace[weakHeadNormalForm[environment, <||>, c], {
				application[application[application[constantReference[HoldComplete[Equal], levels_], type_], l_], r_] :> (
					If[ naturalNumberTypeQ[environment, <||>, type],
						Replace[{l, r}, {
							{application[application[constantReference[HoldComplete[Plus], _], a_], k_], application[application[constantReference[HoldComplete[Plus], _], b_], k_]} :>
								AppendTo[results, <|"CoreConsequence" -> coreEquality[type, a, b, levels], "Method" -> "LemmaForwardChaining"|>],
							{application[application[constantReference[HoldComplete[Plus], _], k_], a_], application[application[constantReference[HoldComplete[Plus], _], k_], b_]} :>
								AppendTo[results, <|"CoreConsequence" -> coreEquality[type, a, b, levels], "Method" -> "LemmaForwardChaining"|>],
							{application[constantReference[HoldComplete["successor"], _], a_], application[constantReference[HoldComplete["successor"], _], b_]} :>
								AppendTo[results, <|"CoreConsequence" -> coreEquality[type, a, b, levels], "Method" -> "LemmaForwardChaining"|>]
						}]
					]
				)
			}]
		],
		conjuncts
	];

	(* Antisymmetry & transitivity across pairs of order conjuncts *)
	If[ Length[conjuncts] >= 2,
		Scan[
			Function[pair,
				With[{c1 = weakHeadNormalForm[environment, <||>, First[pair]], c2 = weakHeadNormalForm[environment, <||>, Last[pair]]},
					Replace[{c1, c2}, {
						{application[application[constantReference[HoldComplete[LessEqual], _], a_], b_], application[application[constantReference[HoldComplete[LessEqual], _], b_], a_]} :>
							AppendTo[results, <|"CoreConsequence" -> coreEquality[coreNaturals[], a, b, {1}], "Method" -> "LemmaForwardChaining"|>],
						{application[application[constantReference[HoldComplete[LessEqual], _], a_], b_], application[application[constantReference[HoldComplete[LessEqual], _], b_], d_]} :>
							AppendTo[results, <|"CoreConsequence" -> coreNaturalLessEqual[a, d], "Method" -> "LemmaForwardChaining"|>],
						{application[application[constantReference[HoldComplete[LessEqual], _], b_], d_], application[application[constantReference[HoldComplete[LessEqual], _], a_], b_]} :>
							AppendTo[results, <|"CoreConsequence" -> coreNaturalLessEqual[a, d], "Method" -> "LemmaForwardChaining"|>]
					}]
				]
			],
			Subsets[conjuncts, {2}]
		]
	];

	results
]


(* --- Consequence Engine F3: Symbolic Projection & Quantifier Elimination --- *)
deriveSymbolicProjections[environment_, coreP_, uParams_List] := Module[
	{mentioned, numConsts, domains, wlVars, varMap, revVarMap, wlCond, domCond, wlDomain, results = {}},
	mentioned = DeleteDuplicates[Cases[coreP, constantReference[name_, _] :> name, {0, Infinity}]];
	numConsts = Select[mentioned, Function[name,
		With[{rec = constantRecord[environment, name]},
			rec["Kind"] === "Axiom" && numberDomainExtended[environment, <||>, rec["Type"]] =!= None
		]
	]];
	If[ numConsts === {},
		{},

		domains = AssociationMap[Function[name, numberDomainExtended[environment, <||>, constantRecord[environment, name]["Type"]]], numConsts];
		wlVars = Table[Subscript[\[FormalX], k], {k, Length[numConsts]}];
		varMap = AssociationThread[numConsts, wlVars];
		revVarMap = AssociationThread[wlVars, numConsts];
		wlCond = corePropToWolfram[environment, <||>, varMap, coreP];
		If[ wlCond === $Failed,
			{},

			domCond = And @@ MapThread[Function[{v, d}, If[d === NonNegativeIntegers, v >= 0, True]], {wlVars, Values[domains]}];
			wlDomain = If[MemberQ[Values[domains], Rationals], Reals, Integers];

			(* 1D projections onto each individual variable: tight upper/lower bounds *)
			Scan[
				Function[v,
					With[{others = DeleteCases[wlVars, v]},
						{
							proj = TimeConstrained[
								Quiet @ If[ others === {},
									Reduce[domCond && wlCond, v, wlDomain],
									Resolve[Exists[Evaluate[others], domCond && wlCond], Reals]
								],
								2,
								$Aborted
							]
						},
						If[ proj =!= $Aborted && proj =!= True && proj =!= False,
							results = Join[results, extractBoundProjections[environment, revVarMap, domains, v, proj]]
						]
					]
				],
				wlVars
			];

			(* 2D projections onto pairs when >= 3 variables (discovers transitive bounds like a + 2 <= c) *)
			If[ Length[wlVars] >= 3 && Length[wlVars] <= 5,
				Scan[
					Function[pair,
						With[{others = Complement[wlVars, pair]},
							{
								proj = TimeConstrained[
									Quiet @ Reduce[Resolve[Exists[Evaluate[others], domCond && wlCond], Integers], pair, Integers],
									2,
									$Aborted
								]
							},
							If[ proj =!= $Aborted && proj =!= True && proj =!= False && ! MatchQ[proj, _Reduce | _Resolve],
								With[{cleaned = stripDomainGuards[proj, wlVars, Values[domains]]},
									Scan[
										Function[atom,
											With[{coreC = wolframCondToCore[environment, <||>, revVarMap, domains, atom]},
												If[ coreC =!= $Failed,
													AppendTo[results, <|"CoreConsequence" -> coreC, "Method" -> "SymbolicProjection"|>]
												]
											]
										],
										extractAtomicInequalities[cleaned]
									]
								]
							]
						]
					],
					Subsets[wlVars, {2}]
				]
			];

			results
		]
	]
]

extractBoundProjections[environment_, revVarMap_, domains_, v_, proj_] := Module[{cleaned, atoms, upper, lower, cands = {}},
	cleaned = stripDomainGuards[proj, Keys[revVarMap], Values[domains]];
	atoms = extractAtomicInequalities[cleaned];
	(* Also check exact numeric ceiling/floor bounds for integers/naturals *)
	upper = TimeConstrained[Quiet @ MaxValue[{v, proj}, v], 1, $Aborted];
	lower = TimeConstrained[Quiet @ MinValue[{v, proj}, v], 1, $Aborted];
	If[ NumericQ[upper] && upper < Infinity,
		With[{uInt = Floor[upper]},
			If[IntegerQ[uInt], AppendTo[atoms, v <= uInt]]
		]
	];
	If[ NumericQ[lower] && lower > -Infinity,
		With[{lInt = Ceiling[lower]},
			If[IntegerQ[lInt] && (domains[revVarMap[v]] =!= NonNegativeIntegers || lInt > 0), AppendTo[atoms, lInt <= v]]
		]
	];
	DeleteCases[
		Function[a,
			With[{coreC = wolframCondToCore[environment, <||>, revVarMap, domains, a]},
				If[coreC === $Failed, None, <|"CoreConsequence" -> coreC, "Method" -> "SymbolicProjection"|>]
			]
		] /@ DeleteDuplicates[atoms],
		None
	]
]

extractAtomicInequalities[And[parts__]] := Catenate[extractAtomicInequalities /@ {parts}]
extractAtomicInequalities[Inequality[lo_, LessEqual, v_, LessEqual, hi_]] := {lo <= v, v <= hi}
extractAtomicInequalities[Inequality[lo_, Less, v_, LessEqual, hi_]] := {lo < v, v <= hi}
extractAtomicInequalities[Inequality[lo_, LessEqual, v_, Less, hi_]] := {lo <= v, v < hi}
extractAtomicInequalities[Inequality[lo_, Less, v_, Less, hi_]] := {lo < v, v < hi}
extractAtomicInequalities[atom : (_LessEqual | _Less | _GreaterEqual | _Greater | _Equal | _Unequal)] := {atom}
extractAtomicInequalities[_] := {}


(* --- Consequence Engine F4: Equational & Algebraic Property Discovery --- *)
deriveEquationalConsequences[environment_, coreP_, uParams_List] := Module[
	{mentioned, ops, results = {}},
	mentioned = DeleteDuplicates[Cases[coreP, constantReference[name_, _] :> name, {0, Infinity}]];
	ops = Select[mentioned, Function[name,
		With[{rec = constantRecord[environment, name]},
			rec["Kind"] === "Axiom" && ! MemberQ[$standardAxiomNames, name] && ! MatchQ[weakHeadNormalForm[environment, <||>, rec["Type"]], _universeSort]
		]
	]];
	(* Unary functions f : T -> T *)
	Scan[
		Function[name,
			With[{type = weakHeadNormalForm[environment, <||>, constantRecord[environment, name]["Type"]], fRef = coreConstant[name]},
				If[ MatchQ[type, dependentFunctionType[_, t_, t_, _] /; looseBoundRange[t] == 0],
					With[{t = First[Rest[type]], x = freshFreeVariable[], y = freshFreeVariable[]},
						{ctx1 = extendContext[<||>, x, HoldComplete["x"], t, "Explicit"]},
						{ctx2 = extendContext[ctx1, y, HoldComplete["y"], t, "Explicit"]},
						{
							fx = Construct[application, fRef, freeVariable[x]],
							fy = Construct[application, fRef, freeVariable[y]]
						},
						{ffx = Construct[application, fRef, fx]},
						{fffx = Construct[application, fRef, ffx]},
						results = Join[results, {
							(* Injective: ForAll[x, y, f[x] == f[y] => x == y] *)
							<|"CoreConsequence" -> makeDependentFunctionType[ctx2, {x, y}, coreImplication[coreEquality[t, fx, fy, {1}], coreEquality[t, freeVariable[x], freeVariable[y], {1}]]], "Method" -> "EquationalDiscovery"|>,
							(* Surjective: ForAll[y, Exists[x, f[x] == y]] *)
							<|"CoreConsequence" -> makeDependentFunctionType[extendContext[<||>, y, HoldComplete["y"], t, "Explicit"], {y},
								coreExists[t, HoldComplete["x"], abstractFreeVariable[coreEquality[t, fx, freeVariable[y], {1}], x], {1}]
							], "Method" -> "EquationalDiscovery"|>,
							(* f[f[f[x]]] == f[x] *)
							<|"CoreConsequence" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, fffx, fx, {1}]], "Method" -> "EquationalDiscovery"|>,
							(* f[f[x]] == f[x] *)
							<|"CoreConsequence" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, ffx, fx, {1}]], "Method" -> "EquationalDiscovery"|>
						}]
					]
				]
			]
		],
		ops
	];

	(* Binary operations f : T -> T -> T paired with constants e : T and unary inv : T -> T *)
	With[
		{
			binOps = Select[ops, Function[n, MatchQ[weakHeadNormalForm[environment, <||>, constantRecord[environment, n]["Type"]], dependentFunctionType[_, t_, dependentFunctionType[_, t_, t_, _], _] /; looseBoundRange[t] == 0]]],
			unOps = Select[ops, Function[n, MatchQ[weakHeadNormalForm[environment, <||>, constantRecord[environment, n]["Type"]], dependentFunctionType[_, t_, t_, _] /; looseBoundRange[t] == 0]]],
			consts = Select[ops, Function[n, ! MatchQ[weakHeadNormalForm[environment, <||>, constantRecord[environment, n]["Type"]], _dependentFunctionType | _universeSort]]]
		},
		Scan[
			Function[binName,
				With[{t = First[Rest[weakHeadNormalForm[environment, <||>, constantRecord[environment, binName]["Type"]]]], fRef = coreConstant[binName]},
					{
						sameConsts = Select[consts, Function[c, weakHeadNormalForm[environment, <||>, constantRecord[environment, c]["Type"]] === t]],
						sameUnOps = Select[unOps, Function[u, First[Rest[weakHeadNormalForm[environment, <||>, constantRecord[environment, u]["Type"]]]] === t]],
						x = freshFreeVariable[], y = freshFreeVariable[], a = freshFreeVariable[]
					},
					{ctx1 = extendContext[<||>, x, HoldComplete["x"], t, "Explicit"]},
					{ctx3 = extendContext[extendContext[ctx1, y, HoldComplete["y"], t, "Explicit"], a, HoldComplete["a"], t, "Explicit"]},
					(* Left & right cancellation *)
					results = Join[results, {
						<|"CoreConsequence" -> makeDependentFunctionType[ctx3, {a, x, y}, coreImplication[
							coreEquality[t, makeApplication[fRef, {freeVariable[a], freeVariable[x]}], makeApplication[fRef, {freeVariable[a], freeVariable[y]}], {1}],
							coreEquality[t, freeVariable[x], freeVariable[y], {1}]
						]], "Method" -> "EquationalDiscovery"|>,
						<|"CoreConsequence" -> makeDependentFunctionType[ctx3, {a, x, y}, coreImplication[
							coreEquality[t, makeApplication[fRef, {freeVariable[x], freeVariable[a]}], makeApplication[fRef, {freeVariable[y], freeVariable[a]}], {1}],
							coreEquality[t, freeVariable[x], freeVariable[y], {1}]
						]], "Method" -> "EquationalDiscovery"|>
					}];
					(* Identity and inverse laws *)
					Scan[
						Function[eName,
							With[{eRef = coreConstant[eName]},
								results = Join[results, {
									<|"CoreConsequence" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, makeApplication[fRef, {freeVariable[x], eRef}], freeVariable[x], {1}]], "Method" -> "EquationalDiscovery"|>,
									<|"CoreConsequence" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, makeApplication[fRef, {eRef, freeVariable[x]}], freeVariable[x], {1}]], "Method" -> "EquationalDiscovery"|>
								}];
								Scan[
									Function[invName,
										With[{invRef = coreConstant[invName]},
											results = Join[results, {
												<|"CoreConsequence" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, makeApplication[fRef, {freeVariable[x], Construct[application, invRef, freeVariable[x]]}], eRef, {1}]], "Method" -> "EquationalDiscovery"|>,
												<|"CoreConsequence" -> makeDependentFunctionType[ctx1, {x}, coreEquality[t, Construct[application, invRef, Construct[application, invRef, freeVariable[x]]], freeVariable[x], {1}]], "Method" -> "EquationalDiscovery"|>,
												<|"CoreConsequence" -> coreEquality[t, Construct[application, invRef, eRef], eRef, {1}], "Method" -> "EquationalDiscovery"|>
											}]
										]
									],
									sameUnOps
								]
							]
						],
						sameConsts
					]
				]
			],
			binOps
		]
	];

	results
]


(* ::Section:: *)
(*Superfunction 4: TypeTheoryTermination*)


(* Form 1: Pointwise termination of an expression under explicit rewrite rules *)
TypeTheoryTermination[expr_, rules_List, opts : OptionsPattern[]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationPointwiseRules[HoldComplete[expr], HoldComplete[rules], Automatic, Hold[opts]]]

TypeTheoryTermination[expr_, rules_List, environment : Except[_Rule | _RuleDelayed], opts : OptionsPattern[]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationPointwiseRules[HoldComplete[expr], HoldComplete[rules], environment, Hold[opts]]]

(* Form 2: Global termination of an explicit rewrite rule list *)
TypeTheoryTermination[rules : {(_Rule | _RuleDelayed) ..}, opts : OptionsPattern[]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationGlobalRules[HoldComplete[rules], Automatic, Hold[opts]]]

TypeTheoryTermination[rules : {(_Rule | _RuleDelayed) ..}, environment : Except[_Rule | _RuleDelayed], opts : OptionsPattern[]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationGlobalRules[HoldComplete[rules], environment, Hold[opts]]]

(* Form 3: Termination of a Wolfram Language symbol (DownValues / While / recursive function) *)
TypeTheoryTermination[symbol_Symbol, opts : OptionsPattern[]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationSymbol[HoldComplete[symbol], Automatic, Hold[opts]]]

TypeTheoryTermination[symbol_Symbol, environment : Except[_Rule | _RuleDelayed], opts : OptionsPattern[]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationSymbol[HoldComplete[symbol], environment, Hold[opts]]]

(* Form 4: Pointwise termination of an expression head[args...] under head's DownValues *)
TypeTheoryTermination[expr : head_Symbol[___], opts : OptionsPattern[]] /; statementQ[Unevaluated[expr]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationPointwiseSymbol[HoldComplete[expr], HoldComplete[head], Automatic, Hold[opts]]]

TypeTheoryTermination[expr : head_Symbol[___], environment : Except[_Rule | _RuleDelayed], opts : OptionsPattern[]] /; statementQ[Unevaluated[expr]] :=
	catchKernelFailure @ withTerminationProgress[Hold[opts], terminationPointwiseSymbol[HoldComplete[expr], HoldComplete[head], environment, Hold[opts]]]

SetAttributes[withTerminationProgress, HoldRest]
withTerminationProgress[Hold[opts___], body_] := With[
	{
		progressOpt = OptionValue[TypeTheoryTermination, {opts}, ProgressReporting],
		timeBudget = Replace[OptionValue[TypeTheoryTermination, {opts}, TimeConstraint], Except[_?Positive] -> 15]
	},
	withSuperfunctionProgress["TypeTheoryTermination", progressOpt, timeBudget, body]
]


(* --- Target 4A: Pointwise Termination / Lasso Detection for Explicit Rule Lists --- *)
terminationPointwiseRules[heldExpr_HoldComplete, heldRules_HoldComplete, environmentSpec_, Hold[opts___]] := Module[
	{environment, maxSteps, rulesList, matchFnHeld, rulesEnv, iterEnv, stepHistory, exprCore, curCore, nextCore, visited, cycleStart, k, nfTerm, termStmt, proof},
	environment = If[environmentSpec === Automatic, TypeTheoryEnvironment["Prelude"], resolveEnvironmentArg[environmentSpec]];
	If[ FailureQ[environment],
		environment,

		maxSteps = Replace[OptionValue[TypeTheoryTermination, {opts}, "MaxSteps"], Except[_Integer?Positive] -> 100];
		rulesList = Replace[heldRules, HoldComplete[{rs___}] :> HoldComplete /@ Unevaluated[{rs}]];
		matchFnHeld = Quiet @ catchKernelFailure[rulesMatchFunction[rulesList]];
		If[ ! MatchQ[matchFnHeld, _HoldComplete],
			Failure["UntranslatableRules", <|"MessageTemplate" -> "The rewrite rules could not be formalized.", "MessageParameters" -> {}|>],

			withStoreCleanup[
				With[{rulesDef = Replace[matchFnHeld, HoldComplete[fn_] :> TypeTheoryDefinition["targetRules", Typed[fn, Expressions -> Match[Expressions]]]]},
					rulesEnv = Quiet @ TypeTheoryEnvironment[environment, {rulesDef}];
					If[ FailureQ[rulesEnv],
						rulesEnv,

						(* Formalize the initial expression as a term of Expressions *)
						exprCore = Replace[heldExpr, HoldComplete[e_] :> Quiet @ catchKernelFailure[
							First[elaborateClosedTerm[rulesEnv, HoldComplete[Unevaluated[e]], coreConstant[HoldComplete[Expressions]], {}]]
						]];
						If[ FailureQ[exprCore],
							exprCore,

							(* Simulate ReplaceAll[cur, "targetRules"] step by step using NormalForm *)
							reportProgress["Simulating rewrite steps...", 0.25];
							visited = <||>;
							stepHistory = {};
							curCore = exprCore;
							k = 0;
							cycleStart = None;
							While[ k < maxSteps && ! deadlineExceededQ[],
								If[ KeyExistsQ[visited, curCore],
									cycleStart = visited[curCore];
									Break[]
								];
								visited[curCore] = k;
								AppendTo[stepHistory, curCore];
								nextCore = reduceExpressionStep[rulesEnv, curCore];
								If[ nextCore === $Failed,
									Break[]
								];
								If[ withKernelCaches[definitionallyEqualQ[rulesEnv, <||>, nextCore, curCore]],
									(* Reached fixed point in k steps! *)
									Break[]
								];
								curCore = nextCore;
								k = k + 1
							];

							Which[
								nextCore === $Failed,
									<|"Status" -> "Undetermined", "Target" -> HoldForm @@ heldExpr, "Proof" -> None, "Method" -> "PointwiseRules"|>,

								cycleStart =!= None,
									(* True non-trivial cycle of period >= 2 under ReplaceAll *)
									buildPointwiseRulesLassoResult[rulesEnv, heldExpr, exprCore, stepHistory, cycleStart],

								withKernelCaches[definitionallyEqualQ[rulesEnv, <||>, nextCore, curCore]],
									(* Kernel-certify Exists[{Typed[n, NonNegativeIntegers]}, SameQ[ReplaceAll["replaceRepeatedSteps"[n, "targetRules"][e], "targetRules"], "replaceRepeatedSteps"[n, "targetRules"][e]] == "true"] *)
									buildPointwiseRulesTerminationResult[rulesEnv, heldExpr, exprCore, curCore, k],

								True,
									<|
										"Status" -> "Undetermined",
										"Target" -> HoldForm @@ heldExpr,
										"Proof" -> None,
										"Method" -> "PointwiseRules",
										"Details" -> <|"StepsExplored" -> maxSteps|>
									|>
							]
						]
					]
				]
			]
		]
	]
]

reduceExpressionStep[rulesEnv_, exprCore_] := Module[{stepTerm, nf},
	stepTerm = makeApplication[coreConstant[HoldComplete[ReplaceAll]], {exprCore, coreConstant[HoldComplete["targetRules"]]}];
	nf = Quiet @ catchKernelFailure[NormalForm[coreToTypeTheoryTerm[rulesEnv, <||>, stepTerm]]];
	If[ FailureQ[nf],
		$Failed,
		First[elaborateClosedTerm[rulesEnv, heldTerm[nf], coreConstant[HoldComplete[Expressions]], {}]]
	]
]

buildPointwiseRulesTerminationResult[rulesEnv_, heldExpr_, exprCore_, nfCore_, steps_Integer] := Module[
	{nId, ctx, iterN, eqTerm, exStmt, pred, witnessProof, verified},
	nId = freshFreeVariable[];
	ctx = extendContext[<||>, nId, HoldComplete["n"], coreNaturals[], "Explicit"];
	iterN = Construct[application, makeApplication[coreConstant[HoldComplete["replaceRepeatedSteps"]], {freeVariable[nId], coreConstant[HoldComplete["targetRules"]]}], exprCore];
	eqTerm = coreEquality[
		coreBooleans[],
		makeApplication[coreConstant[HoldComplete[SameQ]], {makeApplication[coreConstant[HoldComplete[ReplaceAll]], {iterN, coreConstant[HoldComplete["targetRules"]]}], iterN}],
		coreConstant[HoldComplete["true"]],
		{1}
	];
	pred = makeLambda[ctx, {nId}, eqTerm];
	exStmt = makeApplication[coreConstant[HoldComplete[Exists], {1}], {coreNaturals[], pred}];
	witnessProof = proveFromCore[rulesEnv, exStmt, {}, {TypeTheoryTactic["Witness", steps]}];
	If[ FailureQ[witnessProof],
		witnessProof = proveFromCore[rulesEnv, exStmt, {}, {TypeTheoryTactic["Witness", steps], TypeTheoryTactic["Reflexivity"]}]
	];
	<|
		"Status" -> If[FailureQ[witnessProof], "Undetermined", "Terminating"],
		"Target" -> HoldForm @@ heldExpr,
		"Steps" -> steps,
		"NormalForm" -> coreToTypeTheoryTerm[rulesEnv, <||>, nfCore],
		"Statement" -> coreToTypeTheoryTerm[rulesEnv, <||>, exStmt],
		"Proof" -> If[FailureQ[witnessProof], None, witnessProof],
		"Method" -> "ConcreteExecution",
		"Verified" -> ! FailureQ[witnessProof]
	|>
]

buildPointwiseRulesLassoResult[rulesEnv_, heldExpr_, exprCore_, stepHistory_List, cycleStart_Integer] := Module[
	{envWithIter, lassoProof, period = Length[stepHistory] - cycleStart},
	(* Define single-step iteration iterReplace[n, e] and prove by induction on n that ReplaceAll[iterReplace[n, e], rules] != iterReplace[n, e] (SameQ == "false") *)
	envWithIter = Quiet @ TypeTheoryEnvironment[rulesEnv, {
		TypeTheoryDefinition["iterateReplaceAll", Typed[
			Function[{Typed[n, NonNegativeIntegers], Typed[e, Expressions]},
				InductiveRecursor[NonNegativeIntegers][
					Typed[k, NonNegativeIntegers] |-> Expressions,
					e,
					{Typed[k, NonNegativeIntegers], Typed[acc, Expressions]} |-> ReplaceAll[acc, "targetRules"],
					n
				]
			],
			NonNegativeIntegers -> Expressions -> Expressions
		]]
	}];
	lassoProof = If[ FailureQ[envWithIter],
		envWithIter,
		buildLassoNonTerminationProof[envWithIter, exprCore, stepHistory, "Rules"]
	];
	<|
		"Status" -> If[FailureQ[lassoProof], "Undetermined", "NonTerminating"],
		"Target" -> HoldForm @@ heldExpr,
		"Cycle" -> <|
			"PrefixLength" -> cycleStart,
			"Period" -> period,
			"States" -> (coreToTypeTheoryTerm[rulesEnv, <||>, #] & /@ Drop[stepHistory, cycleStart])
		|>,
		"Statement" -> If[FailureQ[lassoProof], None, lassoProof["Statement"]],
		"Proof" -> If[FailureQ[lassoProof], None, lassoProof],
		"Method" -> "LassoCycleInduction",
		"Verified" -> ! FailureQ[lassoProof]
	|>
]


(* --- Target 4B: Pointwise Termination / Lasso Proof for Symbol DownValues ("Meaning" -> "Rules") --- *)
terminationPointwiseSymbol[heldExpr_HoldComplete, heldHead : HoldComplete[head_Symbol], environmentSpec_, Hold[opts___]] := Module[
	{environment, maxSteps, rulesDecls, rulesEnv, dvName, iterEnv, exprCore, curCore, nextOpt, visited, stepHistory, k, cycleStart, result},
	environment = If[environmentSpec === Automatic, TypeTheoryEnvironment["Prelude"], resolveEnvironmentArg[environmentSpec]];
	If[ FailureQ[environment],
		environment,

		maxSteps = Replace[OptionValue[TypeTheoryTermination, {opts}, "MaxSteps"], Except[_Integer?Positive] -> 100];
		rulesDecls = Quiet @ catchKernelFailure[TypeTheoryFormalize[head, environment, "Meaning" -> "Rules"]];
		If[ FailureQ[rulesDecls],
			rulesDecls,

			dvName = "DownValues[" <> SymbolName[Unevaluated[head]] <> "]";
			rulesEnv = Quiet @ TypeTheoryEnvironment[environment, rulesDecls];
			If[ FailureQ[rulesEnv],
				rulesEnv,

				(* Add option-step iterator: iterStep[0, e] = some[e], iterStep[k+1, e] = bindOption[iterStep[k, e], dvName] *)
				iterEnv = With[{dv = dvName},
					Quiet @ TypeTheoryEnvironment[rulesEnv, {
						TypeTheoryDefinition["iterateDownValues", Typed[
							Function[{Typed[n, NonNegativeIntegers], Typed[e, Expressions]},
								InductiveRecursor[NonNegativeIntegers][
									Typed[k, NonNegativeIntegers] |-> Option[Expressions],
									"some"[e],
									{Typed[k, NonNegativeIntegers], Typed[acc, Option[Expressions]]} |->
										InductiveRecursor[Option][
											Typed[o, Option[Expressions]] |-> Option[Expressions],
											Typed["none", Option[Expressions]],
											Typed[x, Expressions] |-> dv[x],
											acc
										],
									n
								]
							],
							NonNegativeIntegers -> Expressions -> Option[Expressions]
						]]
					}]
				];
				If[ FailureQ[iterEnv],
					iterEnv,

					exprCore = Replace[heldExpr, HoldComplete[e_] :> Quiet @ catchKernelFailure[
						First[elaborateClosedTerm[iterEnv, HoldComplete[Unevaluated[e]], coreConstant[HoldComplete[Expressions]], {}]]
					]];
					If[ FailureQ[exprCore],
						exprCore,

						visited = <||>;
						stepHistory = {};
						curCore = exprCore;
						k = 0;
						cycleStart = None;
						While[ k < maxSteps,
							If[ KeyExistsQ[visited, curCore],
								cycleStart = visited[curCore];
								Break[]
							];
							If[ LeafCount[curCore] > 2500,
								Break[]
							];
							visited[curCore] = k;
							AppendTo[stepHistory, curCore];
							nextOpt = reduceDownValuesStep[iterEnv, dvName, curCore];
							If[ nextOpt === "None" || nextOpt === $Failed,
								Break[]
							];
							curCore = nextOpt;
							k = k + 1
						];

						Which[
							nextOpt === "None",
								(* Terminates in k steps: iterStep[k + 1, e] == none! *)
								buildDownValuesTerminationResult[iterEnv, heldExpr, exprCore, curCore, k],

							cycleStart =!= None,
								(* Lasso cycle: prove ForAll[n, Not[iterateDownValues[n, e] == none]] by kernel induction! *)
								With[{lassoProof = buildLassoNonTerminationProof[iterEnv, exprCore, stepHistory, "DownValues"]},
									<|
										"Status" -> If[FailureQ[lassoProof], "Undetermined", "NonTerminating"],
										"Target" -> HoldForm @@ heldExpr,
										"Cycle" -> <|
											"PrefixLength" -> cycleStart,
											"Period" -> Length[stepHistory] - cycleStart,
											"States" -> (coreToTypeTheoryTerm[iterEnv, <||>, #] & /@ Drop[stepHistory, cycleStart])
										|>,
										"Statement" -> If[FailureQ[lassoProof], None, lassoProof["Statement"]],
										"Proof" -> If[FailureQ[lassoProof], None, lassoProof],
										"Method" -> "LassoCycleInduction",
										"Verified" -> ! FailureQ[lassoProof]
									|>
								],

							True,
								<|
									"Status" -> "Undetermined",
									"Target" -> HoldForm @@ heldExpr,
									"Proof" -> None,
									"Method" -> "ConcreteExecution",
									"Details" -> <|"StepsExplored" -> maxSteps|>
								|>
						]
					]
				]
			]
		]
	]
]

reduceDownValuesStep[env_, dvName_String, exprCore_] := Module[{stepTerm, nf, nfCore},
	stepTerm = Construct[application, coreConstant[HoldComplete[dvName]], exprCore];
	nf = Quiet @ catchKernelFailure[NormalForm[coreToTypeTheoryTerm[env, <||>, stepTerm]]];
	If[ FailureQ[nf],
		$Failed,
		nfCore = First[elaborateClosedTerm[env, heldTerm[nf], Construct[application, coreConstant[HoldComplete[Option], {0}], coreConstant[HoldComplete[Expressions]]], {}]];
		Replace[applicationSpine[nfCore], {
			{constantReference[HoldComplete["none"], _], _} :> "None",
			{constantReference[HoldComplete["some"], _], {_, inner_}} :> inner,
			_ :> $Failed
		}]
	]
]

buildDownValuesTerminationResult[iterEnv_, heldExpr_, exprCore_, nfCore_, steps_Integer] := Module[
	{nId, ctx, optExpr, noneTerm, iterN, eqTerm, pred, exStmt, witProof},
	nId = freshFreeVariable[];
	ctx = extendContext[<||>, nId, HoldComplete["n"], coreNaturals[], "Explicit"];
	optExpr = Construct[application, coreConstant[HoldComplete[Option], {0}], coreConstant[HoldComplete[Expressions]]];
	noneTerm = Construct[application, coreConstant[HoldComplete["none"], {0}], coreConstant[HoldComplete[Expressions]]];
	iterN = makeApplication[coreConstant[HoldComplete["iterateDownValues"]], {freeVariable[nId], exprCore}];
	eqTerm = coreEquality[optExpr, iterN, noneTerm, {1}];
	pred = makeLambda[ctx, {nId}, eqTerm];
	exStmt = makeApplication[coreConstant[HoldComplete[Exists], {1}], {coreNaturals[], pred}];
	(* Witness is steps + 1, where iterateDownValues[steps + 1, e] computes to none by Reflexivity! *)
	witProof = proveFromCore[iterEnv, exStmt, {}, {
		TypeTheoryTactic["Witness", steps + 1],
		TypeTheoryTactic["Reflexivity"]
	}];
	<|
		"Status" -> If[FailureQ[witProof], "Undetermined", "Terminating"],
		"Target" -> HoldForm @@ heldExpr,
		"Steps" -> steps,
		"NormalForm" -> coreToTypeTheoryTerm[iterEnv, <||>, nfCore],
		"Statement" -> coreToTypeTheoryTerm[iterEnv, <||>, exStmt],
		"Proof" -> If[FailureQ[witProof], None, witProof],
		"Method" -> "ConcreteExecution",
		"Verified" -> ! FailureQ[witProof]
	|>
]


(* Kernel-checked induction proof of lasso non-termination for ANY prefix m >= 0 and period p >= 1!
   Proves: ForAll[n, Or[iter[n, e0] == state_0, ..., iter[n, e0] == state_{m+p-1}]],
   then derives ForAll[n, Not[halted[iter[n, e0]]]]! *)
buildLassoNonTerminationProof[env_, exprCore_, states_List, mode : "DownValues" | "Rules"] := Module[
	{nId, ctx, optExpr, noneTerm, iterN, invBody, invStmt, invProof, finalStmt, finalProof},
	nId = freshFreeVariable[];
	ctx = extendContext[<||>, nId, HoldComplete["n"], coreNaturals[], "Explicit"];
	If[ mode === "DownValues",
		optExpr = Construct[application, coreConstant[HoldComplete[Option], {0}], coreConstant[HoldComplete[Expressions]]];
		noneTerm = Construct[application, coreConstant[HoldComplete["none"], {0}], coreConstant[HoldComplete[Expressions]]];
		iterN = makeApplication[coreConstant[HoldComplete["iterateDownValues"]], {freeVariable[nId], exprCore}];
		invBody = Fold[
			Function[{acc, st}, coreDisjunction[acc, coreEquality[optExpr, iterN, makeApplication[coreConstant[HoldComplete["some"], {0}], {coreConstant[HoldComplete[Expressions]], st}], {1}]]],
			coreEquality[optExpr, iterN, makeApplication[coreConstant[HoldComplete["some"], {0}], {coreConstant[HoldComplete[Expressions]], First[states]}], {1}],
			Rest[states]
		];
		invStmt = makeDependentFunctionType[ctx, {nId}, invBody];
		invProof = proveLassoInvariant[env, invStmt, Length[states]];
		If[ FailureQ[invProof],
			invProof,

			(* Now derive ForAll[n, Not[iterateDownValues[n, e0] == none]] from invProof *)
			finalStmt = makeDependentFunctionType[ctx, {nId}, coreNegation[env, coreEquality[optExpr, iterN, noneTerm, {1}]]];
			deriveNotNoneFromLassoInvariant[env, finalStmt, invProof, optExpr, noneTerm, states]
		],

		(* Mode "Rules": ForAll[n, SameQ[ReplaceAll[iterateReplaceAll[n, e0], "targetRules"], iterateReplaceAll[n, e0]] == "false"] *)
		iterN = makeApplication[coreConstant[HoldComplete["iterateReplaceAll"]], {freeVariable[nId], exprCore}];
		invBody = Fold[
			Function[{acc, st}, coreDisjunction[acc, coreEquality[coreConstant[HoldComplete[Expressions]], iterN, st, {1}]]],
			coreEquality[coreConstant[HoldComplete[Expressions]], iterN, First[states], {1}],
			Rest[states]
		];
		invStmt = makeDependentFunctionType[ctx, {nId}, invBody];
		invProof = proveLassoInvariant[env, invStmt, Length[states]];
		If[ FailureQ[invProof],
			invProof,

			finalStmt = makeDependentFunctionType[ctx, {nId},
				coreEquality[
					coreBooleans[],
					makeApplication[coreConstant[HoldComplete[SameQ]], {makeApplication[coreConstant[HoldComplete[ReplaceAll]], {iterN, coreConstant[HoldComplete["targetRules"]]}], iterN}],
					coreConstant[HoldComplete["false"]],
					{1}
				]
			];
			deriveNotFixedFromLassoInvariant[env, finalStmt, invProof, states]
		]
	]
]

(* Prove the disjunctive lasso invariant by induction on n, splitting Or branches and rewriting + Reflexivity *)
proveLassoInvariant[env_, invStmt_, numStates_Integer] := Module[{state, indState, closed},
	state = newProofState[env, invStmt, {}];
	indState = Quiet @ catchKernelFailure[runTactics[state, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Induction", n]}]];
	If[ FailureQ[indState],
		indState,

		(* Goal 1 (base case n = 0): close first disjunct by Reflexivity *)
		closed = closeDisjunctByReflexivity[indState, 1, numStates];
		If[ FailureQ[closed],
			closed,

			(* Goal 2 (step case k + 1): introduce k, ih; recursively split ih (left-nested Or) *)
			closed = Quiet @ catchKernelFailure[runTactics[closed, {TypeTheoryTactic["Introduce", k, ih]}]];
			If[ FailureQ[closed],
				closed,

				closed = splitAndCloseLassoStep[closed, numStates];
				verifyProofInKernel[env, invStmt, {}, closed]
			]
		]
	]
]

(* Close a goal A_1 || A_2 || ... || A_m (left-nested) where branch idx holds by Reflexivity *)
closeDisjunctByReflexivity[proof_TypeTheoryProof, idx_Integer, total_Integer] := Module[{cur = proof, pos = total},
	(* Left-nested: ((A_1 || A_2) || A_3) ... || A_total *)
	While[ pos > 1 && ! FailureQ[cur],
		If[ idx === pos,
			cur = Quiet @ catchKernelFailure[TypeTheoryTactic["Apply", "orIntroductionRight"][cur]];
			Break[],
			cur = Quiet @ catchKernelFailure[TypeTheoryTactic["Apply", "orIntroductionLeft"][cur]];
			pos = pos - 1
		]
	];
	If[ FailureQ[cur], cur, Quiet @ catchKernelFailure[TypeTheoryTactic["Reflexivity"][cur]]]
]

(* Recursively case-split left-nested Or hypothesis 'ih' and close each leaf by rewriting + matching disjunct Reflexivity *)
splitAndCloseLassoStep[proof_TypeTheoryProof, numStates_Integer] := closeAllGoalsWith[
	proof,
	Function[cur,
		With[{d = First[cur]},
			{g = First[d["Goals"]]},
			{ctx = currentGoal[d, g]["Context"]},
			{orId = SelectFirst[Reverse[Keys[ctx]], Function[id, MatchQ[weakHeadNormalForm[d["Environment"], ctx, ctx[id]["Type"]], application[application[constantReference[HoldComplete[Or], _], _], _]]], None]},
			If[ orId =!= None,
				With[{nm = ctx[orId]["Name"]},
					Quiet @ catchKernelFailure[
						runTactics[
							Replace[nm, HoldComplete[sym_] :> TypeTheoryTactic["Cases", sym][cur]],
							{}
						]
					]
				],
				(* Leaf branch: introduce any remaining hypothesis, rewrite with the equality hypothesis, try each disjunct 1..numStates *)
				With[{intro = introduceAll[cur]},
					closeLassoLeafBranch[intro, numStates]
				]
			]
		]
	]
]

closeLassoLeafBranch[proof_TypeTheoryProof, numStates_Integer] := Module[{d = First[proof], g, ctx, eqId, unfolded, rewritten, found},
	g = First[d["Goals"]];
	ctx = currentGoal[d, g]["Context"];
	eqId = SelectFirst[Reverse[Keys[ctx]], Function[id, MatchQ[weakHeadNormalForm[d["Environment"], ctx, ctx[id]["Type"]], application[application[application[constantReference[HoldComplete[Equal], _], _], _], _]]], None];
	(* Unfold one step of iterateDownValues / iterateReplaceAll on the goal so ih's LHS appears! *)
	unfolded = unfoldIterStepInGoal[proof];
	rewritten = If[ eqId === None,
		unfolded,
		With[{nm = ctx[eqId]["Name"]},
			Quiet @ catchKernelFailure[Replace[nm, HoldComplete[sym_] :> TypeTheoryTactic["Rewrite", sym][unfolded]]]
		]
	];
	If[ FailureQ[rewritten],
		rewritten,

		found = SelectFirst[
			Range[numStates],
			Function[idx,
				With[{attempt = closeDisjunctByReflexivity[rewritten, idx, numStates]},
					! FailureQ[attempt] && Length[attempt["Goals"]] < Length[rewritten["Goals"]]
				]
			],
			None
		];
		If[ found === None,
			Failure["LassoBranchFailed", <||>],
			closeDisjunctByReflexivity[rewritten, found, numStates]
		]
	]
]

(* Unfold one step of iterateDownValues[successor[k], e] or iterateReplaceAll[successor[k], e] while keeping the recursive call folded! *)
unfoldIterStepInGoal[proof_TypeTheoryProof] := Module[{d = First[proof], g, cur, env, newType, newG, dvConst},
	g = First[d["Goals"]];
	cur = currentGoal[d, g];
	env = d["Environment"];
	dvConst = SelectFirst[
		environmentNames[env],
		Function[name, MatchQ[name, HoldComplete[s_String] /; StringStartsQ[s, "DownValues["]]],
		None
	];
	newType = ReplaceAll[
		cur["Type"],
		{
			term : application[application[constantReference[HoldComplete["iterateDownValues"], _], application[constantReference[HoldComplete["successor"], _], k_]], e_] /; dvConst =!= None :>
				With[
					{
						optExpr = Construct[application, coreConstant[HoldComplete[Option], {0}], coreConstant[HoldComplete[Expressions]]],
						noneTerm = Construct[application, coreConstant[HoldComplete["none"], {0}], coreConstant[HoldComplete[Expressions]]],
						prevCall = makeApplication[coreConstant[HoldComplete["iterateDownValues"]], {k, e}]
					},
					{
						stepped = makeApplication[
							coreConstant[recursorName[HoldComplete[Option]], {1, 0}],
							{
								coreConstant[HoldComplete[Expressions]],
								Construct[lambdaAbstraction, HoldComplete["o"], optExpr, optExpr, "Explicit"],
								noneTerm,
								Construct[lambdaAbstraction, HoldComplete["x"], coreConstant[HoldComplete[Expressions]], Construct[application, coreConstant[dvConst], boundVariable[0]], "Explicit"],
								prevCall
							}
						]
					},
					stepped /; True
				],
			term : application[application[constantReference[HoldComplete["iterateReplaceAll"], _], application[constantReference[HoldComplete["successor"], _], k_]], e_] :>
				With[
					{
						stepped = makeApplication[
							coreConstant[HoldComplete[ReplaceAll]],
							{makeApplication[coreConstant[HoldComplete["iterateReplaceAll"]], {k, e}], coreConstant[HoldComplete["targetRules"]]}
						]
					},
					stepped /; True
				]
		}
	];
	If[ newType === cur["Type"],
		proof,

		newG = freshMetavariableId[];
		proofState @ solveGoal[
			d,
			g,
			metavariable[newG],
			{newG -> <|"Context" -> cur["Context"], "Type" -> newType, "Case" -> None|>}
		]
	]
]

(* From invProof : ForAll[n, Or[iter[n, e0] == some[s_i], ...]], prove ForAll[n, Not[iter[n, e0] == none]] *)
deriveNotNoneFromLassoInvariant[env_, finalStmt_, invProof_TypeTheoryProof, optExpr_, noneTerm_, states_List] := Module[
	{state, invTerm = completedProofTerm[invProof], nId, hEqId, invHypId, goalId, ctx, d, closed},
	state = newProofState[env, finalStmt, {}];
	state = Quiet @ catchKernelFailure[runTactics[state, {TypeTheoryTactic["Introduce", n, hEq]}]];
	If[ FailureQ[state],
		state,

		(* Add invApplied = invTerm[n] as a local hypothesis via pendingAbstraction *)
		d = First[state];
		goalId = First[d["Goals"]];
		ctx = currentGoal[d, goalId]["Context"];
		nId = First[Keys[ctx]];
		invHypId = freshFreeVariable[];
		With[
			{
				invApplied = Construct[application, invTerm, freeVariable[nId]],
				newGoal = freshMetavariableId[]
			},
			{
				invAppliedType = betaNormalize[inferType[env, ctx, invApplied]]
			},
			{
				ctx2 = extendContext[ctx, invHypId, HoldComplete["hInv"], invAppliedType, "Explicit"]
			},
			{
				stepState = proofState @ solveGoal[
					d,
					goalId,
					Construct[application, pendingAbstraction[ctx2, {invHypId}, metavariable[newGoal]], invApplied],
					{newGoal -> <|"Context" -> ctx2, "Type" -> currentGoal[d, goalId]["Type"], "Case" -> None|>}
				]
			},
			(* Split the Or invariant; each leaf has iter[n, e0] == some[s_i] and iter[n, e0] == none -> prove False by Option recursor! *)
			closed = closeAllGoalsWith[stepState, Function[cur,
				With[{cd = First[cur]},
					{cg = First[cd["Goals"]]},
					{cctx = currentGoal[cd, cg]["Context"]},
					{orId = SelectFirst[Reverse[Keys[cctx]], Function[id, MatchQ[weakHeadNormalForm[env, cctx, cctx[id]["Type"]], application[application[constantReference[HoldComplete[Or], _], _], _]]], None]},
					If[ orId =!= None,
						With[{nm = cctx[orId]["Name"]},
							Quiet @ catchKernelFailure[Replace[nm, HoldComplete[sym_] :> TypeTheoryTactic["Cases", sym][cur]]]
						],
						With[{intro = introduceAll[cur]},
							closeSomeEqualsNoneBranch[intro, optExpr]
						]
					]
				]
			]];
			verifyProofInKernel[env, finalStmt, {}, closed]
		]
	]
]

(* Prove False in a branch that has hEq : t == none and hSome : t == some[s] *)
closeSomeEqualsNoneBranch[proof_TypeTheoryProof, optExpr_] := Module[
	{d = First[proof], g, ctx, env, eqIds, someHypId, noneHypId, rewritten, motive, discProof},
	g = First[d["Goals"]];
	ctx = currentGoal[d, g]["Context"];
	env = d["Environment"];
	someHypId = SelectFirst[Keys[ctx], Function[id, MatchQ[ctx[id]["Type"], application[application[application[constantReference[HoldComplete[Equal], _], _], _], application[application[constantReference[HoldComplete["some"], _], _], _]]]], None];
	noneHypId = SelectFirst[Keys[ctx], Function[id, MatchQ[ctx[id]["Type"], application[application[application[constantReference[HoldComplete[Equal], _], _], _], application[constantReference[HoldComplete["none"], _], _]]]], None];
	If[ someHypId === None || noneHypId === None,
		Failure["MissingOptionEquations", <||>],

		(* Rewrite t -> none in someHypId, or transport True along equalitySymmetry[someHyp] ++ noneHyp!
		   Even cleaner: build isSome : Option[Expressions] -> Prop := Option_rec[False, _ |-> True],
		   prove isSome[some[s]] = True by "trueIntroduction", transport along sym[someHyp] and noneHyp to get isSome[none] = False! *)
		With[
			{
				tTerm = Last[First[ctx[someHypId]["Type"]]],
				someTerm = Last[ctx[someHypId]["Type"]],
				noneTerm = Last[ctx[noneHypId]["Type"]],
				oId = freshFreeVariable[],
				xId = freshFreeVariable[]
			},
			{
				isSomeFn = makeLambda[
					extendContext[ctx, oId, HoldComplete["o"], optExpr, "Explicit"],
					{oId},
					makeApplication[
						coreConstant[recursorName[HoldComplete[Option]], {1, 0}],
						{
							coreConstant[HoldComplete[Expressions]],
							Construct[lambdaAbstraction, HoldComplete["m"], optExpr, universeSort[0], "Explicit"],
							coreFalse[],
							Construct[lambdaAbstraction, HoldComplete["x"], coreConstant[HoldComplete[Expressions]], coreTrue[], "Explicit"],
							freeVariable[oId]
						}
					]
				],
				eqSomeNone = makeApplication[
					coreConstant[HoldComplete["equalityTransitivity"], {1}],
					{
						optExpr,
						someTerm,
						tTerm,
						noneTerm,
						makeApplication[coreConstant[HoldComplete["equalitySymmetry"], {1}], {optExpr, tTerm, someTerm, freeVariable[someHypId]}],
						freeVariable[noneHypId]
					}
				]
			},
			{
				falseTerm = makeApplication[
					coreConstant[HoldComplete["equalitySubstitution"], {1}],
					{optExpr, isSomeFn, someTerm, noneTerm, eqSomeNone, coreConstant[HoldComplete["trueIntroduction"]]}
				]
			},
			proofState @ solveGoal[d, g, falseTerm, {}]
		]
	]
]

deriveNotFixedFromLassoInvariant[env_, finalStmt_, invProof_TypeTheoryProof, states_List] := Module[
	{state, invTerm = completedProofTerm[invProof], d, goalId, ctx, nId, invHypId, closed},
	state = newProofState[env, finalStmt, {}];
	state = Quiet @ catchKernelFailure[TypeTheoryTactic["Introduce", n][state]];
	If[ FailureQ[state],
		state,

		d = First[state];
		goalId = First[d["Goals"]];
		ctx = currentGoal[d, goalId]["Context"];
		nId = First[Keys[ctx]];
		invHypId = freshFreeVariable[];
		With[
			{
				invApplied = Construct[application, invTerm, freeVariable[nId]],
				newGoal = freshMetavariableId[]
			},
			{invAppliedType = betaNormalize[inferType[env, ctx, invApplied]]},
			{ctx2 = extendContext[ctx, invHypId, HoldComplete["hInv"], invAppliedType, "Explicit"]},
			{
				stepState = proofState @ solveGoal[
					d,
					goalId,
					Construct[application, pendingAbstraction[ctx2, {invHypId}, metavariable[newGoal]], invApplied],
					{newGoal -> <|"Context" -> ctx2, "Type" -> currentGoal[d, goalId]["Type"], "Case" -> None|>}
				]
			},
			closed = closeAllGoalsWith[stepState, Function[cur,
				With[{cd = First[cur]},
					{cg = First[cd["Goals"]]},
					{cctx = currentGoal[cd, cg]["Context"]},
					{orId = SelectFirst[Reverse[Keys[cctx]], Function[id, MatchQ[weakHeadNormalForm[env, cctx, cctx[id]["Type"]], application[application[constantReference[HoldComplete[Or], _], _], _]]], None]},
					If[ orId =!= None,
						With[{nm = cctx[orId]["Name"]},
							Quiet @ catchKernelFailure[Replace[nm, HoldComplete[sym_] :> TypeTheoryTactic["Cases", sym][cur]]]
						],
						With[{intro = introduceAll[cur]},
							With[{id2 = First[intro], g2 = First[First[intro]["Goals"]]},
								With[{ctxL = currentGoal[id2, g2]["Context"]},
									With[{eqId = SelectFirst[Reverse[Keys[ctxL]], Function[id, MatchQ[ctxL[id]["Type"], application[application[application[constantReference[HoldComplete[Equal], _], _], _], _]]], None]},
										With[{nm = ctxL[eqId]["Name"]},
											Quiet @ catchKernelFailure[runTactics[intro, {Replace[nm, HoldComplete[sym_] :> TypeTheoryTactic["Rewrite", sym]], TypeTheoryTactic["Reflexivity"]}]]
										]
									]
								]
							]
						]
					]
				]
			]];
			verifyProofInKernel[env, finalStmt, {}, closed]
		]
	]
]


(* --- Target 4C: Global Rewrite Rule System Termination (Polynomial Weight Interpretation M4) --- *)
terminationGlobalRules[heldRules_HoldComplete, environmentSpec_, Hold[opts___]] := Module[
	{environment, rulesList, weightResult, methodOpt, llmEval},
	environment = If[environmentSpec === Automatic, TypeTheoryEnvironment["Prelude"], resolveEnvironmentArg[environmentSpec]];
	If[ FailureQ[environment],
		environment,

		methodOpt = OptionValue[TypeTheoryTermination, {opts}, Method];
		llmEval = OptionValue[TypeTheoryTermination, {opts}, "LLMEvaluator"];
		rulesList = Replace[heldRules, HoldComplete[{rs___}] :> HoldComplete /@ Unevaluated[{rs}]];

		(* First check M4: linear polynomial weight interpretation *)
		weightResult = If[ useHeuristicQ[methodOpt],
			reportProgress["Synthesizing polynomial weight interpretation...", 0.30];
			certifyRewriteRulesByWeight[environment, rulesList, heldRules],
			None
		];
		If[ AssociationQ[weightResult],
			weightResult,

			(* Next check M1/M5: try finding a concrete non-terminating instance / self-embedding witness *)
			reportProgress["Probing for rewrite non-termination witnesses...", 0.72];
			With[{nonTermResult = findRulesNonTerminationWitness[environment, rulesList, heldRules, opts]},
				If[ AssociationQ[nonTermResult],
					nonTermResult,

					<|
						"Status" -> "Undetermined",
						"Target" -> HoldForm @@ heldRules,
						"Proof" -> None,
						"Method" -> "SearchExhausted",
						"Verified" -> False
					|>
				]
			]
		]
	]
]

(* Synthesize linear polynomial weights w_h(u_1, ..., u_m) = c0 + Sum[c_j * u_j] (c0 >= 0, c_j >= 1)
   and KERNEL-PROVE w(rhs) < w(lhs) for every rule using an InductiveRecursor[Expressions] measure! *)
certifyRewriteRulesByWeight[environment_, rulesList_List, heldRules_HoldComplete] := Module[
	{parsedRules, heads, weightParams, constraints, sol, weights, measureEnv, ruleProofs},
	parsedRules = parseFirstOrderRule /@ rulesList;
	If[ MemberQ[parsedRules, $Failed] || parsedRules === {},
		None,

		heads = DeleteDuplicates[Catenate[#["Heads"] & /@ parsedRules]];
		(* Create integer weight variables: for each {headFullName, arity}, c0 >= 0 and c1..cm >= 1 *)
		weightParams = Association @ MapIndexed[
			Function[{ha, idx},
				ha -> {Subscript[\[FormalC], First[idx], 0], Table[Subscript[\[FormalC], First[idx], j], {j, Last[ha]}]}
			],
			heads
		];
		constraints = Join[
			Catenate[KeyValueMap[Function[{ha, params}, Join[{0 <= First[params] <= 4}, Thread[1 <= Last[params] <= 3]]], weightParams]],
			Catenate[ruleWeightConstraints[#, weightParams] & /@ parsedRules]
		];
		sol = TimeConstrained[
			Quiet @ FindInstance[And @@ constraints, Flatten[Values[weightParams]], Integers],
			2,
			{}
		];
		(* Fallback for nonlinear polynomial weight constraints (e.g. a[b[x]] :> b[a[x]]): fast finite grid search! *)
		If[ ! MatchQ[sol, {_List, ___}],
			sol = searchSmallWeightAssignment[weightParams, parsedRules]
		];
		If[ ! MatchQ[sol, {_List, ___}],
			None,

			weights = Association @ KeyValueMap[
				Function[{ha, params}, ha -> ReplaceAll[params, First[sol]]],
				weightParams
			];
			(* Build kernel-checked TypeTheoryDefinition "expressionWeight" : Expressions -> NonNegativeIntegers *)
			measureEnv = buildExpressionWeightEnvironment[environment, weights];
			If[ FailureQ[measureEnv],
				None,

				(* Prove ForAll[xs, expressionWeight[rhs] < expressionWeight[lhs]] for EVERY rule in the kernel! *)
				ruleProofs = MapIndexed[
					Function[{rule, idx},
						reportProgress[
							"Proving weight decrease for rule " <> IntegerString[First[idx]] <> "/" <> IntegerString[Length[parsedRules]] <> " in kernel...",
							0.50 + 0.42 * (First[idx] / Max[1, Length[parsedRules]])
						];
						proveRuleWeightDecrease[measureEnv, rule]
					],
					parsedRules
				];
				If[ AnyTrue[ruleProofs, FailureQ],
					None,

					<|
						"Status" -> "Terminating",
						"Target" -> HoldForm @@ heldRules,
						"Measure" -> Association @ KeyValueMap[
							Function[{ha, vals}, First[ha] -> <|"Constant" -> First[vals], "Coefficients" -> Last[vals]|>],
							weights
						],
						"MeasureDefinition" -> measureEnv["expressionWeight"],
						"RuleProofs" -> ruleProofs,
						"Proof" -> If[Length[ruleProofs] === 1, First[ruleProofs], ruleProofs],
						"Method" -> "PolynomialWeightInterpretation",
						"Verified" -> True
					|>
				]
			]
		]
	]
]

parseFirstOrderRule[HoldComplete[(Rule | RuleDelayed)[lhs_, rhs_]]] := Module[{vars, heads},
	vars = DeleteDuplicates[Cases[HoldComplete[lhs], HoldPattern[Verbatim[Pattern][x_Symbol, Verbatim[Blank][]]] :> HoldComplete[x], {0, Infinity}]];
	(* Reject rules with sequence blanks, conditions, or nonlinear/higher-order features for first-order weight engine *)
	If[ ! FreeQ[HoldComplete[lhs], _BlankSequence | _BlankNullSequence | _Condition | _PatternTest | _Alternatives],
		$Failed,

		With[
			{
				lhsTree = exprToFirstOrderTree[HoldComplete[lhs], vars],
				rhsTree = exprToFirstOrderTree[HoldComplete[rhs], vars]
			},
			If[ lhsTree === $Failed || rhsTree === $Failed,
				$Failed,

				heads = DeleteDuplicates[Cases[{lhsTree, rhsTree}, foApply[h_, args_List] :> {h, Length[args]}, {0, Infinity}]];
				<|"Variables" -> vars, "Left" -> lhsTree, "Right" -> rhsTree, "Heads" -> heads|>
			]
		]
	]
]
parseFirstOrderRule[_] := $Failed

exprToFirstOrderTree[HoldComplete[Verbatim[Pattern][x_Symbol, Verbatim[Blank][]]], vars_List] := foVar[HoldComplete[x]]
exprToFirstOrderTree[HoldComplete[x_Symbol], vars_List] /; MemberQ[vars, HoldComplete[x]] := foVar[HoldComplete[x]]
exprToFirstOrderTree[HoldComplete[h_Symbol[args___]], vars_List] := With[
	{parsedArgs = exprToFirstOrderTree[#, vars] & /@ (HoldComplete /@ Unevaluated[{args}])},
	If[ MemberQ[parsedArgs, $Failed],
		$Failed,
		foApply[fullName[h], parsedArgs]
	]
]
exprToFirstOrderTree[HoldComplete[s_Symbol], _] := foConst[fullName[s]]
exprToFirstOrderTree[HoldComplete[n_Integer?NonNegative], _] := foNat[n]
exprToFirstOrderTree[_, _] := $Failed

ruleWeightConstraints[rule_Association, weightParams_Association] := Module[
	{wlVars, varRules, wL, wR, diff, coeffRules, constCoeff, varCoeffs},
	wlVars = Table[Subscript[\[FormalU], j], {j, Length[rule["Variables"]]}];
	varRules = AssociationThread[rule["Variables"], wlVars];
	wL = evalTreeWeight[rule["Left"], varRules, weightParams];
	wR = evalTreeWeight[rule["Right"], varRules, weightParams];
	diff = Expand[wL - wR];
	If[ wlVars === {},
		{diff >= 1},

		coeffRules = CoefficientRules[diff, wlVars];
		constCoeff = Lookup[Association[coeffRules], Key[ConstantArray[0, Length[wlVars]]], 0];
		varCoeffs = Values[KeyDrop[Association[coeffRules], {Key[ConstantArray[0, Length[wlVars]]]}]];
		Prepend[Thread[varCoeffs >= 0], constCoeff >= 1]
	]
]

evalTreeWeight[foVar[v_], varRules_, _] := varRules[v]
evalTreeWeight[foConst[_], _, _] := 1
evalTreeWeight[foNat[_], _, _] := 1
evalTreeWeight[foApply[h_, args_List], varRules_, weightParams_] := With[
	{params = weightParams[{h, Length[args]}]},
	First[params] + Total[MapThread[Times, {Last[params], evalTreeWeight[#, varRules, weightParams] & /@ args}]]
]

(* Fast bounded enumeration for nonlinear polynomial weight constraints when FindInstance gives {} *)
searchSmallWeightAssignment[weightParams_Association, parsedRules_List] := Module[
	{allVars, c0Vars, cjVars, domains, ruleConds, tuples, found},
	c0Vars = First /@ Values[weightParams];
	cjVars = Catenate[Last /@ Values[weightParams]];
	allVars = Join[c0Vars, cjVars];
	If[ Length[allVars] > 8,
		{},

		domains = Join[ConstantArray[{1, 0, 2}, Length[c0Vars]], ConstantArray[{1, 2}, Length[cjVars]]];
		ruleConds = And @@ Catenate[ruleWeightConstraints[#, weightParams] & /@ parsedRules];
		tuples = Tuples[domains];
		found = SelectFirst[
			tuples,
			Function[vals, TrueQ[Quiet[ReplaceAll[ruleConds, Thread[allVars -> vals]]]]],
			None
		];
		If[ found === None, {}, {Thread[allVars -> found]}]
	]
]

(* Build a TypeTheoryEnvironment extending environment with:
   "weightSequence" : {NonNegativeIntegers} -> {NonNegativeIntegers} -> NonNegativeIntegers (dot product of coefficients and arg weights)
   "expressionWeight" : Expressions -> NonNegativeIntegers (InductiveRecursor[Expressions]) *)
buildExpressionWeightEnvironment[environment_, weights_Association] := Module[{branchExpr},
	branchExpr = buildHeadDispatchHeld[Normal[weights]];
	Replace[branchExpr, HoldComplete[dispatch_] :> Quiet @ TypeTheoryEnvironment[environment, {
			TypeTheoryDefinition["listSum", Typed[
				Function[{Typed[l, {NonNegativeIntegers}]},
					InductiveRecursor[List][
						Typed[t, {NonNegativeIntegers}] |-> NonNegativeIntegers,
						0,
						{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[r, NonNegativeIntegers]} |-> x + r,
						l
					]
				],
				{NonNegativeIntegers} -> NonNegativeIntegers
			]],
			TypeTheoryDefinition["weightedDot", Typed[
				Function[{Typed[cs, {NonNegativeIntegers}], Typed[ws, {NonNegativeIntegers}]},
					InductiveRecursor[List][
						Typed[t, {NonNegativeIntegers}] |-> ({NonNegativeIntegers} -> NonNegativeIntegers),
						Typed[u, {NonNegativeIntegers}] |-> 0,
						{Typed[c, NonNegativeIntegers], Typed[crest, {NonNegativeIntegers}], Typed[rec, {NonNegativeIntegers} -> NonNegativeIntegers]} |->
							Function[{Typed[u, {NonNegativeIntegers}]},
								InductiveRecursor[List][
									Typed[s, {NonNegativeIntegers}] |-> NonNegativeIntegers,
									0,
									{Typed[w, NonNegativeIntegers], Typed[wrest, {NonNegativeIntegers}], Typed[unused, NonNegativeIntegers]} |-> w * c + rec[wrest],
									u
								]
							],
						cs
					][ws]
				],
				{NonNegativeIntegers} -> {NonNegativeIntegers} -> NonNegativeIntegers
			]],
			TypeTheoryDefinition["expressionWeight", Typed[
				Function[{Typed[e, Expressions]},
					InductiveRecursor[Expressions][
						Typed[x, Expressions] |-> NonNegativeIntegers,
						Typed[xs, Expressions...] |-> {NonNegativeIntegers},
						Typed[a, Atoms] |-> 1,
						{Typed[h, Expressions], Typed[arguments, Expressions...], Typed[hr, NonNegativeIntegers], Typed[ar, {NonNegativeIntegers}]} |-> dispatch,
						Typed[{}, {NonNegativeIntegers}],
						{Typed[x, Expressions], Typed[rest, Expressions...], Typed[xr, NonNegativeIntegers], Typed[rr, {NonNegativeIntegers}]} |-> Prepend[xr][rr],
						e
					]
				],
				Expressions -> NonNegativeIntegers
			]]
		}]]
]

buildHeadDispatchHeld[{}] := HoldComplete[1 + "listSum"[ar]]
buildHeadDispatchHeld[{{hName_String, arity_Integer} -> {c0_Integer, coeffs_List}, rest___}] := With[
	{
		elseHeld = buildHeadDispatchHeld[{rest}],
		coeffListHeld = buildNaturalListHeld[coeffs]
	},
	Replace[{elseHeld, coeffListHeld}, {HoldComplete[elseExpr_], HoldComplete[cList_]} :>
		HoldComplete[
			InductiveRecursor[Booleans][
				Typed[b, Booleans] |-> NonNegativeIntegers,
				elseExpr,
				c0 + "weightedDot"[cList, ar],
				"and"[SameQ[h, "atom"["symbolAtom"[hName]]], "equal"[Length[ar], arity]]
			]
		]
	]
]

buildNaturalListHeld[{}] := HoldComplete[Typed[{}, {NonNegativeIntegers}]]
buildNaturalListHeld[{c_Integer, rest___}] := Replace[buildNaturalListHeld[{rest}], HoldComplete[r_] :> HoldComplete[Prepend[c][r]]]

(* Prove ForAll[{Typed[x1, Expressions], ...}, expressionWeight[rhs] < expressionWeight[lhs]] in the kernel! *)
proveRuleWeightDecrease[measureEnv_, rule_Association] := Module[
	{varIds, varMap, ctx, lhsCore, rhsCore, ineqCore, stmtCore, proof},
	varIds = Table[freshFreeVariable[], Length[rule["Variables"]]];
	varMap = AssociationThread[rule["Variables"], varIds];
	ctx = Fold[
		Function[{c, pair}, extendContext[c, Last[pair], First[pair], coreConstant[HoldComplete[Expressions]], "Explicit"]],
		<||>,
		Thread[{rule["Variables"], varIds}]
	];
	lhsCore = foTreeToCoreExpression[rule["Left"], varMap];
	rhsCore = foTreeToCoreExpression[rule["Right"], varMap];
	ineqCore = coreNaturalLess[
		Construct[application, coreConstant[HoldComplete["expressionWeight"]], rhsCore],
		Construct[application, coreConstant[HoldComplete["expressionWeight"]], lhsCore]
	];
	stmtCore = makeDependentFunctionType[ctx, varIds, ineqCore];
	(* Introduce variables, compute expressionWeight symbolically by Change/NormalForm, close with LinearArithmetic! *)
	proof = enhancedProveCore[measureEnv, stmtCore, {}, 3.0];
	If[ ! FailureQ[proof],
		proof,

		(* Explicitly unfold expressionWeight on both sides to linear arithmetic over expressionWeight[x_i] *)
		With[{state = introduceAll[newProofState[measureEnv, stmtCore, {}]]},
			With[{d = First[state]},
				{g = First[d["Goals"]]},
				{cur = currentGoal[d, g]},
				(* Read the introduced lhs/rhs from cur["Type"] so free variable IDs match cur["Context"]! *)
				With[{sides = Replace[weakHeadNormalForm[measureEnv, cur["Context"], cur["Type"]], {
					application[application[constantReference[HoldComplete[LessEqual], _], application[constantReference[HoldComplete["successor"], _], r_]], l_] :> {r, l},
					application[application[constantReference[HoldComplete[LessEqual], _], application[application[constantReference[HoldComplete[Plus], _], r_], naturalLiteral[1]]], l_] :> {r, l},
					_ :> None
				}]},
					If[ sides === None,
						Failure["WeightGoalShape", <||>],

						With[
							{
								wR = reduceExpressionWeightCore[measureEnv, cur["Context"], First[sides]],
								wL = reduceExpressionWeightCore[measureEnv, cur["Context"], Last[sides]]
							},
							{reducedGoal = coreNaturalLessEqual[coreNaturalPlus[wR, naturalLiteral[1]], wL]},
							With[{newGoalId = freshMetavariableId[]},
								If[ withKernelCaches[definitionallyEqualQ[measureEnv, cur["Context"], cur["Type"], reducedGoal]],
									With[
										{
											st2 = proofState @ solveGoal[d, g, metavariable[newGoalId], {newGoalId -> <|"Context" -> cur["Context"], "Type" -> reducedGoal, "Case" -> None|>}]
										},
										verifyProofInKernel[measureEnv, stmtCore, {}, Quiet @ catchKernelFailure[TypeTheoryTactic["LinearArithmetic"][st2]]]
									],
									Failure["WeightReductionMismatch", <||>]
								]
							]
						]
					]
				]
			]
		]
	]
]

reduceExpressionWeightCore[env_, context_, term_] := FixedPoint[
	Function[t,
		With[{w = weakHeadNormalForm[env, context, t]},
			Replace[w, {
				application[constantReference[HoldComplete["successor"], _], a_] :>
					Construct[application, coreConstant[HoldComplete["successor"]], reduceExpressionWeightCore[env, context, a]],
				application[application[constantReference[HoldComplete[Plus], _], a_], b_] :> coreNaturalPlus[reduceExpressionWeightCore[env, context, a], reduceExpressionWeightCore[env, context, b]],
				application[application[constantReference[HoldComplete[Times], _], a_], b_] :> coreNaturalTimes[reduceExpressionWeightCore[env, context, a], reduceExpressionWeightCore[env, context, b]],
				other_ :> other
			}]
		]
	],
	term,
	20
]

foTreeToCoreExpression[foVar[v_], varMap_Association] := freeVariable[varMap[v]]
foTreeToCoreExpression[foConst[name_String], _] := Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["symbolAtom"]], stringLiteralCore[name]]]
foTreeToCoreExpression[foNat[n_Integer], _] := Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["naturalAtom"]], naturalLiteral[n]]]
foTreeToCoreExpression[foApply[hName_String, args_List], varMap_Association] := makeApplication[
	coreConstant[HoldComplete["Construct"]],
	{
		Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["symbolAtom"]], stringLiteralCore[hName]]],
		foArgSequenceCore[foTreeToCoreExpression[#, varMap] & /@ args]
	}
]

foArgSequenceCore[{}] := Construct[application, coreConstant[HoldComplete["emptySequenceOf"], {0}], coreConstant[HoldComplete[Expressions]]]
foArgSequenceCore[{a_, rest___}] := makeApplication[
	coreConstant[HoldComplete["sequenceOfPrepend"], {0}],
	{coreConstant[HoldComplete[Expressions]], a, foArgSequenceCore[{rest}]}
]

stringLiteralCore[s_String] := Construct[application, coreConstant[HoldComplete["string"]], buildNatListCore[ToCharacterCode[s]]]
buildNatListCore[{}] := Construct[application, coreConstant[HoldComplete["{}"], {0}], coreNaturals[]]
buildNatListCore[{c_Integer, rest___}] := makeApplication[coreConstant[HoldComplete["Prepend"], {0}], {coreNaturals[], naturalLiteral[c], buildNatListCore[{rest}]}]


(* Try concrete instances of rule LHSes to find a lasso non-termination witness *)
findRulesNonTerminationWitness[environment_, rulesList_List, heldRules_HoldComplete, opts___] := Module[{testExprs, hit},
	testExprs = DeleteCases[
		Function[r, Replace[r, {HoldComplete[(Rule | RuleDelayed)[lhs_, _]] :> instantiatePatternWithZero[HoldComplete[lhs]], _ :> None}]] /@ rulesList,
		None
	];
	hit = SelectFirst[
		testExprs,
		Function[heldE,
			With[{res = Replace[{heldE, heldRules}, {HoldComplete[e_], HoldComplete[rs_]} :> terminationPointwiseRules[HoldComplete[e], HoldComplete[rs], environment, Hold[opts]]]},
				AssociationQ[res] && res["Status"] === "NonTerminating"
			]
		],
		None
	];
	If[ hit === None,
		None,
		Replace[{hit, heldRules}, {HoldComplete[e_], HoldComplete[rs_]} :> Append[terminationPointwiseRules[HoldComplete[e], HoldComplete[rs], environment, Hold[opts]], "Witness" -> HoldForm[e]]]
	]
]

instantiatePatternWithZero[HoldComplete[lhs_]] := ReplaceAll[HoldComplete[lhs], {
	Verbatim[Pattern][_, _] :> 0,
	Verbatim[Blank][___] :> 0
}]


(* --- Target 4D: Termination of a Wolfram Language Symbol (DownValues / While / Recursive / Compiled) --- *)
terminationSymbol[heldSym : HoldComplete[symbol_Symbol], environmentSpec_, Hold[opts___]] := Module[
	{meaningOpt, methodOpt, maxSteps, llmEval, dvs, environment, loopSpec, res},
	reportProgress["Inspecting symbol definitions...", 0.08];
	meaningOpt = OptionValue[TypeTheoryTermination, {opts}, "Meaning"];
	methodOpt = OptionValue[TypeTheoryTermination, {opts}, Method];
	maxSteps = Replace[OptionValue[TypeTheoryTermination, {opts}, "MaxSteps"], Except[_Integer?Positive] -> 100];
	llmEval = OptionValue[TypeTheoryTermination, {opts}, "LLMEvaluator"];
	dvs = definitionStatements[symbol];
	If[ dvs === {},
		Failure["NoDefinitions", <|"MessageTemplate" -> "`1` has no DownValues to analyze.", "MessageParameters" -> {HoldForm[symbol]}|>],

		(* Dispatch by Meaning or automatically inspect the symbol's definition structure *)
		Which[
			meaningOpt === "Rules",
				terminationSymbolAsRules[heldSym, environmentSpec, Hold[opts]],

			meaningOpt === "Function",
				terminationSymbolAsFunction[heldSym, environmentSpec],

			True,
				(* Check if it is a While-loop or integer-recursive function *)
				loopSpec = extractIntegerLoopOrRecursion[heldSym, dvs];
				Which[
					AssociationQ[loopSpec],
						analyzeIntegerLoopOrRecursion[heldSym, loopSpec, methodOpt, maxSteps, llmEval],

					(* Otherwise try direct CIC Function formalization (total by structural recursion) *)
					With[{fnRes = terminationSymbolAsFunction[heldSym, environmentSpec]},
						AssociationQ[fnRes] && fnRes["Status"] === "Terminating"
					],
						terminationSymbolAsFunction[heldSym, environmentSpec],

					(* Fall back to Rules analysis (polynomial weight / lasso / self-embedding divergence) *)
					True,
						terminationSymbolAsRules[heldSym, environmentSpec, Hold[opts]]
				]
		]
	]
]

(* Formalize symbol with "Meaning" -> "Function": if CIC accepts a TypeTheoryDefinition (not an opaque axiom), it is structurally terminating! *)
terminationSymbolAsFunction[heldSym : HoldComplete[symbol_Symbol], environmentSpec_] := Module[{env, decls, extEnv, mainDecl},
	reportProgress["Formalizing function for structural recursion check...", 0.35];
	env = If[environmentSpec === Automatic, TypeTheoryEnvironment["Integers"], resolveEnvironmentArg[environmentSpec]];
	If[ FailureQ[env],
		env,

		decls = Quiet @ catchKernelFailure[TypeTheoryFormalize[symbol, env, "Meaning" -> "Function"]];
		If[ FailureQ[decls] || ! ListQ[decls] || decls === {},
			Failure["NotTotalDefinition", <||>],

			mainDecl = Last[decls];
			If[ ! MatchQ[mainDecl, _TypeTheoryDefinition],
				Failure["FormalizedAsAxiom", <||>],

				withStoreCleanup[
					extEnv = Quiet @ TypeTheoryEnvironment[env, decls];
					If[ FailureQ[extEnv],
						extEnv,

						<|
							"Status" -> "Terminating",
							"Target" -> HoldForm[symbol],
							"Definition" -> mainDecl,
							"Proof" -> TypeTheoryCheck[extEnv],
							"Method" -> "StructuralRecursor",
							"Verified" -> True
						|>
					]
				]
			]
		]
	]
]

(* Analyze symbol as a rewrite rule system ("Meaning" -> "Rules"):
   1. Polynomial weight interpretation (M4)
   2. Concrete lasso detection (M1)
   3. Unbounded self-embedding divergence invariant (M5, e.g. g[x_] := g[x + 1]) *)
(* Strip optional HoldPattern wrapper produced by definitionStatements around LHS *)
unwrapHeldDefinition[HoldComplete[SetDelayed[Verbatim[HoldPattern][lhs_], rhs_]]] := HoldComplete[SetDelayed[lhs, rhs]]
unwrapHeldDefinition[other_] := other

terminationSymbolAsRules[heldSym : HoldComplete[symbol_Symbol], environmentSpec_, Hold[opts___]] := Module[
	{env, dvs, rulesList, weightRes, testExpr, lassoRes, selfEmbedRes},
	env = If[environmentSpec === Automatic, TypeTheoryEnvironment["Prelude"], resolveEnvironmentArg[environmentSpec]];
	If[ FailureQ[env],
		env,

		dvs = unwrapHeldDefinition /@ definitionStatements[symbol];
		rulesList = Cases[dvs, HoldComplete[SetDelayed[lhs_, rhs_]] :> HoldComplete[RuleDelayed[lhs, rhs]]];
		weightRes = certifyRewriteRulesByWeight[env, rulesList, HoldComplete[symbol]];
		If[ AssociationQ[weightRes],
			weightRes,

			(* Try concrete pointwise lasso on first LHS instantiated with 0 (capped to small steps) *)
			testExpr = Replace[First[dvs], HoldComplete[SetDelayed[lhs_, _]] :> instantiatePatternWithZero[HoldComplete[lhs]]];
			lassoRes = Replace[testExpr, HoldComplete[e_] :> terminationPointwiseSymbol[HoldComplete[e], heldSym, env, Hold["MaxSteps" -> 15, opts]]];
			If[ AssociationQ[lassoRes] && lassoRes["Status"] === "NonTerminating",
				Append[lassoRes, "Witness" -> HoldForm @@ testExpr],

				(* Try self-embedding divergence invariant (e.g. g[x_] := g[x + 1] preserves head g[_] forever!) *)
				selfEmbedRes = certifySelfEmbeddingDivergence[env, heldSym, dvs];
				If[ AssociationQ[selfEmbedRes],
					selfEmbedRes,

					<|
						"Status" -> "Undetermined",
						"Target" -> HoldForm[symbol],
						"Proof" -> None,
						"Method" -> "SearchExhausted",
						"Verified" -> False
					|>
				]
			]
		]
	]
]

(* Certify unbounded non-termination for unary self-embedding rule f[x_] := f[body[x]] (e.g. g[x_] := g[x + 1])
   in "DownValues[f]":
   Proves by induction on n : NonNegativeIntegers that Exists[{e : Expressions}, iterateDownValues[n, f[0]] == some[Construct[f, e]]],
   hence ForAll[n, Not[iterateDownValues[n, f[0]] == none]]! *)
certifySelfEmbeddingDivergence[env_, HoldComplete[symbol_Symbol], dvs_List] := Module[
	{cleanDvs = unwrapHeldDefinition /@ dvs, matchSelf, rulesDecls, dvName, iterEnv, headAtomExpr, seedExpr, invStmt, invProof, finalStmt, finalProof},
	matchSelf = SelectFirst[
		cleanDvs,
		Function[d, MatchQ[d, HoldComplete[SetDelayed[symbol[Verbatim[Pattern][_, Verbatim[Blank][]]], symbol[_]]]]],
		None
	];
	If[ matchSelf === None,
		None,

		rulesDecls = Quiet @ catchKernelFailure[TypeTheoryFormalize[symbol, env, "Meaning" -> "Rules"]];
		If[ FailureQ[rulesDecls],
			None,

			dvName = "DownValues[" <> SymbolName[Unevaluated[symbol]] <> "]";
			iterEnv = With[{dv = dvName},
				Quiet @ TypeTheoryEnvironment[env, Append[rulesDecls,
					TypeTheoryDefinition["iterateDownValues", Typed[
						Function[{Typed[n, NonNegativeIntegers], Typed[e, Expressions]},
							InductiveRecursor[NonNegativeIntegers][
								Typed[k, NonNegativeIntegers] |-> Option[Expressions],
								"some"[e],
								{Typed[k, NonNegativeIntegers], Typed[acc, Option[Expressions]]} |->
									InductiveRecursor[Option][
										Typed[o, Option[Expressions]] |-> Option[Expressions],
										Typed["none", Option[Expressions]],
										Typed[x, Expressions] |-> dv[x],
										acc
									],
								n
							]
						],
						NonNegativeIntegers -> Expressions -> Option[Expressions]
					]]
				]]
			];
			If[ FailureQ[iterEnv],
				None,

				(* Build step-preservation proof: ForAll[x : Expressions, Exists[y : Expressions, dvName[Construct[f, x]] == some[Construct[f, y]]]] *)
				With[
					{
						fAtom = Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["symbolAtom"]], stringLiteralCore[fullName[symbol]]]],
						zeroAtom = Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["naturalAtom"]], naturalLiteral[0]]],
						optExpr = Construct[application, coreConstant[HoldComplete[Option], {0}], coreConstant[HoldComplete[Expressions]]],
						noneTerm = Construct[application, coreConstant[HoldComplete["none"], {0}], coreConstant[HoldComplete[Expressions]]]
					},
					{
						mkCall = Function[arg, makeApplication[coreConstant[HoldComplete["Construct"]], {fAtom, foArgSequenceCore[{arg}]}]],
						rhsTemplate = Replace[matchSelf, HoldComplete[SetDelayed[symbol[Verbatim[Pattern][v_Symbol, _]], symbol[rhsArg_]]] :> {HoldComplete[v], HoldComplete[rhsArg]}]
					},
					{
						seedCall = mkCall[zeroAtom],
						stepImgFn = buildQuotedUnaryRhs[First[rhsTemplate], Last[rhsTemplate]]
					},
					If[ stepImgFn === $Failed,
						None,

						(* Prove ForAll[n, Exists[x : Expressions, iterateDownValues[n, f[0]] == some[f[x]]]] by induction on n! *)
						With[{nId = freshFreeVariable[], xId = freshFreeVariable[]},
							{
								ctxN = extendContext[<||>, nId, HoldComplete["n"], coreNaturals[], "Explicit"],
								ctxX = extendContext[<||>, xId, HoldComplete["x"], coreConstant[HoldComplete[Expressions]], "Explicit"]
							},
							{
								iterN = makeApplication[coreConstant[HoldComplete["iterateDownValues"]], {freeVariable[nId], seedCall}],
								someFx = makeApplication[coreConstant[HoldComplete["some"], {0}], {coreConstant[HoldComplete[Expressions]], mkCall[freeVariable[xId]]}]
							},
							{
								exBody = coreExists[coreConstant[HoldComplete[Expressions]], HoldComplete["x"], abstractFreeVariable[coreEquality[optExpr, iterN, someFx, {1}], xId], {1}]
							},
							{
								invStmtCore = makeDependentFunctionType[ctxN, {nId}, exBody],
								finalStmtCore = makeDependentFunctionType[ctxN, {nId}, coreNegation[iterEnv, coreEquality[optExpr, iterN, noneTerm, {1}]]]
							},
							invProof = proveSelfEmbeddingInvariant[iterEnv, invStmtCore, zeroAtom, stepImgFn, mkCall, optExpr];
							If[ FailureQ[invProof],
								None,

								finalProof = deriveNotNoneFromExistsInvariant[iterEnv, finalStmtCore, invProof, optExpr, noneTerm];
								If[ FailureQ[finalProof],
									None,

									<|
										"Status" -> "NonTerminating",
										"Target" -> HoldForm[symbol],
										"Witness" -> HoldForm[symbol[0]],
										"DivergenceInvariant" -> coreToTypeTheoryTerm[iterEnv, <||>, invStmtCore],
										"Statement" -> coreToTypeTheoryTerm[iterEnv, <||>, finalStmtCore],
										"Proof" -> finalProof,
										"Method" -> "SelfEmbeddingDivergenceInvariant",
										"Verified" -> True
									|>
								]
							]
						]
					]
				]
			]
		]
	]
]

buildQuotedUnaryRhs[varHeld_HoldComplete, rhsHeld_HoldComplete] := Module[{tree},
	tree = exprToFirstOrderTree[rhsHeld, {varHeld}];
	If[ tree === $Failed,
		$Failed,
		Function[argCore, foTreeToCoreWithArg[tree, varHeld, argCore]]
	]
]

foTreeToCoreWithArg[foVar[v_], v_, argCore_] := argCore
foTreeToCoreWithArg[foConst[name_String], _, _] := Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["symbolAtom"]], stringLiteralCore[name]]]
foTreeToCoreWithArg[foNat[n_Integer], _, _] := Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["naturalAtom"]], naturalLiteral[n]]]
foTreeToCoreWithArg[foApply[hName_String, args_List], v_, argCore_] := makeApplication[
	coreConstant[HoldComplete["Construct"]],
	{
		Construct[application, coreConstant[HoldComplete["atom"]], Construct[application, coreConstant[HoldComplete["symbolAtom"]], stringLiteralCore[hName]]],
		foArgSequenceCore[foTreeToCoreWithArg[#, v, argCore] & /@ args]
	}
]

proveSelfEmbeddingInvariant[env_, invStmtCore_, zeroAtom_, stepImgFn_, mkCall_, optExpr_] := Module[
	{st, indSt, d1, g1, ctx1, pred1, baseSolved, d2, g2, ctx2, ihId, xId, eqId, newG, exPred, exType, motive, minor, elimSt, d3, g3, ctx3, eqName, rewSt, d4, g4, ctx4, pred4, finalSt},
	st = newProofState[env, invStmtCore, {}];
	indSt = Quiet @ catchKernelFailure[runTactics[st, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Induction", n]}]];
	If[ FailureQ[indSt],
		indSt,

		(* Base case: witness zeroAtom, prove Reflexivity *)
		d1 = First[indSt];
		g1 = First[d1["Goals"]];
		ctx1 = currentGoal[d1, g1]["Context"];
		pred1 = Last[currentGoal[d1, g1]["Type"]];
		With[{eqG = freshMetavariableId[], eqBody = betaNormalize[Construct[application, pred1, zeroAtom]]},
			baseSolved = proofState @ solveGoal[
				d1,
				g1,
				makeApplication[coreConstant[HoldComplete["existsIntroduction"], {1}], {coreConstant[HoldComplete[Expressions]], pred1, zeroAtom, metavariable[eqG]}],
				{eqG -> <|"Context" -> ctx1, "Type" -> eqBody, "Case" -> None|>}
			];
			baseSolved = Quiet @ catchKernelFailure[TypeTheoryTactic["Reflexivity"][baseSolved]];
			If[ FailureQ[baseSolved],
				baseSolved,

				(* Inductive step: introduce k, ih; unpack ih : Exists[x, iter[k, f[0]] == some[f[x]]]; rewrite; witness stepImgFn[x]; Reflexivity! *)
				baseSolved = Quiet @ catchKernelFailure[runTactics[baseSolved, {TypeTheoryTactic["Introduce", k, ih]}]];
				If[ FailureQ[baseSolved],
					baseSolved,

					d2 = First[baseSolved];
					g2 = First[d2["Goals"]];
					ctx2 = currentGoal[d2, g2]["Context"];
					ihId = Last[Keys[ctx2]];
					exType = ctx2[ihId]["Type"];
					exPred = Last[exType];
					xId = freshFreeVariable[];
					eqId = freshFreeVariable[];
					newG = freshMetavariableId[];
					With[
						{
							xCtx = extendContext[ctx2, xId, HoldComplete["xCur"], coreConstant[HoldComplete[Expressions]], "Explicit"]
						},
						{
							eqCtx = extendContext[xCtx, eqId, HoldComplete["hCurEq"], betaNormalize[Construct[application, exPred, freeVariable[xId]]], "Explicit"]
						},
						motive = Construct[lambdaAbstraction, HoldComplete["w"], exType, liftBoundVariables[currentGoal[d2, g2]["Type"], 1, 0], "Explicit"];
						minor = pendingAbstraction[eqCtx, {xId, eqId}, metavariable[newG]];
						elimSt = proofState @ solveGoal[
							d2,
							g2,
							makeApplication[coreConstant[recursorName[HoldComplete[Exists]], {1}], {coreConstant[HoldComplete[Expressions]], exPred, motive, minor, freeVariable[ihId]}],
							{newG -> <|"Context" -> eqCtx, "Type" -> currentGoal[d2, g2]["Type"], "Case" -> None|>}
						];
						rewSt = Quiet @ catchKernelFailure[TypeTheoryTactic["Rewrite", "hCurEq"][unfoldIterStepInGoal[elimSt]]];
						If[ FailureQ[rewSt],
							rewSt,

							d4 = First[rewSt];
							g4 = First[d4["Goals"]];
							ctx4 = currentGoal[d4, g4]["Context"];
							pred4 = Last[currentGoal[d4, g4]["Type"]];
							With[{nextWitness = stepImgFn[freeVariable[xId]], eqG2 = freshMetavariableId[]},
								finalSt = proofState @ solveGoal[
									d4,
									g4,
									makeApplication[coreConstant[HoldComplete["existsIntroduction"], {1}], {coreConstant[HoldComplete[Expressions]], pred4, nextWitness, metavariable[eqG2]}],
									{eqG2 -> <|"Context" -> ctx4, "Type" -> betaNormalize[Construct[application, pred4, nextWitness]], "Case" -> None|>}
								];
								finalSt = Quiet @ catchKernelFailure[TypeTheoryTactic["Reflexivity"][finalSt]];
								verifyProofInKernel[env, invStmtCore, {}, finalSt]
							]
						]
					]
				]
			]
		]
	]
]

deriveNotNoneFromExistsInvariant[env_, finalStmtCore_, invProof_TypeTheoryProof, optExpr_, noneTerm_] := Module[
	{st, d, g, ctx, nId, invTerm = completedProofTerm[invProof], invApplied, invType, exPred, xId, eqId, newG, ctx2, motive, minor, elimSt, closed},
	st = newProofState[env, finalStmtCore, {}];
	st = Quiet @ catchKernelFailure[runTactics[st, {TypeTheoryTactic["Introduce", n, hNone]}]];
	If[ FailureQ[st],
		st,

		d = First[st];
		g = First[d["Goals"]];
		ctx = currentGoal[d, g]["Context"];
		nId = First[Keys[ctx]];
		invApplied = Construct[application, invTerm, freeVariable[nId]];
		invType = betaNormalize[inferType[env, ctx, invApplied]];
		exPred = Last[invType];
		xId = freshFreeVariable[];
		eqId = freshFreeVariable[];
		newG = freshMetavariableId[];
		With[{ctx1 = extendContext[ctx, xId, HoldComplete["xVal"], coreConstant[HoldComplete[Expressions]], "Explicit"]},
			ctx2 = extendContext[ctx1, eqId, HoldComplete["hSomeEq"], betaNormalize[Construct[application, exPred, freeVariable[xId]]], "Explicit"];
			motive = Construct[lambdaAbstraction, HoldComplete["w"], invType, liftBoundVariables[currentGoal[d, g]["Type"], 1, 0], "Explicit"];
			minor = pendingAbstraction[ctx2, {xId, eqId}, metavariable[newG]];
			elimSt = proofState @ solveGoal[
				d,
				g,
				makeApplication[coreConstant[recursorName[HoldComplete[Exists]], {1}], {coreConstant[HoldComplete[Expressions]], exPred, motive, minor, invApplied}],
				{newG -> <|"Context" -> ctx2, "Type" -> currentGoal[d, g]["Type"], "Case" -> None|>}
			];
			closed = closeSomeEqualsNoneBranch[elimSt, optExpr];
			verifyProofInKernel[env, finalStmtCore, {}, closed]
		]
	]
]


(* --- Target 4E: Integer While Loops & Recursive Functions (Farkas Ranking Functions M3, Divergence M5, Conditional M6) --- *)

(* Extract single-variable or multi-variable While loop or single-argument integer recursion from WL DownValues *)
extractIntegerLoopOrRecursion[HoldComplete[symbol_Symbol], dvs_List] := Module[{cleanDvs = unwrapHeldDefinition /@ dvs, res},
	(* Pattern 1: Single-argument integer While loop:
	   f[n_Integer] := Module[{i = init1, ...}, While[guard, updates]; ret] *)
	res = SelectFirst[cleanDvs, MatchQ[#, HoldComplete[SetDelayed[symbol[Verbatim[Pattern][_, Verbatim[Blank][Integer]]], _Module]]] &, None];
	If[ res =!= None,
		parseWhileLoopDefinition[res],

		(* Pattern 2: Single-argument integer recursion:
		   f[n_Integer] := If[baseTest, baseVal, recBody] *)
		res = SelectFirst[cleanDvs, MatchQ[#, HoldComplete[SetDelayed[symbol[Verbatim[Pattern][_, Verbatim[Blank][Integer]]], _If]]] &, None];
		If[ res =!= None,
			parseIntegerRecursionDefinition[HoldComplete[symbol], res],
			None
		]
	]
]

cleanParamName[HoldComplete[sym_Symbol]] := StringReplace[SymbolName[Unevaluated[sym]], "$" ~~ DigitCharacter ... ~~ EndOfString -> ""]

parseWhileLoopDefinition[HoldComplete[SetDelayed[_[Verbatim[Pattern][param_Symbol, _]], Module[inits_List, body_]]]] := Module[
	{initMap, whileExpr, guardHeld, loopBodyHeld, updates, varSyms, paramHeld = HoldComplete[param]},
	initMap = Association @ Cases[HoldComplete[inits], HoldPattern[Set[v_Symbol, val_]] :> (HoldComplete[v] -> HoldComplete[val]), {2}];
	whileExpr = Cases[HoldComplete[body], HoldPattern[While[g_, b_]] :> {HoldComplete[g], HoldComplete[b]}, {0, Infinity}];
	If[ whileExpr === {},
		None,

		{guardHeld, loopBodyHeld} = First[whileExpr];
		updates = extractLoopUpdates[loopBodyHeld];
		If[ updates === $Failed || updates === <||>,
			None,

			(* Find the primary loop control variable(s) mentioned in guard *)
			varSyms = Select[Keys[initMap], Function[v, ! FreeQ[guardHeld, First[v]]]];
			If[ Length[varSyms] =!= 1,
				None,

				With[{ctrlVar = First[varSyms]},
					{
						initVal = initMap[ctrlVar],
						stepVal = Lookup[updates, ctrlVar, ctrlVar]
					},
					(* Replace param -> \[FormalN] and ctrlVar -> \[FormalI] cleanly in Wolfram expressions *)
					With[
						{
							wlInit = ReplaceAll[First[initVal], {HoldPattern[param] -> \[FormalN]}],
							wlGuard = ReplaceAll[First[guardHeld], {HoldPattern[param] -> \[FormalN], HoldPattern @@ ctrlVar -> \[FormalI]}],
							wlStep = ReplaceAll[First[stepVal], {HoldPattern[param] -> \[FormalN], HoldPattern @@ ctrlVar -> \[FormalI]}]
						},
						If[ FreeQ[{wlInit, wlGuard, wlStep}, _Set | _CompoundExpression | _While | _Module],
							<|
								"Kind" -> "WhileLoop",
								"ParamName" -> cleanParamName[HoldComplete[param]],
								"StateName" -> StringReplace[nameToKey[ctrlVar], "$" ~~ DigitCharacter ... ~~ EndOfString -> ""],
								"Init" -> wlInit,
								"Guard" -> wlGuard,
								"Step" -> wlStep
							|>,
							None
						]
					]
				]
			]
		]
	]
]
parseWhileLoopDefinition[_] := None

extractLoopUpdates[HoldComplete[CompoundExpression[stmts___]]] := Module[{pairs},
	pairs = Catenate[extractSingleUpdate /@ (HoldComplete /@ Unevaluated[{stmts}])];
	If[MemberQ[pairs, $Failed], $Failed, Association[pairs]]
]
extractLoopUpdates[single_HoldComplete] := Module[{pairs = extractSingleUpdate[single]},
	If[MemberQ[pairs, $Failed], $Failed, Association[pairs]]
]

extractSingleUpdate[HoldComplete[Null]] := {}
extractSingleUpdate[HoldComplete[Set[v_Symbol, rhs_]]] := {HoldComplete[v] -> HoldComplete[rhs]}
extractSingleUpdate[HoldComplete[Increment[v_Symbol]]] := {HoldComplete[v] -> HoldComplete[v + 1]}
extractSingleUpdate[HoldComplete[Decrement[v_Symbol]]] := {HoldComplete[v] -> HoldComplete[v - 1]}
extractSingleUpdate[HoldComplete[AddTo[v_Symbol, d_]]] := {HoldComplete[v] -> HoldComplete[v + d]}
extractSingleUpdate[HoldComplete[SubtractFrom[v_Symbol, d_]]] := {HoldComplete[v] -> HoldComplete[v - d]}
extractSingleUpdate[_] := {$Failed}

parseIntegerRecursionDefinition[HoldComplete[symbol_Symbol], HoldComplete[SetDelayed[symbol_[Verbatim[Pattern][param_Symbol, _]], If[test_, base_, rec_]]]] := Module[
	{recCalls, stepArg, wlGuard, wlStep},
	recCalls = Cases[HoldComplete[rec], HoldPattern[symbol[arg_]] :> HoldComplete[arg], {0, Infinity}];
	If[ Length[recCalls] =!= 1,
		None,

		stepArg = First[recCalls];
		wlGuard = Not[ReplaceAll[test, HoldPattern[param] -> \[FormalI]]];
		wlStep = ReplaceAll[First[stepArg], HoldPattern[param] -> \[FormalI]];
		<|
			"Kind" -> "IntegerRecursion",
			"ParamName" -> cleanParamName[HoldComplete[param]],
			"StateName" -> cleanParamName[HoldComplete[param]],
			"Init" -> \[FormalN],
			"Guard" -> wlGuard,
			"Step" -> wlStep
		|>
	]
]
parseIntegerRecursionDefinition[_, _] := None


(* Analyze extracted integer loop/recursion:
   M3: Unconditional affine Farkas ranking function -> kernel-checked descent & fuel termination proof!
   M5+M6: Empirical probe -> divergence invariant + termination precondition -> kernel-checked conditional or non-termination proof! *)
analyzeIntegerLoopOrRecursion[heldSym : HoldComplete[symbol_Symbol], spec_Association, methodOpt_, maxSteps_Integer, llmEval_] := Module[
	{intsEnv, initExpr = spec["Init"], guardExpr = spec["Guard"], stepExpr = spec["Step"],
	 ranking, descentProof, termSamples, divSamples, witnessN, precondResult, divResult, llmRank},
	reportProgress["Loading Integers environment...", 0.15];
	intsEnv = TypeTheoryEnvironment["Integers"];

	(* Step 1 (M3): Try unconditional affine ranking function mu(n, i) = c0 + c1*n + c2*i *)
	ranking = If[ useHeuristicQ[methodOpt],
		reportProgress["Synthesizing Farkas affine ranking function...", 0.25];
		synthesizeAffineRankingFunction[guardExpr, stepExpr, True],
		None
	];
	If[ AssociationQ[ranking],
		reportProgress["Verifying affine ranking descent in kernel...", 0.55];
		descentProof = proveAffineRankingInKernel[intsEnv, guardExpr, stepExpr, True, ranking["Measure"]];
		If[ ! FailureQ[descentProof],
			<|
				"Status" -> "Terminating",
				"Target" -> HoldForm[symbol],
				"Measure" -> ranking["MeasureDisplay"],
				"FuelBound" -> ReplaceAll[Max[ranking["Measure"], 0] + 1, \[FormalI] -> initExpr],
				"Statement" -> descentProof["Statement"],
				"Proof" -> descentProof,
				"Method" -> "FarkasAffineRankingFunction",
				"Verified" -> True
			|>,
			analyzeConditionalOrDivergentLoop[intsEnv, heldSym, spec, maxSteps, methodOpt, llmEval]
		],

		analyzeConditionalOrDivergentLoop[intsEnv, heldSym, spec, maxSteps, methodOpt, llmEval]
	]
]

analyzeConditionalOrDivergentLoop[intsEnv_, heldSym : HoldComplete[symbol_Symbol], spec_Association, maxSteps_Integer, methodOpt_, llmEval_] := Module[
	{initExpr = spec["Init"], guardExpr = spec["Guard"], stepExpr = spec["Step"],
	 samples, termInputs, divInputs, witnessN, precond, condRanking, condProof, divInv, divProof},

	(* Probe integer inputs -6..6 to classify terminating vs diverging inputs *)
	reportProgress["Analyzing conditional termination and divergence witnesses...", 0.65];
	samples = Table[
		{k, simulateIntegerLoop[initExpr, guardExpr, stepExpr, k, Min[maxSteps, 60]]},
		{k, -6, 6}
	];
	termInputs = First /@ Select[samples, Last[#] === "Terminated" &];
	divInputs = First /@ Select[samples, Last[#] === "Diverged" &];

	If[ divInputs === {},
		(* Try LLM ranking function if enabled *)
		If[ useLLMQ[methodOpt],
			reportProgress["Querying LLMFunction for candidate ranking function...", 0.85];
			With[{llmRes = tryLLMRankingFunction[intsEnv, heldSym, spec, llmEval, remainingBudget[30]]},
				If[ AssociationQ[llmRes],
					llmRes,
					<|"Status" -> "Undetermined", "Target" -> HoldForm[symbol], "Proof" -> None, "Method" -> "SearchExhausted", "Verified" -> False|>
				]
			],
			<|"Status" -> "Undetermined", "Target" -> HoldForm[symbol], "Proof" -> None, "Method" -> "SearchExhausted", "Verified" -> False|>
		],

		witnessN = First[SortBy[divInputs, {Abs[#], If[# < 0, 1, 0]} &]];
		divInv = synthesizeDivergenceInvariant[initExpr, guardExpr, stepExpr, witnessN];
		divProof = If[ divInv =!= None,
			proveDivergenceInvariantInKernel[intsEnv, initExpr, guardExpr, stepExpr, witnessN, divInv],
			Failure["NoDivInv", <||>]
		];

		If[ termInputs === {},
			(* Purely non-terminating *)
			<|
				"Status" -> If[FailureQ[divProof], "Undetermined", "NonTerminating"],
				"Target" -> HoldForm[symbol],
				"Witness" -> <|spec["ParamName"] -> witnessN|>,
				"DivergenceInvariant" -> divInv,
				"Statement" -> If[FailureQ[divProof], None, divProof["Statement"]],
				"Proof" -> If[FailureQ[divProof], None, divProof],
				"Method" -> "DivergenceInvariant",
				"Verified" -> ! FailureQ[divProof]
			|>,

			(* Conditionally terminating: synthesize precondition A(n) and ranking function under A(n) *)
			precond = synthesizeTerminationPrecondition[initExpr, guardExpr, stepExpr, termInputs, divInputs];
			condRanking = If[ precond =!= None,
				synthesizeAffineRankingFunction[guardExpr, stepExpr, precond["StateInvariant"]],
				None
			];
			condProof = If[ AssociationQ[condRanking],
				proveAffineRankingInKernel[intsEnv, guardExpr, stepExpr, precond["StateInvariant"], condRanking["Measure"]],
				Failure["NoCondProof", <||>]
			];
			If[ ! FailureQ[condProof],
				<|
					"Status" -> "ConditionallyTerminating",
					"Target" -> HoldForm[symbol],
					"Precondition" -> precond["Display"],
					"Measure" -> condRanking["MeasureDisplay"],
					"TerminationProof" -> condProof,
					"Proof" -> condProof,
					"NonTerminationWitness" -> <|spec["ParamName"] -> witnessN|>,
					"DivergenceInvariant" -> divInv,
					"NonTerminationProof" -> If[FailureQ[divProof], None, divProof],
					"Method" -> "ConditionalRankingAndDivergence",
					"Verified" -> True
				|>,

				If[ ! FailureQ[divProof],
					<|
						"Status" -> "NonTerminating",
						"Target" -> HoldForm[symbol],
						"Witness" -> <|spec["ParamName"] -> witnessN|>,
						"DivergenceInvariant" -> divInv,
						"Proof" -> divProof,
						"Method" -> "DivergenceInvariant",
						"Verified" -> True
					|>,
					<|"Status" -> "Undetermined", "Target" -> HoldForm[symbol], "Proof" -> None, "Method" -> "SearchExhausted", "Verified" -> False|>
				]
			]
		]
	]
]

simulateIntegerLoop[initExpr_, guardExpr_, stepExpr_, nVal_Integer, maxSteps_Integer] := Module[{iVal, k = 0},
	iVal = Quiet[ReplaceAll[initExpr, \[FormalN] -> nVal]];
	If[ ! IntegerQ[iVal],
		"Unknown",
		While[ k < maxSteps && TrueQ[Quiet[ReplaceAll[guardExpr, {\[FormalN] -> nVal, \[FormalI] -> iVal}]]],
			iVal = Quiet[ReplaceAll[stepExpr, {\[FormalN] -> nVal, \[FormalI] -> iVal}]];
			If[! IntegerQ[iVal], Break[]];
			k = k + 1
		];
		If[k < maxSteps, "Terminated", "Diverged"]
	]
]

(* Farkas / quantifier-elimination synthesis of an affine ranking function mu(n, i) = c0 + c1*n + c2*i
   satisfying: inv && guard => mu(n, i) >= 0 && mu(n, step(i)) <= mu(n, i) - 1 *)
synthesizeAffineRankingFunction[guardExpr_, stepExpr_, invExpr_] := Module[
	{c0 = \[FormalA], c1 = \[FormalB], c2 = \[FormalC], mu, muNext, cond, resolved, sol, vals, measureExpr},
	mu = c0 + c1 * \[FormalN] + c2 * \[FormalI];
	muNext = ReplaceAll[mu, \[FormalI] -> stepExpr];
	cond = ForAll[{\[FormalN], \[FormalI]}, Implies[invExpr && guardExpr, mu >= 0 && muNext <= mu - 1]];
	resolved = TimeConstrained[Quiet @ Resolve[cond, Reals], 3, $Aborted];
	If[ resolved === $Aborted || resolved === False,
		None,

		sol = TimeConstrained[
			Quiet @ FindInstance[resolved && -10 <= c0 <= 10 && -5 <= c1 <= 5 && -5 <= c2 <= 5, {c0, c1, c2}, Integers],
			2,
			{}
		];
		If[ ! MatchQ[sol, {_List, ___}],
			None,

			measureExpr = Simplify[ReplaceAll[mu, First[sol]]];
			<|
				"Measure" -> measureExpr,
				"MeasureDisplay" -> ReplaceAll[measureExpr, {\[FormalN] -> "n", \[FormalI] -> "i"}]
			|>
		]
	]
]

(* Kernel-prove the descent theorem in TypeTheoryEnvironment["Integers"]:
   ForAll[{Typed[n, Integers], Typed[i, Integers]}, Implies[inv && guard, 0 <= mu[n, i] && mu[n, step[i]] < mu[n, i]]] *)
proveAffineRankingInKernel[intsEnv_, guardExpr_, stepExpr_, invExpr_, measureExpr_] := Module[
	{nId, iId, ctx, symMap, guardCore, invCore, muCore, muNextCore, nonNegCore, decCore, p1, p2},
	nId = freshFreeVariable[];
	iId = freshFreeVariable[];
	ctx = extendContext[extendContext[<||>, nId, HoldComplete["n"], coreIntegers[], "Explicit"], iId, HoldComplete["i"], coreIntegers[], "Explicit"];
	symMap = Association[\[FormalN] -> nId, \[FormalI] -> iId];
	guardCore = wlCondToCoreIn[intsEnv, symMap, Integers, normalizeIntegerGuard[guardExpr]];
	invCore = If[invExpr === True, coreTrue[], wlCondToCoreIn[intsEnv, symMap, Integers, normalizeIntegerGuard[invExpr]]];
	muCore = wlExprToCoreIn[intsEnv, symMap, Integers, Expand[measureExpr]];
	muNextCore = wlExprToCoreIn[intsEnv, symMap, Integers, Expand[ReplaceAll[measureExpr, \[FormalI] -> stepExpr]]];
	If[ MemberQ[{guardCore, invCore, muCore, muNextCore}, $Failed],
		Failure["UntranslatableLoop", <||>],

		nonNegCore = coreIntegerLessEqual[coreIntegerLiteral[0], muCore];
		decCore = coreIntegerLess[muNextCore, muCore];
		(* Prove nonNeg and dec separately, then combine with andIntroduction into one kernel-checked theorem! *)
		With[
			{
				hypWrap = Function[concl,
					If[ invExpr === True,
						makeDependentFunctionType[ctx, {nId, iId}, coreImplication[guardCore, concl]],
						makeDependentFunctionType[ctx, {nId, iId}, coreImplication[invCore, coreImplication[guardCore, concl]]]
					]
				]
			},
			{
				stmt1 = hypWrap[nonNegCore],
				stmt2 = hypWrap[decCore],
				combinedStmt = hypWrap[coreConjunction[nonNegCore, decCore]]
			},
			p1 = proveIntegerImplicationGuard[intsEnv, stmt1];
			p2 = proveIntegerImplicationGuard[intsEnv, stmt2];
			If[ FailureQ[p1] || FailureQ[p2],
				Failure["RankingProofFailed", <||>],

				(* Combine p1 and p2 into a single kernel-checked proof of combinedStmt! *)
				combineTwoImplicationProofs[intsEnv, combinedStmt, p1, p2, nonNegCore, decCore, invExpr =!= True]
			]
		]
	]
]

normalizeIntegerGuard[Not[a_ == b_]] := (a != b)
normalizeIntegerGuard[a_ > b_] := (b < a)
normalizeIntegerGuard[a_ >= b_] := (b <= a)
normalizeIntegerGuard[And[a_, b__]] := And @@ (normalizeIntegerGuard /@ {a, b})
normalizeIntegerGuard[other_] := other

(* Prove ForAll[n, i, (inv =>) guard => ineq] in Integers, unpacking conjunctions in guard/inv and handling != via case-split or direct integer linear arithmetic *)
proveIntegerImplicationGuard[intsEnv_, stmtCore_] := Module[{st, intro, unpacked, closed},
	st = newProofState[intsEnv, stmtCore, {}];
	intro = introduceAll[st];
	unpacked = Quiet @ catchKernelFailure[unpackConjunctionHypotheses[intro]];
	If[FailureQ[unpacked], unpacked = intro];
	closed = Quiet @ catchKernelFailure[proveIntegerLinearInState[unpacked]];
	If[ ! FailureQ[closed] && closed["Goals"] === {},
		verifyProofInKernel[intsEnv, stmtCore, {}, closed],
		(* Also try if guard is i != 0 and inv is 0 <= i -> in fact 0 <= i && i != 0 implies 1 <= i! *)
		closed = Quiet @ catchKernelFailure[proveIntegerLinearWithDisequality[unpacked]];
		verifyProofInKernel[intsEnv, stmtCore, {}, closed]
	]
]

(* Handle hypotheses containing both integerLessEqual[0, i] and Not[i == 0]: unpack 0 <= i into i == 0 + k, Cases on k : ℕ!
   k = 0 gives i == 0 (contradicting Not[i == 0]); k = m + 1 gives i == m + 1 (so 1 <= i)! *)
proveIntegerLinearWithDisequality[proof_TypeTheoryProof] := Module[
	{d = First[proof], g, ctx, env, neqId, targetVar, leId, unpacked, kId, eqId, splitSt, closed},
	g = First[d["Goals"]];
	ctx = currentGoal[d, g]["Context"];
	env = d["Environment"];
	neqId = SelectFirst[Keys[ctx], Function[id, MatchQ[
		weakHeadNormalForm[env, ctx, ctx[id]["Type"]],
		dependentFunctionType[_, application[application[application[constantReference[HoldComplete[Equal], _], _], freeVariable[_]], _], constantReference[HoldComplete[False], _], _]
	]], None];
	If[ neqId === None,
		Failure["NoDisequality", <||>],

		(* Unpack all integer inequalities first, then Cases on the first slack natural variable k *)
		With[{goalInfo = extractIntegerOrderGoal[env, ctx, currentGoal[d, g]["Type"]]},
			If[ ! MatchQ[goalInfo, {_, _, _}],
				Failure["NotOrderGoal", <||>],

				With[{intIneqIds = Select[Keys[ctx], Function[id, MatchQ[extractIntegerOrderGoal[env, ctx, ctx[id]["Type"]], {_, _, _}]]]},
					If[ intIneqIds === {},
						Failure["NoIntIneq", <||>],

						With[{unpackedPair = unpackOneIntegerIneq[proof, First[intIneqIds], {}]},
							{st1 = First[unpackedPair], sl = Last[unpackedPair]},
							If[ FailureQ[st1] || sl === {},
								Failure["UnpackFailed", <||>],

								kId = First[First[sl]];
								With[{kName = currentGoal[First[st1], First[First[st1]["Goals"]]]["Context"][kId]["Name"]},
									splitSt = Quiet @ catchKernelFailure[Replace[kName, HoldComplete[sym_] :> TypeTheoryTactic["Cases", sym][st1]]];
									If[ FailureQ[splitSt],
										splitSt,

										(* Branch 1 (k = 0): derive contradiction from eq : i == 0 + 0 and neq : i != 0!
										   Branch 2 (k = m + 1): prove goal by proveIntegerLinearInState! *)
										closeAllGoalsWith[splitSt, Function[cur,
											With[{sub = introduceAll[cur]},
												With[{res1 = Quiet @ catchKernelFailure[proveIntegerLinearInState[sub]]},
													If[ ! FailureQ[res1] && res1["Goals"] === {},
														res1,
														closeDisequalityZeroBranch[sub, neqId]
													]
												]
											]
										]]
									]
								]
							]
						]
					]
				]
			]
		]
	]
]

closeDisequalityZeroBranch[proof_TypeTheoryProof, neqId_Integer] := Module[{d = First[proof], g, ctx, env, eqTarget, eqGoalId, stepSt, closed},
	g = First[d["Goals"]];
	ctx = currentGoal[d, g]["Context"];
	env = d["Environment"];
	eqTarget = Replace[weakHeadNormalForm[env, ctx, ctx[neqId]["Type"]], dependentFunctionType[_, lhs_, _, _] :> lhs, _ :> None];
	If[ eqTarget === None,
		Failure["NoNeqTarget", <||>],

		eqGoalId = freshMetavariableId[];
		stepSt = proofState @ solveGoal[
			d,
			g,
			makeApplication[coreConstant[HoldComplete["falseElimination"]], {currentGoal[d, g]["Type"], Construct[application, freeVariable[neqId], metavariable[eqGoalId]]}],
			{eqGoalId -> <|"Context" -> ctx, "Type" -> eqTarget, "Case" -> None|>}
		];
		closed = Quiet @ catchKernelFailure[TypeTheoryTactic["PolynomialReduce"][stepSt]];
		If[! FailureQ[closed] && closed["Goals"] === {}, closed, Quiet @ catchKernelFailure[TypeTheoryTactic["Ring"][stepSt]]]
	]
]

combineTwoImplicationProofs[env_, combinedStmt_, p1_TypeTheoryProof, p2_TypeTheoryProof, _, _, _] := Module[
	{st, intro, d, g, cur, ctx, ids, goalAnd, leftC, rightC, t1 = completedProofTerm[p1], t2 = completedProofTerm[p2], applied1, applied2, conjTerm, solved},
	st = newProofState[env, combinedStmt, {}];
	intro = introduceAll[st];
	d = First[intro];
	g = First[d["Goals"]];
	cur = currentGoal[d, g];
	ctx = cur["Context"];
	ids = Keys[ctx];
	goalAnd = weakHeadNormalForm[env, ctx, cur["Type"]];
	leftC = Last[First[goalAnd]];
	rightC = Last[goalAnd];
	applied1 = makeApplication[t1, freeVariable /@ ids];
	applied2 = makeApplication[t2, freeVariable /@ ids];
	conjTerm = makeApplication[coreConstant[HoldComplete["andIntroduction"]], {leftC, rightC, applied1, applied2}];
	solved = proofState @ solveGoal[d, g, conjTerm, {}];
	verifyProofInKernel[env, combinedStmt, {}, solved]
]

(* Synthesize a divergence invariant I(n, i) satisfied at init(witnessN), implying guard, and preserved by step *)
synthesizeDivergenceInvariant[initExpr_, guardExpr_, stepExpr_, witnessN_Integer] := Module[{candidates, initVal},
	initVal = Quiet[ReplaceAll[initExpr, \[FormalN] -> witnessN]];
	candidates = {
		\[FormalI] <= -1,
		\[FormalI] <= initVal,
		\[FormalI] >= 1,
		\[FormalI] >= initVal,
		\[FormalI] >= \[FormalN] && \[FormalI] >= 1,
		\[FormalI] <= \[FormalN] && \[FormalI] <= -1
	};
	SelectFirst[
		candidates,
		Function[inv,
			TrueQ[Quiet[ReplaceAll[inv, {\[FormalN] -> witnessN, \[FormalI] -> initVal}]]] &&
			TrueQ[TimeConstrained[Quiet @ Resolve[ForAll[{\[FormalI]}, Implies[ReplaceAll[inv, \[FormalN] -> witnessN], ReplaceAll[guardExpr, \[FormalN] -> witnessN] && ReplaceAll[inv, {\[FormalN] -> witnessN, \[FormalI] -> ReplaceAll[stepExpr, \[FormalN] -> witnessN]}]]], Integers], 1.5, False]]
		],
		None
	]
]

(* Kernel-prove the divergence invariant at witnessN:
   I(init(witnessN)) && ForAll[i : Integers, I(i) => (guard(i) && I(step(i)))]! *)
proveDivergenceInvariantInKernel[intsEnv_, initExpr_, guardExpr_, stepExpr_, witnessN_Integer, invExpr_] := Module[
	{initVal, invInst, guardInst, stepInst, iId, ctx, revMap, invCore, guardCore, invStepCore, initInvCore, pInit, pStep, pGuard, combined},
	initVal = Quiet[ReplaceAll[initExpr, \[FormalN] -> witnessN]];
	invInst = ReplaceAll[invExpr, \[FormalN] -> witnessN];
	guardInst = ReplaceAll[guardExpr, \[FormalN] -> witnessN];
	stepInst = ReplaceAll[stepExpr, \[FormalN] -> witnessN];
	iId = freshFreeVariable[];
	ctx = extendContext[<||>, iId, HoldComplete["i"], coreIntegers[], "Explicit"];
	revMap = Association[\[FormalI] -> iId];
	initInvCore = wlCondToCoreIn[intsEnv, <||>, Integers, normalizeIntegerGuard[ReplaceAll[invInst, \[FormalI] -> initVal]]];
	invCore = wlCondToCoreIn[intsEnv, revMap, Integers, normalizeIntegerGuard[invInst]];
	invStepCore = wlCondToCoreIn[intsEnv, revMap, Integers, normalizeIntegerGuard[ReplaceAll[invInst, \[FormalI] -> stepInst]]];
	guardCore = wlCondToCoreIn[intsEnv, revMap, Integers, normalizeIntegerGuard[guardInst]];
	If[ MemberQ[{initInvCore, invCore, invStepCore, guardCore}, $Failed],
		Failure["UntranslatableDivergence", <||>],

		With[
			{
				stepStmt = makeDependentFunctionType[ctx, {iId}, coreImplication[invCore, invStepCore]],
				guardStmt = makeDependentFunctionType[ctx, {iId}, coreImplication[invCore, guardCore]]
			},
			pInit = enhancedProveCore[intsEnv, initInvCore, {}, 1.5];
			pStep = proveIntegerImplicationGuard[intsEnv, stepStmt];
			pGuard = proveIntegerImplicationGuard[intsEnv, guardStmt];
			(* Even if guard is i != 0 (not an order inequality), prove i <= -1 => i != 0! *)
			If[ FailureQ[pGuard],
				pGuard = proveIntegerOrderImpliesDisequality[intsEnv, guardStmt]
			];
			If[ FailureQ[pInit] || FailureQ[pStep] || FailureQ[pGuard],
				Failure["DivergenceProofFailed", <||>],

				(* Package into a single kernel-checked theorem: I(init) && (ForAll[i, I(i) => guard(i)] && ForAll[i, I(i) => I(step(i))]) *)
				With[
					{
						rightConj = coreConjunction[guardStmt, stepStmt],
						fullStmt = coreConjunction[initInvCore, coreConjunction[guardStmt, stepStmt]],
						st = newProofState[intsEnv, coreConjunction[initInvCore, coreConjunction[guardStmt, stepStmt]], {}]
					},
					{
						proofTerm = makeApplication[
							coreConstant[HoldComplete["andIntroduction"]],
							{
								initInvCore,
								rightConj,
								completedProofTerm[pInit],
								makeApplication[coreConstant[HoldComplete["andIntroduction"]], {guardStmt, stepStmt, completedProofTerm[pGuard], completedProofTerm[pStep]}]
							}
						]
					},
					verifyProofInKernel[intsEnv, fullStmt, {}, proofState @ solveGoal[First[st], First[First[st]["Goals"]], proofTerm, {}]]
				]
			]
		]
	]
]

(* Prove ForAll[i, i <= -1 => i != 0] or ForAll[i, 1 <= i => i != 0] in Integers *)
proveIntegerOrderImpliesDisequality[intsEnv_, stmtCore_] := Module[{st, intro, rew, d2, g2, ctx2, closedHyp, closed},
	st = newProofState[intsEnv, stmtCore, {}];
	(* Introduce with distinct explicit names so Rewrite ... "At" -> hLe unambiguously targets the order hypothesis! *)
	intro = Quiet @ catchKernelFailure[runTactics[st, {TypeTheoryTactic["Introduce", "iVal", "hOrder", "hEq"]}]];
	If[ FailureQ[intro],
		intro,

		rew = Quiet @ catchKernelFailure[TypeTheoryTactic["Rewrite", "hEq", "At" -> "hOrder"][intro]];
		If[ FailureQ[rew],
			Failure["RewriteAtFailed", <||>],

			d2 = First[rew];
			g2 = First[d2["Goals"]];
			ctx2 = currentGoal[d2, g2]["Context"];
			closedHyp = SelectFirst[Keys[ctx2], Function[id,
				! FailureQ[proveFromCore[intsEnv, coreNegation[intsEnv, ctx2[id]["Type"]], {}, {TypeTheoryTactic["Decide"]}]]
			], None];
			If[ closedHyp === None,
				Failure["NotContradictory", <||>],

				With[{negProof = proveFromCore[intsEnv, coreNegation[intsEnv, ctx2[closedHyp]["Type"]], {}, {TypeTheoryTactic["Decide"]}]},
					closed = proofState @ solveGoal[d2, g2, Construct[application, completedProofTerm[negProof], freeVariable[closedHyp]], {}];
					verifyProofInKernel[intsEnv, stmtCore, {}, closed]
				]
			]
		]
	]
]

(* Synthesize a clean termination precondition A(n) separating terminating inputs from diverging inputs *)
synthesizeTerminationPrecondition[initExpr_, guardExpr_, stepExpr_, termInputs_List, divInputs_List] := Module[{minTerm, maxTerm, candidates},
	minTerm = Min[termInputs];
	maxTerm = Max[termInputs];
	candidates = {
		<|"ParamCond" -> (0 <= \[FormalN]), "StateInvariant" -> (0 <= \[FormalI]), "Display" -> "0 <= n"|>,
		<|"ParamCond" -> (\[FormalN] <= 0), "StateInvariant" -> (\[FormalI] <= 0), "Display" -> "n <= 0"|>,
		<|"ParamCond" -> (1 <= \[FormalN]), "StateInvariant" -> (1 <= \[FormalI]), "Display" -> "1 <= n"|>,
		<|"ParamCond" -> (minTerm <= \[FormalN]), "StateInvariant" -> (minTerm <= \[FormalI]), "Display" -> ToString[minTerm] <> " <= n"|>
	};
	SelectFirst[
		candidates,
		Function[c,
			AllTrue[termInputs, Function[k, TrueQ[Quiet[ReplaceAll[c["ParamCond"], \[FormalN] -> k]]]]] &&
			AllTrue[divInputs, Function[k, ! TrueQ[Quiet[ReplaceAll[c["ParamCond"], \[FormalN] -> k]]]]]
		],
		None
	]
]


(* ::Section:: *)
(*Optional LLMFunction Integration (Strictly Untrusted Candidate Generator)*)


(* Readable Wolfram Language input string for a TypeTheoryTerm (never dumps internal Association guts). *)
termToPromptString[term_TypeTheoryTerm] := With[{expr = Quiet[TypeTheoryExpression[term]]},
	If[ FailureQ[expr] || MatchQ[expr, _TypeTheoryExpression],
		ToString[term, InputForm],
		ToString[expr, InputForm]
	]
]

$standardPromptConstants = {
	HoldComplete[Equal], HoldComplete[Unequal], HoldComplete[Plus], HoldComplete[Times], HoldComplete[Power], HoldComplete[Subtract],
	HoldComplete[LessEqual], HoldComplete[Less], HoldComplete[GreaterEqual], HoldComplete[Greater],
	HoldComplete[And], HoldComplete[Or], HoldComplete[Not], HoldComplete[Implies], HoldComplete[Equivalent],
	HoldComplete[True], HoldComplete[False], HoldComplete[Exists], HoldComplete[NonNegativeIntegers], HoldComplete[Integers],
	HoldComplete[Rationals], HoldComplete[Booleans], HoldComplete[List], HoldComplete[Option], HoldComplete[Expressions],
	HoldComplete["zero"], HoldComplete["successor"], HoldComplete["{}"], HoldComplete["Prepend"],
	HoldComplete["true"], HoldComplete["false"], HoldComplete["none"], HoldComplete["some"],
	HoldComplete[Join], HoldComplete[Length], HoldComplete[Map], HoldComplete[Reverse], HoldComplete[Append]
}

(* Summarize user-declared / non-core constants referenced in coreStmt (and recent user declarations) so the LLM knows what can be unfolded or used. *)
environmentUserContextForPrompt[environment_, coreStmt_] := Module[{libStore, baseNames, allNames, userNames, refNames, names, lines},
	libStore = If[ MatchQ[environment, TypeTheoryEnvironment[_Symbol]],
		First[environment]["Library"],
		None
	];
	baseNames = If[ MatchQ[libStore, _Symbol] && environmentQ[TypeTheoryEnvironment[libStore]] && environmentCount[TypeTheoryEnvironment[libStore]] <= 50000,
		environmentNames[TypeTheoryEnvironment[libStore]],
		{}
	];
	allNames = If[environmentCount[environment] <= 50000, environmentNames[environment], {}];
	userNames = Select[
		Complement[allNames, baseNames],
		Function[n, constantDeclaredQ[environment, n] && ! MemberQ[$standardPromptConstants, n]]
	];
	refNames = Select[
		Cases[coreStmt, constantReference[name_HoldComplete, _] :> name, Infinity],
		Function[n, constantDeclaredQ[environment, n] && ! MemberQ[$standardPromptConstants, n]]
	];
	names = DeleteDuplicates[Join[refNames, Take[userNames, -Min[6, Length[userNames]]]]];
	If[ names === {},
		"",
		lines = Function[n,
			With[{rec = constantRecord[environment, n]},
				With[
					{
						typeTerm = If[ AssociationQ[rec] && Lookup[rec, "Type", None] =!= None,
							termToPromptString[coreToTypeTheoryTerm[environment, <||>, rec["Type"]]],
							"Unknown"
						],
						hint = If[ AssociationQ[rec] && Lookup[rec, "Kind", ""] === "Definition",
							" (definition; unfold with \"RewriteRepeated\"[" <> nameToKey[n] <> "])",
							" (" <> ToLowerCase[Lookup[rec, "Kind", "constant"]] <> ")"
						]
					},
					"- " <> nameToKey[n] <> " : " <> typeTerm <> hint
				]
			]
		] /@ Take[names, UpTo[8]];
		"Relevant constants in environment:\n" <> StringRiffle[lines, "\n"] <> "\n"
	]
]

(* Resolve LLMEvaluator option: Automatic uses Wolfram AI's default model; a String adds prompt guidance. *)
resolveLLMEvaluator[Automatic] := Automatic
resolveLLMEvaluator[guidance_String] := LLMConfiguration[<|"Prompts" -> guidance|>]
resolveLLMEvaluator[eval_] := eval

(* Build an LLMFunction with optional custom LLMEvaluator; returns {} if LLM functionality is unavailable. *)
invokeLLMCandidates[prompt_String, llmEval_, timeLimit_ : 30] := Module[{resolvedEval, fn, raw},
	If[ ! NameQ["System`LLMFunction"],
		{},

		resolvedEval = resolveLLMEvaluator[llmEval];
		fn = Quiet[
			If[ resolvedEval === Automatic,
				LLMFunction[prompt],
				LLMFunction[prompt, LLMEvaluator -> resolvedEval]
			]
		];
		If[ FailureQ[fn] || ! MatchQ[fn, _LLMFunction],
			{},

			raw = CheckAbort[TimeConstrained[Quiet[fn[]], Max[25, timeLimit], $Aborted], $Aborted];
			If[ StringQ[raw],
				parseLLMWolframExpressions[raw],
				{}
			]
		]
	]
]

(* Extract candidate WL expressions (one per line or fenced code block) as HoldComplete expressions without evaluating them! *)
parseLLMWolframExpressions[text_String] := Module[{unwrapped, lines, parsedLines, blockExprs},
	unwrapped = StringReplace[text, {
		"```" ~~ LetterCharacter ... ~~ "\n" -> "\n",
		"```" -> ""
	}];
	lines = Select[
		StringTrim /@ StringSplit[unwrapped, "\n"],
		Function[line, line =!= "" && ! StringStartsQ[line, "#" | "(*" | "//"]]
	];
	parsedLines = DeleteCases[
		Function[line,
			With[
				{
					cleaned = StringTrim @ StringReplace[
						line,
						{
							StartOfString ~~ (DigitCharacter .. ~~ ("." | ")") | "-" | "*") ~~ Whitespace -> "",
							StartOfString ~~ "`" -> "",
							"`" ~~ EndOfString -> "",
							";" ~~ EndOfString -> ""
						}
					]
				},
				Quiet @ Check[ToExpression[cleaned, InputForm, HoldComplete], None]
			]
		] /@ Take[lines, UpTo[12]],
		None | $Failed
	];
	(* Also try parsing fenced blocks or the whole text as a single multi-line WL expression if line parsing missed it *)
	blockExprs = DeleteCases[
		Quiet @ Check[ToExpression[#, InputForm, HoldComplete], None] & /@
			StringCases[text, "```" ~~ LetterCharacter ... ~~ "\n" ~~ Shortest[body__] ~~ "```" :> StringTrim[body]],
		None | $Failed
	];
	DeleteDuplicates[Join[parsedLines, blockExprs]]
]

(* Run an LLM-proposed tactic list safely; if a few easy subgoals remain, try Automatic on them before kernel verification. *)
runLLMTacticCandidate[environment_, coreStmt_, uParams_List, surfaceTerm_, HoldComplete[tactics_List]] := Module[{proof, safety = 0},
	proof = Quiet @ catchKernelFailure[TypeTheoryProof[surfaceTerm, tactics]];
	If[ MatchQ[proof, _TypeTheoryProof] && proof["Goals"] =!= {},
		While[ MatchQ[proof, _TypeTheoryProof] && proof["Goals"] =!= {} && safety < 6,
			safety++;
			With[{next = Quiet @ catchKernelFailure[TypeTheoryTactic[Automatic][proof]]},
				If[ MatchQ[next, _TypeTheoryProof] && Length[next["Goals"]] < Length[proof["Goals"]],
					proof = next,
					Break[]
				]
			]
		]
	];
	verifyProofInKernel[environment, coreStmt, uParams, proof]
]
runLLMTacticCandidate[___] := Failure["InvalidCandidate", <||>]

tryLLMDetermination[environment_, coreStmt_, negStmt_, uParams_List, surfaceTerm_, compDecidable_, llmEval_, timeLimit_ : 30] := Module[
	{prompt, exprs, result = None, ctxInfo},
	ctxInfo = environmentUserContextForPrompt[environment, coreStmt];
	prompt = StringJoin[
		"You are assisting a dependent type theory theorem prover (WolframInstitute`TypeTheory`).\n",
		"Proposition: ", termToPromptString[surfaceTerm], "\n",
		ctxInfo,
		"Available tactics (written as Wolfram Language expressions inside a List):\n",
		"- \"Introduce\"[x, y, ...] : introduce universal variables or hypotheses\n",
		"- \"Induction\"[n] : structural induction on NonNegativeIntegers (creates 2 goals: base 0, then successor with k and ih introduced via \"Introduce\"[k, ih]) or List (base {}, then \"Introduce\"[x, rest, ih])\n",
		"- \"Cases\"[x] : case split\n",
		"- \"RewriteRepeated\"[f, g, ...] : unfold definitions or rewrite with hypotheses (automatically closes a goal if both sides become identical!)\n",
		"- \"Rewrite\"[h] : rewrite with equality hypothesis h\n",
		"- \"Reflexivity\", \"Assumption\", \"Decide\", \"Ring\", \"PolynomialReduce\", \"LinearArithmetic\", \"NonlinearArithmetic\", \"SumOfSquares\", \"FindEquationalProof\", \"Witness\", \"Classical\", Automatic\n",
		"Example for recursive natural number proof: {\"Introduce\"[n], \"Induction\"[n], \"RewriteRepeated\"[f], \"Introduce\"[k, ih], \"RewriteRepeated\"[f], \"PolynomialReduce\"}\n",
		"Example for list induction proof: {\"Introduce\"[a, b], \"Induction\"[a], \"RewriteRepeated\"[f, Join], \"Ring\", \"Introduce\"[x, rest, ih], \"RewriteRepeated\"[f, Join, ih], \"Ring\"}\n",
		"Return 3 to 5 candidate Wolfram Language tactic lists, one complete List per line, valid InputForm, no commentary or numbering."
	];
	exprs = invokeLLMCandidates[prompt, llmEval, timeLimit];
	Scan[
		Function[heldExpr,
			If[ result === None && MatchQ[heldExpr, HoldComplete[_List]],
				With[{ver = runLLMTacticCandidate[environment, coreStmt, uParams, surfaceTerm, heldExpr]},
					If[ ! FailureQ[ver],
						result = determineResult[
							"Proved",
							surfaceTerm,
							ver,
							None,
							None,
							None,
							compDecidable,
							"LLMVerified",
							<|"Tactics" -> Replace[heldExpr, HoldComplete[t_] :> HoldForm[t]]|>
						]
					]
				]
			]
		],
		exprs
	];
	result
]

abduceViaLLM[environment_, coreStmt_, varContext_, varIds_List, bodyCore_, uParams_List, llmEval_, timeLimit_ : 30] := Module[
	{prompt, exprs, scope, results = {}, ctxInfo, varSummary},
	ctxInfo = environmentUserContextForPrompt[environment, coreStmt];
	varSummary = StringRiffle[
		KeyValueMap[
			Function[{id, e}, nameToKey[e["Name"]] <> " : " <> termToPromptString[coreToTypeTheoryTerm[environment, <||>, e["Type"]]]],
			varContext
		],
		", "
	];
	prompt = StringJoin[
		"You are proposing sensible, non-vacuous, non-trivial missing assumptions for an unprovable proposition in WolframInstitute`TypeTheory`.\n",
		"Proposition: ", termToPromptString[coreToTypeTheoryTerm[environment, <||>, coreStmt]], "\n",
		ctxInfo,
		If[ varSummary =!= "", "Bound variables in scope: " <> varSummary <> "\n", "" ],
		"Use valid Wolfram Language TypeTheory surface syntax:\n",
		"- Local guard over bound variables (e.g. b <= a, c != 0, 4 <= n)\n",
		"- Or closed global proposition (e.g. ForAll[{Typed[x, NonNegativeIntegers]}, g[g[x]] == x] or ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]])\n",
		"- Connectives: ForAll, Exists, Implies, And, Or, Not, ==, !=, <=, <, NonNegativeIntegers, Integers, TypeUniverse[0]\n",
		"Return 3 to 5 sensible candidate assumptions, one per line, valid InputForm. Never return False, True, or the proposition itself. No commentary or numbering."
	];
	exprs = invokeLLMCandidates[prompt, llmEval, timeLimit];
	scope = contextScope[varContext];
	Scan[
		Function[heldExpr,
			(* Closed global propositions elaborate without local variables; open guards elaborate in varContext *)
			With[{globalElab = Quiet @ catchKernelFailure[elaborateClosedTerm[environment, heldExpr, universeSort[0], uParams]]},
				If[ ! FailureQ[globalElab] && ListQ[globalElab],
					AppendTo[results, <|"Scope" -> "Global", "CoreAssumption" -> First[globalElab], "Method" -> "LLM"|>],

					With[{localElab = Quiet @ catchKernelFailure[elaborateInContext[environment, varContext, scope, heldExpr, universeSort[0]]]},
						If[ ! FailureQ[localElab] && ListQ[localElab],
							AppendTo[results, <|"Scope" -> "Local", "CoreAssumption" -> First[localElab], "Method" -> "LLM"|>]
						]
					]
				]
			]
		],
		exprs
	];
	results
]

deriveConsequencesViaLLM[environment_, coreStmt_, uParams_List, llmEval_, timeLimit_ : 30] := Module[
	{prompt, exprs, results = {}, ctxInfo},
	ctxInfo = environmentUserContextForPrompt[environment, coreStmt];
	prompt = StringJoin[
		"You are proposing sensible, non-trivial mathematical consequences of an assumed proposition in WolframInstitute`TypeTheory`.\n",
		"Assumed proposition: ", termToPromptString[coreToTypeTheoryTerm[environment, <||>, coreStmt]], "\n",
		ctxInfo,
		"Use valid Wolfram Language TypeTheory surface syntax: ForAll[{Typed[x, NonNegativeIntegers]}, ...], Exists[{Typed[x, NonNegativeIntegers]}, ...], Implies[a, b], And[a, b], Or[a, b], Not[a], ==, !=, <=, <, NonNegativeIntegers, Integers, TypeUniverse[0].\n",
		"Return 3 to 5 sensible, provable, non-trivial consequence propositions, one per line, valid InputForm. Avoid True, the proposition itself, or trivial disjunctions. No commentary or numbering."
	];
	exprs = invokeLLMCandidates[prompt, llmEval, timeLimit];
	Scan[
		Function[heldExpr,
			With[{elab = Quiet @ catchKernelFailure[elaborateClosedTerm[environment, heldExpr, universeSort[0], uParams]]},
				If[ ! FailureQ[elab] && ListQ[elab],
					AppendTo[results, <|"CoreConsequence" -> First[elab], "Method" -> "LLM"|>]
				]
			]
		],
		exprs
	];
	results
]

tryLLMRankingFunction[intsEnv_, HoldComplete[symbol_Symbol], spec_Association, llmEval_, timeLimit_ : 30] := Module[{prompt, exprs, result = None},
	prompt = StringJoin[
		"Propose a candidate integer ranking function mu(n, i) (in terms of variables n and i) proving termination of this loop:\n",
		"Init: i = ", ToString[ReplaceAll[spec["Init"], \[FormalN] -> n], InputForm], "\n",
		"Guard: ", ToString[ReplaceAll[spec["Guard"], {\[FormalN] -> n, \[FormalI] -> i}], InputForm], "\n",
		"Step: i = ", ToString[ReplaceAll[spec["Step"], {\[FormalN] -> n, \[FormalI] -> i}], InputForm], "\n",
		"Return 1 to 3 linear integer expressions in n and i (one per line, e.g. n - i + 1). No commentary or numbering."
	];
	exprs = invokeLLMCandidates[prompt, llmEval, timeLimit];
	Scan[
		Function[heldExpr,
			If[ result === None,
				With[{mu = Replace[heldExpr, HoldComplete[e_] :> ReplaceAll[e, {Global`n -> \[FormalN], Global`i -> \[FormalI]}]]},
					With[{proof = proveAffineRankingInKernel[intsEnv, spec["Guard"], spec["Step"], True, mu]},
						If[ ! FailureQ[proof],
							result = <|
								"Status" -> "Terminating",
								"Target" -> HoldForm[symbol],
								"Measure" -> ReplaceAll[mu, {\[FormalN] -> "n", \[FormalI] -> "i"}],
								"Statement" -> proof["Statement"],
								"Proof" -> proof,
								"Method" -> "LLMRankingFunctionVerified",
								"Verified" -> True
							|>
						]
					]
				]
			]
		],
		exprs
	];
	result
]
