(* ::Package:: *)

(*
Proofs: a proof state with goals, and tactics that refine it.

A proof state holds a partial proof term with holes. Each hole is a metavariable, an open goal with a
local context and a type. A tactic works on the first goal: it assigns the goal's metavariable a term,
which may contain new metavariables, the new goals. A proof with no goals left is finished. Its term is
checked by the kernel when it is declared, so a tactic cannot make a false statement pass: at worst it
fails, or leaves goals open.

	TypeTheoryProof[<|
		"Environment" -> environment,
		"Statement" -> statement,                       the core statement
		"UniverseParameters" -> {HoldComplete[u], ...},
		"Root" -> id,                                   the metavariable of the whole proof
		"Goals" -> {id, ...},                           the open goals, first goal first
		"Metavariables" -> <|id -> <|"Context" -> context, "Type" -> type, "Case" -> None | HoldComplete[name]|>, ...|>,
		"Assignments" -> <|id -> term, ...|>
	|>]

A function introduced by a tactic is recorded as pendingAbstraction[context, {id, ...}, body], the
function of the free variables id, ... of body. It is abstracted only once body has no metavariables
left, since their solutions may mention those variables.

The tactics:

	"Introduce", x, ...     x : A |- B for a goal ForAll[{Typed[x, A]}, B] or A -> B, unfolding definitions to find it
	"Exact", term           solves the goal with term
	"Apply", term           solves the goal with term applied to as many new goals as its conclusion needs
	"Reflexivity"           solves a goal a == b whose sides are definitionally equal
	"Induction", x          splits on the variable x of an inductive type: one goal per constructor, taking
	                        the constructor's fields and an induction hypothesis per recursive field
	"Assumption"            solves the goal with a hypothesis of the same type

The other open goals may occur in a goal's type. Unification may then solve them while elaborating a
term for the goal, and the proof keeps those solutions.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryProof]
PackageExported[TypeTheoryTactic]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[proofStatement]
PackageScoped[proofUniverseParameters]
PackageScoped[completedProofTerm]
PackageScoped[goalDisplaySyntax]
PackageScoped[instantiateProofTerm]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryProof::usage = "TypeTheoryProof[statement, environment] starts a proof of statement in the TypeTheoryEnvironment environment, \
with statement itself as its one goal.\n\
TypeTheoryProof[TypeTheoryTerm[statement, environment]] does the same.\n\
TypeTheoryProof[statement, environment, {tactic1, tactic2, ...}] and TypeTheoryProof[TypeTheoryTerm[statement, environment], {tactic1, ...}] \
apply the TypeTheoryTactic tactics in turn.\n\
proof[\"Goals\"] gives the open goals as TypeTheoryTerm[RightTee[{Typed[x, type], ...}, goal], environment]; proof[\"Term\"] gives the proof term; \
proof[\"Statement\"] gives the statement; proof[\"Environment\"] gives the environment. \
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear."
TypeTheoryTactic::usage = "TypeTheoryTactic[name, arguments...] is a tactic: TypeTheoryTactic[name, arguments...][proof] applies it to the first goal of the TypeTheoryProof proof.\n\
TypeTheoryTactic[\"Introduce\", x, ...] introduces the variables or hypotheses of a universal statement or implication.\n\
TypeTheoryTactic[\"Exact\", term] solves the goal with term.\n\
TypeTheoryTactic[\"Apply\", term] solves the goal with term applied to new goals.\n\
TypeTheoryTactic[\"Reflexivity\"] solves an equation whose sides are equal by computation.\n\
TypeTheoryTactic[\"Induction\", x] splits on the variable x of an inductive type, one goal per constructor.\n\
TypeTheoryTactic[\"Assumption\"] solves the goal with a hypothesis of the same type."

proofStatement::usage = "proofStatement[proof] gives the core statement of the TypeTheoryProof proof."
proofUniverseParameters::usage = "proofUniverseParameters[proof] gives the universe parameters of the TypeTheoryProof proof."
completedProofTerm::usage = "completedProofTerm[proof] gives the core proof term of a finished TypeTheoryProof, or throws a kernel failure if goals are left."
goalDisplaySyntax::usage = "goalDisplaySyntax[data, id] gives {case, {hypothesisSyntax, ...}, goalSyntax} for the goal id of the proof data, case being None or HoldComplete[constructor]."
instantiateProofTerm::usage = "instantiateProofTerm[data, term] replaces the solved metavariables of the proof data in term by their solutions."


(* ::Section:: *)
(*Function Definitions*)


Options[TypeTheoryProof] = {"UniverseParameters" -> Automatic}

SetAttributes[TypeTheoryProof, HoldFirst]
SetAttributes[TypeTheoryTactic, HoldRest]


(* A proof state holds an Association, and patterns such as TypeTheoryProof[_Association] must not start
   a proof either, so a statement that is an Association or contains a pattern is not one. *)
TypeTheoryProof[statement_, environment_?environmentQ, options : OptionsPattern[]] /; statementQ[Unevaluated[statement]] :=
	startProof[environment, HoldComplete[statement], Hold[options]]

TypeTheoryProof[statement_, environment_?environmentQ, tactics : {___TypeTheoryTactic}, options : OptionsPattern[]] /; statementQ[Unevaluated[statement]] :=
	runTactics[TypeTheoryProof[statement, environment, options], tactics]

(* a TypeTheoryTerm, written out or held in a symbol, carries its own environment *)
TypeTheoryProof[term_, options : OptionsPattern[]] /; termExpressionQ[Unevaluated[term]] := With[{evaluated = term},
	startProof[termEnvironment[evaluated], heldTerm[evaluated], Hold[options]]
]

TypeTheoryProof[term_, tactics : {___TypeTheoryTactic}, options : OptionsPattern[]] /; termExpressionQ[Unevaluated[term]] :=
	runTactics[TypeTheoryProof[term, options], tactics]

startProof[environment_, held_HoldComplete, Hold[options___]] := catchKernelFailure @ With[
	{universeParameters = declarationUniverseParameters[TypeTheoryProof, Hold[options], {toSyntax @@ held}]},
	newProofState[environment, elaborateClosedType[environment, held, universeParameters], universeParameters]
]

(* the tactics in turn, stopping at the first one that fails *)
runTactics[state_, tactics_List] := Fold[Function[{current, tactic}, If[FailureQ[current], current, tactic[current]]], state, tactics]

statementQ[Unevaluated[_Association]] := False
statementQ[Unevaluated[statement_]] := FreeQ[Unevaluated[statement], _Pattern | _Blank | _BlankSequence | _BlankNullSequence]

termExpressionQ[Unevaluated[_TypeTheoryTerm]] := True
termExpressionQ[Unevaluated[symbol_Symbol]] := MatchQ[OwnValues[symbol], {Verbatim[RuleDelayed][_, _TypeTheoryTerm]}]
termExpressionQ[_] := False

proofState[data_Association] := TypeTheoryProof[data]

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


TypeTheoryProof[data_Association]["Goals"] := Function[goal, goalTerm[data, goal]] /@ data["Goals"]
TypeTheoryProof[data_Association]["Statement"] := coreToTypeTheoryTerm[data["Environment"], <||>, data["Statement"]]
TypeTheoryProof[data_Association]["Term"] := coreToTypeTheoryTerm[data["Environment"], <||>, instantiateProofTerm[data, metavariable[data["Root"]]]]
TypeTheoryProof[data_Association]["Environment"] := data["Environment"]

proofStatement[TypeTheoryProof[data_Association]] := data["Statement"]
proofUniverseParameters[TypeTheoryProof[data_Association]] := data["UniverseParameters"]

completedProofTerm[TypeTheoryProof[data_Association]] := If[ data["Goals"] =!= {},
	kernelFailure["ProofIncomplete", "The proof has `1` open goals.", {Length[data["Goals"]]}],
	instantiateProofTerm[data, metavariable[data["Root"]]]
]


(* ::Subsection:: *)
(*Goals*)


instantiateProofTerm[data_, term_] := resolvePendingAbstractions @ ReplaceRepeated[
	term,
	metavariable[id_] /; KeyExistsQ[data["Assignments"], id] :> data["Assignments"][id]
]

resolvePendingAbstractions[term_] := ReplaceRepeated[
	term,
	pendingAbstraction[context_, ids_, body_] /; FreeQ[body, _pendingAbstraction] :> makeLambda[context, ids, body]
]

(* a goal with the solutions found so far filled into its hypotheses and type *)
currentGoal[data_, goal_] := With[{entry = data["Metavariables"][goal]},
	<|
		"Context" -> Function[hypothesis, Append[hypothesis, "Type" -> instantiateProofTerm[data, hypothesis["Type"]]]] /@ entry["Context"],
		"Type" -> instantiateProofTerm[data, entry["Type"]]
	|>
]

openGoalTypes[data_] := AssociationMap[Function[goal, instantiateProofTerm[data, data["Metavariables"][goal]["Type"]]], data["Goals"]]

(* the hypotheses by name, a later hypothesis hiding an earlier one of the same name *)
contextScope[context_Association] := Association @ KeyValueMap[Function[{id, entry}, entry["Name"] -> {freeVariable[id], entry["Type"]}], context]

solveGoal[data_, goal_, term_, newGoals_List] := Join[data, <|
	"Assignments" -> Append[data["Assignments"], goal -> term],
	"Metavariables" -> Join[data["Metavariables"], Association[newGoals]],
	"Goals" -> Join[Keys[newGoals], DeleteCases[data["Goals"], goal]]
|>]

(* other open goals that unification solved while elaborating for this goal *)
keepSolvedGoals[data_, goalTypes_Association] := With[
	{solved = instantiateMetavariables /@ KeyTake[$metavariableAssignments, Keys[goalTypes]]},
	If[ ! FreeQ[Values[solved], metavariable[id_] /; ! KeyExistsQ[goalTypes, id]] || ! FreeQ[Values[solved], _levelMetavariable],
		kernelFailure["UnsolvedImplicitArgument", "Could not infer every implicit argument of the solution of another goal.", {}]
	];
	Join[data, <|
		"Assignments" -> Join[data["Assignments"], solved],
		"Goals" -> Select[data["Goals"], Function[goal, ! KeyExistsQ[solved, goal]]]
	|>]
]

goalTerm[data_, goal_] := Replace[goalDisplaySyntax[data, goal], {_, hypotheses_, target_} :>
	TypeTheoryTerm @@ Append[heldFromSyntax[syntaxHead[RightTee, {syntaxHead[List, hypotheses], target}]], data["Environment"]]
]

goalDisplaySyntax[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	{
		data["Metavariables"][goal]["Case"],
		KeyValueMap[
			Function[{id, entry}, syntaxHead[Typed, {nameSyntax[entry["Name"]], delaborate[environment, current["Context"], entry["Type"]]}]],
			current["Context"]
		],
		delaborate[environment, current["Context"], current["Type"]]
	}
]

goalDisplay[data_, goal_] := Quiet @ catchKernelFailure[goalTerm[data, goal]]


(* ::Subsection:: *)
(*Tactics*)


TypeTheoryTactic[name_String, arguments___][TypeTheoryProof[data_Association]] := catchKernelFailure @ Replace[data["Goals"], {
	{} :> kernelFailure["NoGoals", "The proof has no open goals.", {}],
	{goal_, ___} :> With[{goalTypes = openGoalTypes[data]},
		Block[{$metavariableTypes = goalTypes, $goalMetavariableTypes = goalTypes},
			proofState[runTactic[name, Hold[arguments], data, goal]]
		]
	]
}]

runTactic["Introduce", Hold[], data_, goal_] := introduceVariable[data, goal, Automatic]
runTactic["Introduce", Hold[names : (_Symbol | _String) ..], data_, goal_] := Fold[
	Function[{state, name}, introduceVariable[state, First[state["Goals"]], name]],
	data,
	HoldComplete /@ Unevaluated[{names}]
]
runTactic["Exact", Hold[term_], data_, goal_] := exactTerm[data, goal, HoldComplete[term]]
runTactic["Apply", Hold[term_], data_, goal_] := applyTerm[data, goal, HoldComplete[term]]
runTactic["Reflexivity", Hold[], data_, goal_] := reflexivity[data, goal]
runTactic["Induction", Hold[variable : _Symbol | _String], data_, goal_] := induction[data, goal, HoldComplete[variable]]
runTactic["Assumption", Hold[], data_, goal_] := assumption[data, goal]
runTactic[name_, _, _, _] := kernelFailure["UnknownTactic", "`1` is not a tactic, or is not given the arguments it takes.", {name}]


tacticFailure[tag_String, template_String, data_, goal_, parameters_List : {}] :=
	kernelFailure[tag, template, Prepend[parameters, goalDisplay[data, goal]]]


(* x : A |- B[x] for a goal (x : A) -> B, the solution being the function of x that solves the new goal *)
introduceVariable[data_, goal_, name_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	Replace[weakHeadNormalForm[environment, current["Context"], current["Type"]], {
		dependentFunctionType[binderName_, domain_, codomain_, binder_] :> With[
			{id = freshFreeVariable[], newGoal = freshMetavariableId[]},
			{context = extendContext[current["Context"], id, Replace[name, Automatic -> binderName], domain, binder]},
			solveGoal[
				data,
				goal,
				pendingAbstraction[context, {id}, metavariable[newGoal]],
				{newGoal -> <|"Context" -> context, "Type" -> betaNormalize[instantiateBoundVariable[codomain, freeVariable[id]]], "Case" -> None|>}
			]
		],
		_ :> tacticFailure["NothingToIntroduce", "The goal `1` is not a universal statement, an implication or a function type.", data, goal]
	}]
]


exactTerm[data_, goal_, held_HoldComplete] := With[
	{current = currentGoal[data, goal], environment = data["Environment"], goalTypes = openGoalTypes[data]},
	withElaborationState[{environment, current["Context"], contextScope[current["Context"]], data["UniverseParameters"]},
		With[{syntax = toSyntax @@ held},
			{result = elaborateSyntax[syntax, current["Type"]]},
			unifyOrFail[Last[result], current["Type"], syntax];
			With[{updated = keepSolvedGoals[data, goalTypes]},
				solveGoal[updated, goal, First @ finishElaboration[environment, current["Context"], result, instantiateMetavariables[current["Type"]]], {}]
			]
		]
	]
]


(* The term is applied to new metavariables until its type unifies with the goal; those left unsolved
   become new goals, the ones no other new goal mentions first. *)
applyTerm[data_, goal_, held_HoldComplete] := With[
	{current = currentGoal[data, goal], environment = data["Environment"], goalTypes = openGoalTypes[data]},
	withElaborationState[{environment, current["Context"], contextScope[current["Context"]], data["UniverseParameters"]},
		With[{syntax = toSyntax @@ held},
			{elaborated = elaborateSyntax[syntax, None]},
			{applied = applyUntilUnified[data, goal, First[elaborated], Last[elaborated], current["Type"]]},
			{
				newIds = DeleteDuplicates @ Cases[applied, metavariable[id_] /; ! KeyExistsQ[goalTypes, id] :> id, {0, Infinity}],
				updated = keepSolvedGoals[data, goalTypes]
			},
			{newTypes = AssociationMap[Function[id, instantiateMetavariables[$metavariableTypes[id]]], newIds]},
			If[ ! FreeQ[{applied, Values[newTypes]}, _levelMetavariable],
				tacticFailure["UnsolvedUniverseLevel", "Could not infer every universe level while applying to the goal `1`.", data, goal]
			];
			(* the partial term is checked now, with its holes standing for terms of their types *)
			Block[{$metavariableTypes = Join[goalTypes, newTypes], $metavariableAssignments = <||>},
				checkHasType[environment, current["Context"], applied, instantiateProofTerm[updated, current["Type"]]]
			];
			solveGoal[
				updated,
				goal,
				applied,
				Function[id, id -> <|"Context" -> current["Context"], "Type" -> newTypes[id], "Case" -> None|>] /@ SortBy[
					newIds,
					Function[id, ! FreeQ[Values[newTypes], metavariable[id]]]
				]
			]
		]
	]
]

applyUntilUnified[data_, goal_, term_, type_, target_] := If[ attemptOrRestore[unify[type, target]],
	instantiateMetavariables[term],
	Replace[weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[type]], {
		dependentFunctionType[_, domain_, codomain_, _] :> With[{argument = newMetavariable[domain]},
			applyUntilUnified[data, goal, application[term, argument], instantiateBoundVariable[codomain, argument], target]
		],
		_ :> tacticFailure["ApplyFailed", "The conclusion of the term does not match the goal `1`.", data, goal]
	}]
]


reflexivity[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	Replace[weakHeadNormalForm[environment, current["Context"], current["Type"]], {
		application[application[application[constantReference[HoldComplete[Equal], levels_], type_], left_], right_] :> If[
			definitionallyEqualQ[environment, current["Context"], left, right],
			solveGoal[data, goal, makeApplication[constantReference[HoldComplete[EqualityReflexivity], levels], {type, left}], {}],
			tacticFailure["NotReflexive", "The two sides of the goal `1` are not equal by computation.", data, goal]
		],
		_ :> tacticFailure["EquationExpected", "The goal `1` is not an equation.", data, goal]
	}]
]


assumption[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	Replace[
		SelectFirst[
			Reverse @ Keys[current["Context"]],
			Function[id, definitionallyEqualQ[environment, current["Context"], current["Context"][id]["Type"], current["Type"]]],
			None
		],
		{
			None :> tacticFailure["NoAssumption", "No hypothesis proves the goal `1`.", data, goal],
			id_ :> solveGoal[data, goal, freeVariable[id], {}]
		}
	]
]


(* ::Subsection:: *)
(*Induction*)


(* The recursor of the variable's type, applied to its parameters, the goal as a function of the
   variable (the motive), one new goal per constructor (the minor premises) and the variable itself.
   Each new goal is the minor premise's type, the goal for that constructor. *)
induction[data_, goal_, variableName_HoldComplete] := Module[
	{
		current = currentGoal[data, goal], environment = data["Environment"], context, id, head, parameters, inductiveName,
		inductiveRecord, recursorRecord, eliminationLevel, recursorLevels, motive, minorTypes, minorIds
	},
	context = current["Context"];
	id = Replace[
		SelectFirst[Reverse @ Keys[context], Function[key, context[key]["Name"] === variableName], None],
		None :> tacticFailure["UnknownHypothesis", "The goal `1` has no hypothesis `2`.", data, goal, {HoldForm @@ variableName}]
	];
	{head, parameters} = applicationSpine[weakHeadNormalForm[environment, context, context[id]["Type"]]];
	inductiveName = Replace[head, {
		constantReference[name_, _] /; constantRecord[environment, name]["Kind"] === "InductiveType" :> name,
		_ :> tacticFailure["InductiveTypeExpected", "In the goal `1`, the type of `2` is not an inductive type.", data, goal, {HoldForm @@ variableName}]
	}];
	inductiveRecord = constantRecord[environment, inductiveName];
	recursorRecord = constantRecord[environment, recursorName[inductiveName]];
	If[ inductiveRecord["NumberOfIndices"] > 0,
		tacticFailure["IndexedInduction", "In the goal `1`, `2` belongs to an inductive family with indices, which induction does not handle yet.", data, goal, {HoldForm @@ variableName}]
	];
	If[ AnyTrue[KeyDrop[context, id], Function[entry, ! FreeQ[entry["Type"], freeVariable[id]]]],
		tacticFailure["DependentHypothesis", "In the goal `1`, a hypothesis depends on `2`, and induction does not generalize it yet.", data, goal, {HoldForm @@ variableName}]
	];
	eliminationLevel = sortLevel[environment, context, current["Type"]];
	If[ ! TrueQ[recursorRecord["EliminationUniverse"]] && ! levelEquivalentQ[eliminationLevel, 0],
		tacticFailure["LargeElimination", "In the goal `1`, `2` can only be eliminated into a proposition.", data, goal, {HoldForm @@ inductiveName}]
	];
	recursorLevels = If[TrueQ[recursorRecord["EliminationUniverse"]], Prepend[Last[head], eliminationLevel], Last[head]];
	motive = lambdaAbstraction[variableName, context[id]["Type"], abstractFreeVariable[current["Type"], id], "Explicit"];
	minorTypes = minorPremiseTypes[
		instantiateUniverseParameters[recursorRecord["Type"], recursorRecord["UniverseParameters"], recursorLevels],
		parameters,
		motive,
		recursorRecord["NumberOfMinors"]
	];
	minorIds = Table[freshMetavariableId[], Length[minorTypes]];
	solveGoal[
		data,
		goal,
		makeApplication[constantReference[recursorName[inductiveName], recursorLevels], Join[parameters, {motive}, metavariable /@ minorIds, {freeVariable[id]}]],
		MapThread[
			Function[{minorId, minor}, minorId -> <|"Context" -> KeyDrop[context, id], "Type" -> Last[minor], "Case" -> First[minor]|>],
			{minorIds, minorTypes}
		]
	]
]

(* {{HoldComplete[constructor], minorType}, ...}, read off the recursor's type; the minor premises do not
   depend on one another, so each is instantiated with a placeholder *)
minorPremiseTypes[recursorType_, parameters_List, motive_, numberOfMinors_Integer] := With[
	{afterMotive = instantiateBinder[Fold[instantiateBinder, recursorType, parameters], motive]},
	First @ Fold[
		Function[{state, index}, Replace[Last[state], dependentFunctionType[constructor_, domain_, codomain_, _] :> {
			Append[First[state], {constructor, betaNormalize[domain]}],
			instantiateBoundVariable[codomain, metavariable[0]]
		}]],
		{{}, afterMotive},
		Range[numberOfMinors]
	]
]

instantiateBinder[dependentFunctionType[_, _, codomain_, _], value_] := instantiateBoundVariable[codomain, value]
