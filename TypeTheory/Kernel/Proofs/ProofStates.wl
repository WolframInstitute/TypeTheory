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
	"Reflexivity"           solves a goal a == b whose sides are definitionally equal, of Equal or of another type
	                        of equations, such as Lean's Eq imported
	"Induction", x          splits on the variable x of an inductive type: one goal per constructor, taking
	                        the constructor's fields and an induction hypothesis per recursive field; the
	                        indices of x's type must be variables, and hypotheses that depend on x or them
	                        are generalized
	"Cases", x              splits on x as "Induction" does, each goal taking the constructor's fields alone
	"Generalize", h, ...    moves the hypotheses h, ..., with those that depend on them, back into the goal
	"Constructor"           applies the first constructor of the goal's inductive type that applies
	"Assumption"            solves the goal with a hypothesis of the same type
	"Rewrite", h            replaces the first instance in the goal of the left side of the equation h, and every
	                        copy of it, by the right side; "Rewrite", h, "RightToLeft" replaces the right side;
	                        with "At" -> k last, it rewrites the hypothesis k instead
	"Change", statement     replaces the goal by a statement equal to it by computation
	"Simplify", {h, ...}    rewrites with the equations h, ... until none applies, then closes an equation whose
	                        sides are equal by computation; a definition among them unfolds where it computes
	"Decide"                proves a closed statement of equations and inequalities of natural numbers and the
	                        connectives by computing its decision

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


TypeTheoryProof::usage = "TypeTheoryProof[statement] starts a proof of statement in the default environment, $TypeTheoryEnvironment, with statement itself as its one goal.\n\
TypeTheoryProof[statement, environment] starts the proof in the TypeTheoryEnvironment environment.\n\
TypeTheoryProof[TypeTheoryTerm[statement, environment]] does the same.\n\
TypeTheoryProof[statement, {tactic1, tactic2, ...}], TypeTheoryProof[statement, environment, {tactic1, ...}] and \
TypeTheoryProof[TypeTheoryTerm[statement, environment], {tactic1, ...}] apply the TypeTheoryTactic tactics in turn.\n\
proof[\"Goals\"] gives the open goals as TypeTheoryTerm[RightTee[{Typed[x, type], ...}, goal], environment]; proof[\"Term\"] gives the proof term; \
proof[\"Statement\"] gives the statement; proof[\"Environment\"] gives the environment. \
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear."
TypeTheoryTactic::usage = "TypeTheoryTactic[name, arguments...] is a tactic: TypeTheoryTactic[name, arguments...][proof] applies it to the first goal of the TypeTheoryProof proof.\n\
TypeTheoryTactic[\"Introduce\", x, ...] introduces the variables or hypotheses of a universal statement or implication.\n\
TypeTheoryTactic[\"Exact\", term] solves the goal with term.\n\
TypeTheoryTactic[\"Apply\", term] solves the goal with term applied to new goals.\n\
TypeTheoryTactic[\"Reflexivity\"] solves an equation whose sides are equal by computation.\n\
TypeTheoryTactic[\"Induction\", x] splits on the variable x of an inductive type, one goal per constructor.\n\
TypeTheoryTactic[\"Cases\", x] splits on x without induction hypotheses.\n\
TypeTheoryTactic[\"Generalize\", h, ...] moves the hypotheses h, ..., and those that depend on them, back into the goal.\n\
TypeTheoryTactic[\"Constructor\"] applies the first constructor of the goal's inductive type that applies to it.\n\
TypeTheoryTactic[\"Assumption\"] solves the goal with a hypothesis of the same type.\n\
TypeTheoryTactic[\"Rewrite\", h] replaces an instance of the left side of the equation h in the goal by its right side; \
TypeTheoryTactic[\"Rewrite\", h, \"RightToLeft\"] replaces the right side by the left.\n\
TypeTheoryTactic[\"Rewrite\", h, \"At\" -> k] and TypeTheoryTactic[\"Rewrite\", h, \"RightToLeft\", \"At\" -> k] rewrite the hypothesis k instead of the goal.\n\
TypeTheoryTactic[\"Change\", statement] replaces the goal by statement, which must be equal to it by computation.\n\
TypeTheoryTactic[\"Simplify\", {h1, h2, ...}] rewrites the goal with the equations until none applies, then closes it if its sides are equal by computation; \
a definition among h1, h2, ... unfolds where it computes, as Join does on ListPrepend[x, l], with its recursive calls folded back.\n\
TypeTheoryTactic[\"Decide\"] proves a closed statement built from == and <= of natural numbers, And, Or, Not, True and False by computing its decision."

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

(* without an environment, a statement is proved in the default environment *)
TypeTheoryProof[statement_, options : OptionsPattern[]] /; ! termExpressionQ[Unevaluated[statement]] && statementQ[Unevaluated[statement]] :=
	TypeTheoryProof[statement, defaultEnvironment[], options]

TypeTheoryProof[statement_, tactics : {___TypeTheoryTactic}, options : OptionsPattern[]] /; ! termExpressionQ[Unevaluated[statement]] && statementQ[Unevaluated[statement]] :=
	TypeTheoryProof[statement, defaultEnvironment[], tactics, options]

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

openGoalContexts[data_] := AssociationMap[Function[goal, Keys[data["Metavariables"][goal]["Context"]]], data["Goals"]]

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
	{goal_, ___} :> withOpenGoals[data, proofState[runTactic[name, Hold[arguments], data, goal]]]
}]

(* the open goals of the proof, as the metavariables a tactic's elaboration may meet, each with its type and hypotheses *)
SetAttributes[withOpenGoals, HoldRest]
withOpenGoals[data_, body_] := With[{goalTypes = openGoalTypes[data]},
	Block[{$metavariableTypes = goalTypes, $goalMetavariableTypes = goalTypes, $goalMetavariableContexts = openGoalContexts[data]},
		body
	]
]

runTactic["Introduce", Hold[], data_, goal_] := introduceVariable[data, goal, Automatic]
runTactic["Introduce", Hold[names : (_Symbol | _String) ..], data_, goal_] := Fold[
	Function[{state, name}, introduceVariable[state, First[state["Goals"]], name]],
	data,
	HoldComplete /@ Unevaluated[{names}]
]
runTactic["Exact", Hold[term_], data_, goal_] := exactTerm[data, goal, HoldComplete[term]]
runTactic["Apply", Hold[term_], data_, goal_] := applyTerm[data, goal, HoldComplete[term]]
runTactic["Reflexivity", Hold[], data_, goal_] := reflexivity[data, goal]
runTactic["Induction", Hold[variable : _Symbol | _String], data_, goal_] := eliminate[data, goal, HoldComplete[variable], "Induction"]
runTactic["Cases", Hold[variable : _Symbol | _String], data_, goal_] := eliminate[data, goal, HoldComplete[variable], "Cases"]
runTactic["Generalize", Hold[names : (_Symbol | _String) ..], data_, goal_] := generalize[data, goal, HoldComplete /@ Unevaluated[{names}]]
runTactic["Constructor", Hold[], data_, goal_] := constructorTactic[data, goal]
runTactic["Change", Hold[statement_], data_, goal_] := change[data, goal, HoldComplete[statement]]
runTactic["Simplify", Hold[{lemmas___}], data_, goal_] := simplify[data, goal, HoldComplete /@ Unevaluated[{lemmas}]]
runTactic["Decide", Hold[], data_, goal_] := decide[data, goal]
runTactic["Assumption", Hold[], data_, goal_] := assumption[data, goal]
runTactic["Rewrite", Hold[term_], data_, goal_] := rewrite[data, goal, HoldComplete[term], "LeftToRight", None]
runTactic["Rewrite", Hold[term_, direction : "LeftToRight" | "RightToLeft"], data_, goal_] := rewrite[data, goal, HoldComplete[term], direction, None]
runTactic["Rewrite", Hold[term_, "At" -> (hypothesis : _Symbol | _String)], data_, goal_] := rewrite[data, goal, HoldComplete[term], "LeftToRight", HoldComplete[hypothesis]]
runTactic["Rewrite", Hold[term_, direction : "LeftToRight" | "RightToLeft", "At" -> (hypothesis : _Symbol | _String)], data_, goal_] :=
	rewrite[data, goal, HoldComplete[term], direction, HoldComplete[hypothesis]]
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
   become new goals, the ones no other new goal mentions first, each with the hypotheses of the context
   it was made in. *)
applyTerm[data_, goal_, held_HoldComplete] := With[
	{current = currentGoal[data, goal], environment = data["Environment"], goalTypes = openGoalTypes[data]},
	withElaborationState[{environment, current["Context"], contextScope[current["Context"]], data["UniverseParameters"]},
		With[{syntax = toSyntax @@ held},
			{elaborated = elaborateSyntax[syntax, None]},
			{applied = settleOverloads[applyUntilUnified[data, goal, First[elaborated], Last[elaborated], current["Type"]]]},
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
				Function[id, id -> <|"Context" -> KeyTake[current["Context"], $metavariableContexts[id]], "Type" -> newTypes[id], "Case" -> None|>] /@ SortBy[
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
		application[application[application[constantReference[equality_, levels_], type_], left_], right_] /; equalityTypeQ[environment, equality] :> If[
			definitionallyEqualQ[environment, current["Context"], left, right],
			solveGoal[data, goal, makeApplication[constantReference[First[constantRecord[environment, equality]["Constructors"]], levels], {type, left}], {}],
			tacticFailure["NotReflexive", "The two sides of the goal `1` are not equal by computation.", data, goal]
		],
		_ :> tacticFailure["EquationExpected", "The goal `1` is not an equation.", data, goal]
	}]
]

(* a type of equations, as Equal is and Lean's Eq imported: an inductive type of a type A and two elements of
   it, whose one constructor makes an element x equal to x *)
equalityTypeQ[environment_, name_HoldComplete] := With[{record = constantRecord[environment, name]},
	And[
		MatchQ[record, KeyValuePattern[{"Kind" -> "InductiveType", "Constructors" -> {_}}]],
		MatchQ[record["Type"], dependentFunctionType[_, _, dependentFunctionType[_, boundVariable[0], dependentFunctionType[_, boundVariable[1], _universeSort, _], _], _]],
		MatchQ[
			constantRecord[environment, First[record["Constructors"]]]["Type"],
			dependentFunctionType[_, _, dependentFunctionType[_, boundVariable[0], application[application[application[constantReference[name, _], boundVariable[1]], boundVariable[0]], boundVariable[0]], _], _]
		]
	]
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
(*Rewrite*)


(* The proof h is applied to new metavariables until its type is an equation lhs == rhs of a type of
   equations. The first subterm of the statement that unifies with the side to replace, children before
   their parent and functions before arguments as Lean's kabstract visits them, fixes those
   metavariables, and every copy of that instance is abstracted into the motive P.
   Left to right, the new goal is P[rhs], carried back along the equation to a proof of the goal P[lhs];
   right to left, the new goal is P[lhs], carried forward to P[rhs]. A new goal whose two sides are the
   same term is closed by reflexivity, as after Lean's rw.
   At a hypothesis k : P[lhs], left to right, k is carried forward to a proof of P[rhs], which a new
   hypothesis of the same name takes, and right to left back; the new hypothesis replaces k unless the
   goal or another hypothesis depends on k, as with Lean's rw at k. *)
rewrite[data_, goal_, held_HoldComplete, direction_String, location_] := With[
	{current = currentGoal[data, goal], environment = data["Environment"], goalTypes = openGoalTypes[data]},
	withElaborationState[{environment, current["Context"], contextScope[current["Context"]], data["UniverseParameters"]},
		Replace[location, {
			None :> rewriteGoal[data, goal, current, goalTypes, rewrittenStatement[data, goal, current, goalTypes, toSyntax @@ held, direction, current["Type"]], direction],
			name_HoldComplete :> With[{id = hypothesisId[data, goal, current["Context"], name]},
				rewriteHypothesis[
					data,
					goal,
					current,
					goalTypes,
					rewrittenStatement[data, goal, current, goalTypes, toSyntax @@ held, direction, current["Context"][id]["Type"]],
					direction,
					id
				]
			]
		}]
	]
]

(* the equation, its instance in the statement and the motive: <|"Left", "Right", "Proof", "Type", "Recursor",
   "Instance", "Motive" -> P, "Statement" -> the statement rewritten|> *)
rewrittenStatement[data_, goal_, current_, goalTypes_, syntax_, direction_String, statement_] := Module[
	{environment = data["Environment"], context = current["Context"], elaborated, equation, side, target, left, right, proof, elementType, levels, instance, motiveBody},
	elaborated = elaborateSyntax[syntax, None];
	equation = equationOf[data, goal, settleOverloads[First[elaborated]], Last[elaborated]];
	side = If[direction === "LeftToRight", equation["Left"], equation["Right"]];
	target = instantiateMetavariables[statement];
	If[ instancePatternKey[instantiateMetavariables[side]] === None,
		tacticFailure["PatternExpected", "In the goal `1`, the side of the equation to rewrite is an unknown term.", data, goal]
	];
	If[ ! firstInstanceUnifiedQ[target, side],
		tacticFailure["NoInstance", "The goal `1` has no instance of `2`.", data, goal, {displayCoreTerm[environment, context, instantiateMetavariables[side]]}]
	];
	{left, right, proof, elementType} = instantiateMetavariables /@ {equation["Left"], equation["Right"], equation["Proof"], equation["Type"]};
	(* levels are instantiated where they stand, in a constant *)
	levels = Last @ instantiateMetavariables[constantReference[equation["Equality"], equation["Levels"]]];
	If[ ! FreeQ[{proof, left, right, levels}, metavariable[id_] /; ! KeyExistsQ[goalTypes, id]] || ! FreeQ[{proof, left, right, levels}, _levelMetavariable],
		tacticFailure["UnsolvedImplicitArgument", "Could not infer every argument of the equation used to rewrite the goal `1`.", data, goal]
	];
	instance = If[direction === "LeftToRight", left, right];
	motiveBody = abstractInstances[instantiateMetavariables[target], instance];
	<|
		"Left" -> left,
		"Right" -> right,
		"Proof" -> proof,
		"Type" -> elementType,
		"Equality" -> equation["Equality"],
		"Levels" -> levels,
		"Recursor" -> equationRecursor[data, goal, context, equation["Equality"], levels, instantiateMetavariables[target]],
		"Instance" -> instance,
		"Motive" -> motiveBody,
		"Statement" -> betaNormalize[instantiateBoundVariable[motiveBody, If[direction === "LeftToRight", right, left]]]
	|>
]

rewriteGoal[data_, goal_, current_, goalTypes_, rewritten_Association, direction_String] := With[
	{
		newId = freshMetavariableId[],
		environment = data["Environment"],
		context = current["Context"],
		updated = keepSolvedGoals[data, goalTypes]
	},
	With[{solution = If[direction === "LeftToRight", transportBackward, transportForward][rewritten, context, metavariable[newId]]},
		Replace[
			Block[{$metavariableTypes = Join[goalTypes, <|newId -> rewritten["Statement"]|>], $metavariableAssignments = <||>},
				catchKernelFailure[checkHasType[environment, context, solution, instantiateProofTerm[updated, current["Type"]]]]
			],
			_Failure :> motiveFailure[data, goal, context, rewritten]
		];
		closeIfSidesSame[
			solveGoal[updated, goal, solution, {newId -> <|"Context" -> context, "Type" -> rewritten["Statement"], "Case" -> None|>}],
			newId,
			rewritten["Statement"]
		]
	]
]

rewriteHypothesis[data_, goal_, current_, goalTypes_, rewritten_Association, direction_String, id_] := Module[
	{environment = data["Environment"], context = current["Context"], newId = freshFreeVariable[], newGoal = freshMetavariableId[], proof, others, newContext},
	proof = If[direction === "LeftToRight", transportForward, transportBackward][rewritten, context, freeVariable[id]];
	Replace[
		Block[{$metavariableTypes = goalTypes, $metavariableAssignments = <||>},
			catchKernelFailure[checkHasType[environment, context, proof, rewritten["Statement"]]]
		],
		_Failure :> motiveFailure[data, goal, context, rewritten]
	];
	others = KeyDrop[context, id];
	newContext = extendContext[
		If[FreeQ[{current["Type"], rewritten["Statement"], Lookup[Values[others], "Type"]}, freeVariable[id]], others, context],
		newId,
		context[id]["Name"],
		rewritten["Statement"],
		context[id]["Binder"]
	];
	solveGoal[
		keepSolvedGoals[data, goalTypes],
		goal,
		application[pendingAbstraction[newContext, {newId}, metavariable[newGoal]], proof],
		{newGoal -> <|"Context" -> newContext, "Type" -> current["Type"], "Case" -> None|>}
	]
]

(* m, a proof of P[lhs], carried along the equation to a proof of P[rhs]: the equation's recursor with the
   motive (y, t) ↦ P[y] takes m as its one minor premise *)
transportForward[rewritten_Association, context_, m_] := makeApplication[rewritten["Recursor"], {
	rewritten["Type"],
	rewritten["Left"],
	rewriteMotive[context, rewritten["Equality"], rewritten["Levels"], rewritten["Type"], rewritten["Left"], rewritten["Motive"], None],
	m,
	rewritten["Right"],
	rewritten["Proof"]
}]

(* m, a proof of P[rhs], carried back to a proof of P[lhs]: the recursor with the motive (y, t) ↦ P[y] -> P[lhs]
   and the identity as its minor premise gives a function from P[rhs] to P[lhs] *)
transportBackward[rewritten_Association, context_, m_] := application[
	makeApplication[rewritten["Recursor"], {
		rewritten["Type"],
		rewritten["Left"],
		rewriteMotive[context, rewritten["Equality"], rewritten["Levels"], rewritten["Type"], rewritten["Left"], rewritten["Motive"], rewritten["Left"]],
		lambdaAbstraction[HoldComplete[p], instantiateBoundVariable[rewritten["Motive"], rewritten["Left"]], boundVariable[0], "Explicit"],
		rewritten["Right"],
		rewritten["Proof"]
	}],
	m
]

motiveFailure[data_, goal_, context_, rewritten_Association] := tacticFailure[
	"MotiveNotTypeCorrect",
	"Abstracting `2` in the goal `1` gives a statement that is not well typed.",
	data,
	goal,
	{displayCoreTerm[data["Environment"], context, rewritten["Instance"]]}
]

(* the proof applied to new metavariables until its type is an equation of a type of equations *)
equationOf[data_, goal_, proof_, type_] := Replace[
	weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[type]],
	{
		application[application[application[constantReference[equality_, levels_], elementType_], left_], right_] /; equalityTypeQ[$elaborationEnvironment, equality] :>
			<|"Proof" -> proof, "Equality" -> equality, "Levels" -> levels, "Type" -> elementType, "Left" -> left, "Right" -> right|>,
		dependentFunctionType[_, domain_, codomain_, _] :> With[{argument = newMetavariable[domain]},
			equationOf[data, goal, application[proof, argument], instantiateBoundVariable[codomain, argument]]
		],
		_ :> tacticFailure["EquationExpected", "The term given to rewrite the goal `1` does not prove an equation.", data, goal]
	}
]

(* A subterm can be an instance of the pattern only if it has the pattern's head, a constant at any
   levels, a variable or a literal, and as many arguments; a pattern whose head is unknown has no key. *)
instancePatternKey[term_] := Replace[applicationSpine[term], {
	{metavariable[_], _} :> None,
	{constantReference[name_, _], arguments_} :> {name, Length[arguments]},
	{head_, arguments_} :> {head, Length[arguments]}
}]

(* unifies the pattern with the first subterm of term that can be its instance, and gives True if one does *)
firstInstanceUnifiedQ[term_, pattern_] := With[{key = instancePatternKey[instantiateMetavariables[pattern]]},
	AnyTrue[
		instanceCandidates[term],
		Function[candidate, instancePatternKey[candidate] === key && attemptOrRestore[unify[candidate, pattern]]]
	]
]

(* the subterms of term that no binder of term binds into, each once, children before their parent *)
instanceCandidates[term_] := DeleteDuplicates @ Catenate @ Last @ Reap[sowInstanceCandidates[term], "candidate"]

sowInstanceCandidates[term : application[function_, argument_]] := (sowInstanceCandidates[function]; sowInstanceCandidates[argument]; sowInstanceCandidate[term])
sowInstanceCandidates[term : (lambdaAbstraction | dependentFunctionType)[_, domain_, body_, _]] :=
	(sowInstanceCandidates[domain]; sowInstanceCandidates[body]; sowInstanceCandidate[term])
sowInstanceCandidates[term : localDefinition[_, type_, value_, body_]] :=
	(sowInstanceCandidates[type]; sowInstanceCandidates[value]; sowInstanceCandidates[body]; sowInstanceCandidate[term])
sowInstanceCandidates[term : projection[_, _, inner_]] := (sowInstanceCandidates[inner]; sowInstanceCandidate[term])
sowInstanceCandidates[term_] := sowInstanceCandidate[term]

sowInstanceCandidate[term_] := If[looseBoundRange[term] == 0, Sow[term, "candidate"]]

(* term with every copy of instance replaced by the variable of a binder just outside it *)
abstractInstances[term_, instance_] := Block[{$instanceMemo = <||>}, abstractInstance[term, instance, 0]]

abstractInstance[term_, instance_, depth_] := Lookup[
	$instanceMemo,
	Key[{term, depth}],
	$instanceMemo[{term, depth}] = If[term === instance, boundVariable[depth], abstractInstanceBelow[term, instance, depth]]
]

abstractInstanceBelow[application[function_, argument_], instance_, depth_] :=
	application[abstractInstance[function, instance, depth], abstractInstance[argument, instance, depth]]
abstractInstanceBelow[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_], instance_, depth_] :=
	head[name, abstractInstance[domain, instance, depth], abstractInstance[body, instance, depth + 1], binder]
abstractInstanceBelow[localDefinition[name_, type_, value_, body_], instance_, depth_] :=
	localDefinition[name, abstractInstance[type, instance, depth], abstractInstance[value, instance, depth], abstractInstance[body, instance, depth + 1]]
abstractInstanceBelow[projection[structure_, index_, inner_], instance_, depth_] := projection[structure, index, abstractInstance[inner, instance, depth]]
abstractInstanceBelow[term_, _, _] := term

(* the recursor of the type of equations, eliminating into the sort of the goal *)
equationRecursor[data_, goal_, context_, equality_, levels_List, target_] := With[
	{record = constantRecord[data["Environment"], recursorName[equality]], eliminationLevel = sortLevel[data["Environment"], context, target]},
	If[ ! TrueQ[record["EliminationUniverse"]] && ! levelEquivalentQ[eliminationLevel, 0],
		tacticFailure["LargeElimination", "In the goal `1`, the equation can only rewrite a proposition.", data, goal]
	];
	constantReference[recursorName[equality], If[TrueQ[record["EliminationUniverse"]], Prepend[levels, eliminationLevel], levels]]
]

(* (y, t) ↦ P[y] -> P[result], or (y, t) ↦ P[y] when result is None, t being a proof that start equals y *)
rewriteMotive[context_, equality_, levels_List, elementType_, start_, motiveBody_, result_] := With[
	{variable = freshFreeVariable[], equation = freshFreeVariable[]},
	With[
		{
			local = extendContext[
				extendContext[context, variable, HoldComplete[y], elementType, "Explicit"],
				equation,
				HoldComplete[t],
				makeApplication[constantReference[equality, levels], {elementType, start, freeVariable[variable]}],
				"Explicit"
			],
			atVariable = instantiateBoundVariable[motiveBody, freeVariable[variable]]
		},
		makeLambda[local, {variable, equation}, If[
			result === None,
			atVariable,
			dependentFunctionType[HoldComplete[p], atVariable, instantiateBoundVariable[motiveBody, result], "Explicit"]
		]]
	]
]

(* ::Subsection:: *)
(*Change, Simplify and Decide*)


(* The goal replaced by a statement equal to it by computation, which a rewrite can then reach into: the
   new goal's solution solves the goal as it is. *)
change[data_, goal_, held_HoldComplete] := With[
	{current = currentGoal[data, goal], environment = data["Environment"], goalTypes = openGoalTypes[data], newGoal = freshMetavariableId[]},
	withElaborationState[{environment, current["Context"], contextScope[current["Context"]], data["UniverseParameters"]},
		With[{statement = First @ finishElaboration[
			environment,
			current["Context"],
			elaborateSyntax[toSyntax @@ held, inferType[environment, current["Context"], current["Type"]]],
			inferType[environment, current["Context"], current["Type"]]
		]},
			If[ ! definitionallyEqualQ[environment, current["Context"], statement, current["Type"]],
				tacticFailure["NotDefinitionallyEqual", "The statement given is not equal by computation to the goal `1`.", data, goal]
			];
			solveGoal[keepSolvedGoals[data, goalTypes], goal, metavariable[newGoal], {newGoal -> <|"Context" -> current["Context"], "Type" -> statement, "Case" -> None|>}]
		]
	]
]


(* Each lemma in turn rewrites the goal, left side to right side, the first that applies each time, until
   none does or the goal repeats, as commutativity would make it; the goal is then closed by reflexivity
   if its sides are equal by computation. A lemma that applies nowhere is no failure, but a goal that no
   lemma changes and reflexivity does not close is. *)
simplify[data_, goal_, lemmas_List] := Replace[
	simplificationSteps[data, goal, lemmas, {}],
	{
		{state_, None, _} :> state,
		{state_, current_, _} :> Replace[
			closedByReflexivity[state, current],
			None :> If[
				currentGoal[state, current]["Type"] =!= currentGoal[data, goal]["Type"],
				state,
				tacticFailure["NoProgress", "The lemmas leave the goal `1` as it is, and its sides are not equal by computation.", data, goal]
			]
		]
	}
]

(* {state, the goal as rewritten so far or None once a rewrite closed it, whether a lemma rewrote it};
   at most a hundred rewrites *)
simplificationSteps[state_, goal_, lemmas_List, seen_List] := If[
	Length[seen] >= 100 || MemberQ[seen, currentGoal[state, goal]["Type"]],
	{state, goal, seen =!= {}},
	Replace[firstRewrite[state, goal, lemmas], {
		None :> {state, goal, seen =!= {}},
		(* the rewritten goal comes first, unless the rewrite closed it *)
		rewritten_ /; Length[rewritten["Goals"]] < Length[state["Goals"]] :> {rewritten, None, True},
		rewritten_ :> simplificationSteps[rewritten, First[rewritten["Goals"]], lemmas, Append[seen, currentGoal[state, goal]["Type"]]]
	}]
]

(* the state after the first lemma that rewrites the goal, or None; a definition named among the lemmas
   unfolds where it computes instead *)
firstRewrite[state_, goal_, {}] := None
firstRewrite[state_, goal_, {lemma_, rest___}] := Replace[
	withOpenGoals[state, Quiet @ catchKernelFailure[
		If[definitionNamedQ[state, goal, lemma], unfold[state, goal, lemma], rewrite[state, goal, lemma, "LeftToRight", None]]
	]],
	_Failure :> firstRewrite[state, goal, {rest}]
]

(* a name that is no hypothesis of the goal and stands for a definition *)
definitionNamedQ[data_, goal_, held_HoldComplete] := With[{name = aliasResolvedName[data["Environment"], held]},
	And[
		! MemberQ[Lookup[Values[data["Metavariables"][goal]["Context"]], "Name"], held],
		constantDeclaredQ[data["Environment"], name],
		constantRecord[data["Environment"], name]["Kind"] === "Definition"
	]
]

(* The first application of the definition in the goal, children before their parent, that computes, in
   its place. A definition by recursion on one of its arguments, as Join is on its first, computes where
   that argument is a constructor applied: it gives the recursor's rule for that constructor, with each
   recursive call folded back into the definition, so Join[ListPrepend[x, l], m] gives
   ListPrepend[x, Join[l, m]]. Any other definition, given all its arguments, is its value applied to them.
   The new goal is equal to the goal by computation, so its solution solves the goal. *)
unfold[data_, goal_, held_HoldComplete] := With[
	{current = currentGoal[data, goal], environment = data["Environment"], name = aliasResolvedName[data["Environment"], held]},
	Replace[
		SelectFirst[
			Function[candidate, {candidate, unfoldedApplication[environment, current["Context"], name, candidate]}] /@ instanceCandidates[current["Type"]],
			Function[pair, Last[pair] =!= None],
			None
		],
		{
			None :> tacticFailure["NothingToUnfold", "The definition `2` computes nowhere in the goal `1`.", data, goal, {HoldForm @@ held}],
			{instance_, unfolded_} :> With[
				{newGoal = freshMetavariableId[], statement = betaNormalize[instantiateBoundVariable[abstractInstances[current["Type"], instance], unfolded]]},
				solveGoal[data, goal, metavariable[newGoal], {newGoal -> <|"Context" -> current["Context"], "Type" -> statement, "Case" -> None|>}]
			]
		}
	]
]

(* the term, an application of the definition name, computed as unfold computes it, or None *)
unfoldedApplication[environment_, context_, name_, term_] := Replace[applicationSpine[term], {
	{constantReference[name, levels_], arguments_} :> With[
		{record = constantRecord[environment, name]},
		{value = instantiateUniverseParameters[record["Value"], record["UniverseParameters"], levels]},
		{opened = openedFunction[value, 0]},
		Which[
			Length[arguments] < Last[opened],
				None,
			recursorApplicationQ[environment, First[opened]],
				computedRecursion[environment, context, name, levels, opened, arguments],
			True,
				makeApplication[value, arguments]
		]
	],
	_ :> None
}]

(* {body, count}: the body under the functions nested at the top of term, and their count *)
openedFunction[lambdaAbstraction[_, _, body_, _], count_Integer] := openedFunction[body, count + 1]
openedFunction[body_, count_Integer] := {body, count}

recursorApplicationQ[environment_, body_] := MatchQ[First[applicationSpine[body]], constantReference[recursor_, _] /; constantRecord[environment, recursor]["Kind"] === "Recursor"]

(* A definition by structural recursion has a recursor applied to its parameters, motives and minor
   premises, no indices, and last the major premise, one of the definition's count variables, which no
   other argument of the recursor mentions. None for any other body. *)
computedRecursion[environment_, context_, name_, levels_, {body_, count_Integer}, arguments_List] := With[
	{spine = applicationSpine[body]},
	{record = constantRecord[environment, First[First[spine]]], recursorArguments = Last[spine]},
	If[ And[
			record["NumberOfIndices"] === 0,
			Length[recursorArguments] === record["NumberOfParameters"] + record["NumberOfMotives"] + record["NumberOfMinors"] + 1,
			MatchQ[Last[recursorArguments], boundVariable[k_Integer] /; k < count],
			NoneTrue[Most[recursorArguments], Function[argument, boundVariableOccursQ[argument, First[Last[recursorArguments]]]]]
		],
		refoldedRecursion[environment, context, name, levels, First[spine], recursorArguments, count, arguments],
		None
	]
]

(* The recursor reduced on the argument given for its major premise, or None if it does not reduce; in
   what it gives, a recursive call, the recursor applied to the same arguments but a smaller major
   premise, is the definition applied to that one in its place. *)
refoldedRecursion[environment_, context_, name_, levels_, recursor_, recursorArguments_List, count_Integer, arguments_List] := With[
	{
		position = count - First[Last[recursorArguments]],
		given = Take[arguments, count]
	},
	{prefix = makeApplication[recursor, Function[argument, instantiateBoundVariables[argument, given]] /@ Most[recursorArguments]]},
	{reduced = reducedHeadWithoutUnfolding[environment, context, application[prefix, First[Drop[given, position - 1]]]]},
	If[ MatchQ[reduced, application[Verbatim[prefix], _]],
		None,
		makeApplication[
			ReplaceAll[reduced, application[Verbatim[prefix], smaller_] :> makeApplication[constantReference[name, levels], Join[Take[given, position - 1], {smaller}, Drop[given, position]]]],
			Drop[arguments, count]
		]
	]
]

(* the state with the goal closed by reflexivity, or None *)
closedByReflexivity[state_, goal_] := Replace[
	withOpenGoals[state, Quiet @ catchKernelFailure[reflexivity[state, goal]]],
	_Failure -> None
]


(* A closed proposition built from == and <= on the natural numbers, And, Or, Not, True and False gets
   its decision from the prelude's, Decidable[p]; the kernel computes Decide of it to True, and
   DecideSoundness turns EqualityReflexivity[True] into a proof of the goal. *)
decide[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	If[ ! AllTrue[$decisionConstants, Function[name, constantDeclaredQ[environment, name]]],
		tacticFailure["DecisionUnavailable", "The environment of the goal `1` lacks the decisions of the prelude.", data, goal]
	];
	With[{decision = decisionTerm[data, goal, environment, current["Context"], current["Type"]]},
		Replace[weakHeadNormalForm[environment, current["Context"], makeApplication[preludeConstant[Decide], {current["Type"], decision}]], {
			constantReference[HoldComplete["true"], _] :> solveGoal[data, goal, makeApplication[preludeConstant[DecideSoundness], {
				current["Type"],
				decision,
				makeApplication[constantReference[HoldComplete[EqualityReflexivity], {1}], {preludeConstant[Booleans], preludeConstant["true"]}]
			}], {}],
			constantReference[HoldComplete["false"], _] :> tacticFailure["DecidedFalse", "The goal `1` is false.", data, goal],
			_ :> tacticFailure["NotDecided", "The decision of the goal `1` does not compute to True or False, as when it has variables.", data, goal]
		}]
	]
]

$decisionConstants = HoldComplete /@ Unevaluated[{
	Decidable, DecidableTrue, DecidableFalse, Decide, DecideSoundness, NotDecidable, AndDecidable, OrDecidable,
	NaturalNumberEqualityDecidable, LessEqualDecidable, Booleans, "true", EqualityReflexivity, TrueIntroduction
}]

SetAttributes[preludeConstant, HoldAll]
preludeConstant[name_] := constantReference[HoldComplete[name], {}]

(* the decision of a proposition, by its form; a definition such as Not, Less or Unequal is unfolded to find it *)
decisionTerm[data_, goal_, environment_, context_, proposition_] := Replace[proposition, {
	application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] /;
		MatchQ[weakHeadNormalForm[environment, context, type], constantReference[HoldComplete[NonNegativeIntegers], _]] :>
		makeApplication[preludeConstant[NaturalNumberEqualityDecidable], {left, right}],
	application[application[constantReference[HoldComplete[LessEqual], _], left_], right_] :>
		makeApplication[preludeConstant[LessEqualDecidable], {left, right}],
	application[application[constantReference[HoldComplete[connective : And | Or], _], left_], right_] :>
		makeApplication[preludeConstant @@ {If[connective === And, AndDecidable, OrDecidable]}, {
			left,
			right,
			decisionTerm[data, goal, environment, context, left],
			decisionTerm[data, goal, environment, context, right]
		}],
	constantReference[HoldComplete[True], _] :> makeApplication[preludeConstant[DecidableTrue], {proposition, preludeConstant[TrueIntroduction]}],
	constantReference[HoldComplete[False], _] :> makeApplication[preludeConstant[DecidableFalse], {proposition, lambdaAbstraction[HoldComplete[h], proposition, boundVariable[0], "Explicit"]}],
	(* Not[p] unfolds to a function from p to False *)
	dependentFunctionType[_, premise_, constantReference[HoldComplete[False], _], _] :>
		makeApplication[preludeConstant[NotDecidable], {premise, decisionTerm[data, goal, environment, context, premise]}],
	other_ :> With[{reduced = weakHeadNormalForm[environment, context, other]},
		If[ reduced =!= other,
			decisionTerm[data, goal, environment, context, reduced],
			tacticFailure["NotDecidable", "The goal `1` is not built from equations and inequalities of natural numbers and the connectives.", data, goal]
		]
	]
}]


(* a rewritten goal a == a is closed by reflexivity *)
closeIfSidesSame[data_, goal_, type_] := If[
	MatchQ[type, application[application[application[constantReference[equality_, _], _], side_], side_] /; equalityTypeQ[data["Environment"], equality]],
	reflexivity[data, goal],
	data
]


(* ::Subsection:: *)
(*Induction*)


(* The recursor of the variable's type, applied to its parameters, the goal as a function of the
   variable's indices and the variable (the motive), one new goal per constructor (the minor premises),
   the indices and the variable itself. The indices must be distinct variables. The hypotheses that
   depend on the variable or its indices are reverted into the motive, so each new goal, the goal for
   that constructor, states them again, and so does each induction hypothesis: the recursor's result is
   applied to them. "Induction" gives each new goal the minor premise's type, the constructor's fields
   and an induction hypothesis per recursive field; "Cases" gives it the fields alone. *)
eliminate[data_, goal_, variableName_HoldComplete, mode : "Induction" | "Cases"] := Module[
	{
		current = currentGoal[data, goal], environment = data["Environment"], context, id, head, arguments, inductiveName,
		inductiveRecord, recursorRecord, parameters, indices, eliminated, dependents, goalBody, eliminationLevel,
		recursorLevels, motive, minorTypes, caseIds, premises
	},
	context = current["Context"];
	id = hypothesisId[data, goal, context, variableName];
	{head, arguments} = applicationSpine[weakHeadNormalForm[environment, context, context[id]["Type"]]];
	inductiveName = Replace[head, {
		constantReference[name_, _] /; constantRecord[environment, name]["Kind"] === "InductiveType" :> name,
		_ :> tacticFailure["InductiveTypeExpected", "In the goal `1`, the type of `2` is not an inductive type.", data, goal, {HoldForm @@ variableName}]
	}];
	inductiveRecord = constantRecord[environment, inductiveName];
	recursorRecord = constantRecord[environment, recursorName[inductiveName]];
	If[ recursorRecord["NumberOfMotives"] > 1,
		tacticFailure["MutualInduction", "In the goal `1`, `2` is one of a block of mutually inductive or nested types, which induction does not handle yet.", data, goal, {HoldForm @@ inductiveName}]
	];
	parameters = Take[arguments, inductiveRecord["NumberOfParameters"]];
	indices = Drop[arguments, inductiveRecord["NumberOfParameters"]];
	If[ ! (MatchQ[indices, {___freeVariable}] && DuplicateFreeQ[indices] && FreeQ[parameters, Alternatives @@ indices]),
		tacticFailure["IndexNotVariable", "In the goal `1`, an index of the type of `2` is not a variable of its own; generalize it first.", data, goal, {HoldForm @@ variableName}]
	];
	eliminated = Append[First /@ indices, id];
	dependents = dependentHypotheses[context, eliminated];
	goalBody = makeDependentFunctionType[context, dependents, current["Type"]];
	eliminationLevel = sortLevel[environment, context, goalBody];
	If[ ! TrueQ[recursorRecord["EliminationUniverse"]] && ! levelEquivalentQ[eliminationLevel, 0],
		tacticFailure["LargeElimination", "In the goal `1`, `2` can only be eliminated into a proposition.", data, goal, {HoldForm @@ inductiveName}]
	];
	recursorLevels = If[TrueQ[recursorRecord["EliminationUniverse"]], Prepend[Last[head], eliminationLevel], Last[head]];
	motive = makeLambda[context, eliminated, goalBody];
	minorTypes = minorPremiseTypes[
		instantiateUniverseParameters[recursorRecord["Type"], recursorRecord["UniverseParameters"], recursorLevels],
		parameters,
		motive,
		recursorRecord["NumberOfMinors"]
	];
	caseIds = Table[freshMetavariableId[], Length[minorTypes]];
	premises = MapThread[
		Function[{caseId, minor}, If[ mode === "Induction",
			{metavariable[caseId], Last[minor]},
			casePremise[KeyDrop[context, Join[eliminated, dependents]], caseId, Last[minor], constructorFieldCounts[environment, First[minor], inductiveRecord]]
		]],
		{caseIds, minorTypes}
	];
	solveGoal[
		data,
		goal,
		makeApplication[
			constantReference[recursorName[inductiveName], recursorLevels],
			Join[parameters, {motive}, First /@ premises, indices, {freeVariable[id]}, freeVariable /@ dependents]
		],
		MapThread[
			Function[{caseId, minor, premise}, caseId -> <|"Context" -> KeyDrop[context, Join[eliminated, dependents]], "Type" -> Last[premise], "Case" -> First[minor]|>],
			{caseIds, minorTypes, premises}
		]
	]
]

(* the latest hypothesis of the goal with the given name *)
hypothesisId[data_, goal_, context_, name_HoldComplete] := Replace[
	SelectFirst[Reverse @ Keys[context], Function[key, context[key]["Name"] === name], None],
	None :> tacticFailure["UnknownHypothesis", "The goal `1` has no hypothesis `2`.", data, goal, {HoldForm @@ name}]
]

(* the hypotheses other than ids whose types mention them, or a hypothesis so found, in the order of the context *)
dependentHypotheses[context_Association, ids_List] := Fold[
	Function[{found, key}, If[
		! MemberQ[ids, key] && ! FreeQ[context[key]["Type"], freeVariable[Alternatives @@ Join[ids, found]]],
		Append[found, key],
		found
	]],
	{},
	Keys[context]
]

(* {fields, recursive fields} of the constructor: the fields that end in a type of the inductive's block get an
   induction hypothesis each *)
constructorFieldCounts[environment_, constructor_HoldComplete, inductiveRecord_Association] := With[
	{record = constantRecord[environment, constructor]},
	With[{domains = Take[binderDomains[record["Type"]], {record["NumberOfParameters"] + 1, record["NumberOfParameters"] + record["NumberOfFields"]}]},
		{record["NumberOfFields"], Count[domains, domain_ /; MemberQ[inductiveRecord["Block"], conclusionName[domain]]]}
	]
]

binderDomains[dependentFunctionType[_, domain_, codomain_, _]] := Prepend[binderDomains[codomain], domain]
binderDomains[_] := {}

(* the constant at the head of a type's conclusion, past its binders *)
conclusionName[dependentFunctionType[_, _, codomain_, _]] := conclusionName[codomain]
conclusionName[type_] := Replace[First[applicationSpine[type]], {constantReference[name_, _] :> name, _ -> None}]

(* For "Cases", the minor premise (fields, hypotheses) ↦ solution[fields], and its goal (fields) ↦ P[c fields]:
   the induction hypotheses are left out, for nothing in the goal depends on them. *)
casePremise[context_, caseId_, minorType_, {fieldCount_Integer, hypothesisCount_Integer}] := Module[
	{fieldContext, fieldIds, afterFields, hypothesisContext, hypothesisIds, body},
	{fieldContext, fieldIds, afterFields} = openBinders[context, minorType, fieldCount];
	{hypothesisContext, hypothesisIds, body} = openBinders[fieldContext, afterFields, hypothesisCount];
	{
		makeLambda[hypothesisContext, Join[fieldIds, hypothesisIds], makeApplication[metavariable[caseId], freeVariable /@ fieldIds]],
		makeDependentFunctionType[fieldContext, fieldIds, body]
	}
]

(* the first count binders of a function type opened as new variables: {context, {id, ...}, the rest} *)
openBinders[context_, type_, 0] := {context, {}, type}
openBinders[context_, dependentFunctionType[name_, domain_, codomain_, binder_], count_Integer] := With[{id = freshFreeVariable[]},
	Replace[
		openBinders[extendContext[context, id, name, domain, binder], instantiateBoundVariable[codomain, freeVariable[id]], count - 1],
		{opened_, ids_, rest_} :> {opened, Prepend[ids, id], rest}
	]
]


(* The hypotheses named, with every hypothesis that depends on them, go back into the goal as a function
   type, in the order of the context; the goal's solution is the new goal applied to them. *)
generalize[data_, goal_, names_List] := With[{current = currentGoal[data, goal], newGoal = freshMetavariableId[]},
	With[{named = Function[name, hypothesisId[data, goal, current["Context"], name]] /@ names},
		With[{reverted = Select[Keys[current["Context"]], Function[key, MemberQ[Join[named, dependentHypotheses[current["Context"], named]], key]]]},
			solveGoal[
				data,
				goal,
				makeApplication[metavariable[newGoal], freeVariable /@ reverted],
				{newGoal -> <|
					"Context" -> KeyDrop[current["Context"], reverted],
					"Type" -> makeDependentFunctionType[current["Context"], reverted, current["Type"]],
					"Case" -> None
				|>}
			]
		]
	]
]


(* the first constructor of the goal's inductive type that applies to the goal, as "Apply" applies it *)
constructorTactic[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	Replace[First[applicationSpine[weakHeadNormalForm[environment, current["Context"], current["Type"]]]], {
		constantReference[name_, _] /; constantRecord[environment, name]["Kind"] === "InductiveType" :>
			firstConstructorApplied[data, goal, constantRecord[environment, name]["Constructors"]],
		_ :> tacticFailure["InductiveTypeExpected", "The goal `1` is not an inductive type.", data, goal]
	}]
]

firstConstructorApplied[data_, goal_, {}] := tacticFailure["NoConstructorApplies", "No constructor of its type applies to the goal `1`.", data, goal]
firstConstructorApplied[data_, goal_, {constructor_HoldComplete, rest___}] := Replace[
	Quiet @ catchKernelFailure[applyTerm[data, goal, constructor]],
	_Failure :> firstConstructorApplied[data, goal, {rest}]
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
