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
	"Hole", annotation      closes the goal with a hole, a proof left to give, which the theorem declares (Holes.wl)
	"Rewrite", h            replaces the first instance in the goal of the left side of the equation h, and every
	                        copy of it, by the right side; "Rewrite", h, "RightToLeft" replaces the right side;
	                        with "At" -> k last, it rewrites the hypothesis k instead
	"Change", statement     replaces the goal by a statement equal to it by computation
	"Simplify", {h, ...}    rewrites with the equations h, ... until none applies, then closes an equation whose
	                        sides are equal by computation; a definition among them unfolds where it computes
	"Decide"                proves a closed statement by computing its decision, the instance of Decidable found:
	                        the prelude's decide equations and inequalities of natural numbers and the connectives
	"FindInstance"          proves an existential statement over the natural numbers with witnesses that
	                        Wolfram's FindInstance finds, the instance proved by "Decide"
	"Ring"                  proves an equation of natural numbers that holds in every commutative semiring, by
	                        normal forms with proofs from the prelude's laws (Ring.wl); an equation of the
	                        integers of TypeTheoryEnvironment["Integers"] that holds in every commutative ring,
	                        by normal forms with proofs from the integers' laws, or, in an environment without
	                        all of them, by induction on the class of each integer variable, the soundness of
	                        quotients, and the equation of natural numbers of the pairs
	"PolynomialReduce"      proves an equation of natural numbers from the equations among the hypotheses by a
	                        polynomial combination, whose cofactors Wolfram finds and "Ring" checks; and an
	                        equation of the integers of TypeTheoryEnvironment["Integers"] from the equations of
	                        integers among them, by a combination with integer cofactors
	"LinearArithmetic"      proves an inequality, an equation or False, of natural numbers, that follows linearly
	                        from the inequalities and equations among the hypotheses, with multipliers Wolfram
	                        finds
	"FindEquationalProof"   proves an equation from the hypotheses that are equations for all values, by replaying
	                        a proof that Wolfram's FindEquationalProof finds (Equational.wl)
	"SumOfSquares"          proves an inequality of the integers of TypeTheoryEnvironment["Integers"], or of natural
	                        numbers there, whose larger side less the smaller is a sum of squares of polynomials up
	                        to a positive factor, which Wolfram finds (SumsOfSquares.wl)

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
TypeTheoryTactic[\"Decide\"] proves a closed statement by computing its decision, the instance of Decidable that elaboration finds: \
the prelude's decide == and <= of natural numbers, And, Or, Not, True and False, and an environment may declare more.\n\
TypeTheoryTactic[\"FindInstance\"] proves Exists[{Typed[x1, Naturals], ...}, p] with witnesses that Wolfram's FindInstance finds, proving p of them by computing its decision.\n\
TypeTheoryTactic[\"Ring\"] proves an equation of natural numbers that holds in every commutative semiring, such as (a + b)^2 == a^2 + 2 a b + b^2, \
and an equation of integers that holds in every commutative ring.\n\
TypeTheoryTactic[\"PolynomialReduce\"] proves an equation of natural numbers from the equations among the hypotheses, by a polynomial combination of them that Wolfram finds.\n\
TypeTheoryTactic[\"LinearArithmetic\"] proves an inequality, an equation or False, of natural numbers, from the inequalities and equations among the hypotheses, \
by a linear combination of them that Wolfram finds.\n\
TypeTheoryTactic[\"FindEquationalProof\"] proves an equation from the hypotheses that are equations of its type for all values of their variables, \
by replaying a proof that Wolfram's FindEquationalProof finds.\n\
TypeTheoryTactic[\"SumOfSquares\"] proves an inequality of integers, or of natural numbers, in TypeTheoryEnvironment[\"Integers\"], such as 2 x y <= x x + y y, \
by a sum of squares of polynomials that Wolfram finds, a positive multiple of its larger side less the smaller."

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

(* a proof's holes go to the declaration being made, which declares a constant for each (Holes.wl) *)
completedProofTerm[TypeTheoryProof[data_Association]] := If[ data["Goals"] =!= {},
	kernelFailure["ProofIncomplete", "The proof has `1` open goals.", {Length[data["Goals"]]}],
	If[ListQ[$elaboratedHoles], $elaboratedHoles = Join[$elaboratedHoles, Values[Lookup[data, "Holes", <||>]]]];
	instantiateProofTerm[data, metavariable[data["Root"]]]
]


(* ::Subsection:: *)
(*Goals*)


instantiateProofTerm[data_, term_] := resolvePendingAbstractions @ ReplaceRepeated[
	term,
	metavariable[id_] /; KeyExistsQ[data["Assignments"], id] :> With[{assigned = data["Assignments"][id]}, assigned /; True]
]

resolvePendingAbstractions[term_] := ReplaceRepeated[
	term,
	pendingAbstraction[context_, ids_, body_] /; FreeQ[body, _pendingAbstraction] :> With[{function = makeLambda[context, ids, body]}, function /; True]
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

(* A goal closed with a hole: a metavariable of no context, of the type Π (hypotheses). goal, applied to the
   hypotheses, which the theorem declared with this proof replaces with a constant (Holes.wl). *)
holeTactic[data_, goal_, annotation_] := Block[{holeGoal = currentGoal[data, goal], holeId = freshMetavariableId[], holeType},
	holeType = makeDependentFunctionType[holeGoal["Context"], Keys[holeGoal["Context"]], holeGoal["Type"]];
	Join[
		solveGoal[data, goal, makeApplication[metavariable[holeId], freeVariable /@ Keys[holeGoal["Context"]]], {}],
		<|"Holes" -> Append[Lookup[data, "Holes", <||>], holeId -> <|"Id" -> holeId, "Type" -> holeType, "Annotation" -> annotation|>]|>
	]
]

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

(* the open goals of the proof, as the metavariables a tactic's elaboration may meet, each with its type and hypotheses;
   a tactic's terms are not checked until it checks them, so the kernel's type queries check *)
SetAttributes[withOpenGoals, HoldRest]
withOpenGoals[data_, body_] := With[{goalTypes = openGoalTypes[data]},
	Block[{$metavariableTypes = goalTypes, $goalMetavariableTypes = goalTypes, $goalMetavariableContexts = openGoalContexts[data], $termsChecked = False},
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
runTactic["FindInstance", Hold[], data_, goal_] := findInstance[data, goal]
runTactic["Ring", Hold[], data_, goal_] := ring[data, goal]
runTactic["PolynomialReduce", Hold[], data_, goal_] := polynomialReduce[data, goal]
runTactic["LinearArithmetic", Hold[], data_, goal_] := linearArithmetic[data, goal]
runTactic["FindEquationalProof", Hold[], data_, goal_] := findEquationalProof[data, goal]
runTactic["SumOfSquares", Hold[], data_, goal_] := sumOfSquares[data, goal]
runTactic["Assumption", Hold[], data_, goal_] := assumption[data, goal]
runTactic["Hole", Hold[annotation___], data_, goal_] /; Length[{annotation}] <= 1 := holeTactic[data, goal, holeAnnotation[{annotation}]]
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
			(* a premise P[x] whose P the conclusion fixed as a function is a redex until beta reduced, which the new
			   goal states it as, as the other tactics state theirs *)
			{newTypes = AssociationMap[Function[id, betaNormalize[instantiateMetavariables[$metavariableTypes[id]]]], newIds]},
			If[ ! FreeQ[{applied, Values[newTypes]}, _levelMetavariable],
				tacticFailure["UnsolvedUniverseLevel", "Could not infer every universe level while applying to the goal `1`.", data, goal]
			];
			(* the partial term is checked now, with its holes standing for terms of their types *)
			Block[{$metavariableTypes = Join[goalTypes, newTypes], $metavariableAssignments = <||>},
				withKernelCaches[checkHasType[environment, current["Context"], applied, instantiateProofTerm[updated, current["Type"]]]]
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


(* like every tactic's comparison, outside the kernel's check, so the type queries check *)
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


(* outside the kernel's check, so the type queries check *)
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
	(* the subterm the side unified with may be equal to the instance only by computation, as m 2 is to m (1 + 1),
	   so every subterm equal to it is abstracted, not only its copies; a goal with none left has no instance *)
	motiveBody = withKernelCaches[abstractInstances[instantiateMetavariables[target], instance, instanceOfQ[environment, context, instance]]];
	If[ ! boundVariableOccursQ[motiveBody, 0],
		tacticFailure["NoInstance", "The goal `1` has no instance of `2`.", data, goal, {displayCoreTerm[environment, context, instance]}]
	];
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
				catchKernelFailure[withKernelCaches[checkHasType[environment, context, solution, instantiateProofTerm[updated, current["Type"]]]]]
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
			catchKernelFailure[withKernelCaches[checkHasType[environment, context, proof, rewritten["Statement"]]]]
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
		Construct[application, pendingAbstraction[newContext, {newId}, metavariable[newGoal]], proof],
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
transportBackward[rewritten_Association, context_, m_] := Construct[
	application,
	makeApplication[rewritten["Recursor"], {
		rewritten["Type"],
		rewritten["Left"],
		rewriteMotive[context, rewritten["Equality"], rewritten["Levels"], rewritten["Type"], rewritten["Left"], rewritten["Motive"], rewritten["Left"]],
		Construct[lambdaAbstraction, HoldComplete[p], instantiateBoundVariable[rewritten["Motive"], rewritten["Left"]], boundVariable[0], "Explicit"],
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

(* term with every copy of instance, or with a test every subterm the test takes, replaced by the variable of a
   binder just outside it *)
abstractInstances[term_, instance_] := abstractInstances[term, instance, Function[candidate, candidate === instance]]
abstractInstances[term_, instance_, instanceQ_] := Block[{$instanceMemo = <||>}, abstractInstance[term, instanceQ, 0]]

abstractInstance[term_, instanceQ_, depth_] := Lookup[
	$instanceMemo,
	Key[{term, depth}],
	$instanceMemo[{term, depth}] = If[instanceQ[term], boundVariable[depth], abstractInstanceBelow[term, instanceQ, depth]]
]

abstractInstanceBelow[application[function_, argument_], instanceQ_, depth_] :=
	Construct[application, abstractInstance[function, instanceQ, depth], abstractInstance[argument, instanceQ, depth]]
abstractInstanceBelow[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_], instanceQ_, depth_] :=
	Construct[head, name, abstractInstance[domain, instanceQ, depth], abstractInstance[body, instanceQ, depth + 1], binder]
abstractInstanceBelow[localDefinition[name_, type_, value_, body_], instanceQ_, depth_] :=
	Construct[localDefinition, name, abstractInstance[type, instanceQ, depth], abstractInstance[value, instanceQ, depth], abstractInstance[body, instanceQ, depth + 1]]
abstractInstanceBelow[projection[structure_, index_, inner_], instanceQ_, depth_] := Construct[projection, structure, index, abstractInstance[inner, instanceQ, depth]]
abstractInstanceBelow[term_, _, _] := term

(* The subterms a rewrite takes for its instance, as Lean's kabstract takes them: a copy, or a subterm with no
   variable of a binder inside the goal and no hole, with the instance's head and number of arguments, equal to it
   without unfolding a definition. Lean compares them at instances transparency, so a subterm equal to the instance
   only once a definition unfolds is no instance: a full test could unfold far, and leave a motive that is not well
   typed. *)
instanceOfQ[environment_, context_, instance_] := With[{key = instancePatternKey[instance], closedQ = FreeQ[instance, _metavariable]},
	Function[candidate, Or[
		candidate === instance,
		closedQ && looseBoundRange[candidate] == 0 && FreeQ[candidate, _metavariable] && instancePatternKey[candidate] === key && equalWithoutUnfoldingQ[environment, context, candidate, instance]
	]]
]

(* two closed terms equal without unfolding a definition: the same, the same number by arithmetic on literals, or
   the same head applied to arguments equal in the same way. m 2 and m (1 + 1) are; Doubled[2] + 1 and 4 + 1 are not,
   as Doubled must unfold, which reducing the head Plus would do to its arguments. *)
equalWithoutUnfoldingQ[environment_, context_, a_, b_] := Or[
	a === b,
	With[{valueA = literalValue[environment, context, a]}, valueA =!= None && valueA === literalValue[environment, context, b]],
	With[{spineA = applicationSpine[a], spineB = applicationSpine[b]},
		And[
			Last[spineA] =!= {},
			First[spineA] === First[spineB],
			Length[Last[spineA]] == Length[Last[spineB]],
			AllTrue[Transpose[{Last[spineA], Last[spineB]}], Function[pair, equalWithoutUnfoldingQ[environment, context, First[pair], Last[pair]]]]
		]
	]
]

(* the literal a term computes to by the registered operations on literals alone, or None *)
literalValue[_, _, literal_naturalLiteral] := literal
literalValue[environment_, context_, term_] := With[{spine = applicationSpine[term]},
	If[ MatchQ[First[spine], _constantReference] && Last[spine] =!= {},
		With[{arguments = Function[argument, literalValue[environment, context, argument]] /@ Last[spine]},
			If[FreeQ[arguments, None], Replace[literalOperationResult[environment, context, First[First[spine]], arguments], Except[_naturalLiteral] -> None], None]
		],
		None
	]
]

(* the recursor of the type of equations, eliminating into the sort of the goal *)
equationRecursor[data_, goal_, context_, equality_, levels_List, target_] := With[
	{record = constantRecord[data["Environment"], recursorName[equality]], eliminationLevel = sortLevel[data["Environment"], context, target]},
	If[ ! TrueQ[record["EliminationUniverse"]] && ! levelEquivalentQ[eliminationLevel, 0],
		tacticFailure["LargeElimination", "In the goal `1`, the equation can only rewrite a proposition.", data, goal]
	];
	constantReference[recursorName[equality], If[TrueQ[record["EliminationUniverse"]], Prepend[levels, motiveUniverse[data, goal, eliminationLevel]], levels]]
]

(* The universe parameter of a recursor whose motive goes into a goal of level level. Under rules with Prop a
   motive goes into Sort u, so u is the goal's level; without Prop it goes into Type u, which is Sort (u + 1),
   so u is one level less (InductiveTypes.wl builds the motive so). *)
motiveUniverse[data_, goal_, level_] := If[ rulesSetting[data["Environment"], "Prop"],
	level,
	Replace[levelPredecessor[normalizeLevel[level]], None :> tacticFailure[
		"MotiveUniverse",
		"In the goal `1`, the universe level `2` of the goal has no level below it, which a motive into a Type needs.",
		data,
		goal,
		{level}
	]]
]

(* l - 1 for a canonical level l >= 1 that has one, or None, as for a parameter u, which may be 0 *)
levelPredecessor[n_Integer /; n >= 1] := n - 1
levelPredecessor[levelSuccessor[base_, 1]] := base
levelPredecessor[levelSuccessor[base_, k_Integer /; k > 1]] := levelSuccessor[base, k - 1]
levelPredecessor[levelMaximum[levels__]] := With[{predecessors = levelPredecessor /@ {levels}}, If[MemberQ[predecessors, None], None, normalizeLevel[levelMaximum @@ predecessors]]]
levelPredecessor[_] := None

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
			Construct[dependentFunctionType, HoldComplete[p], atVariable, instantiateBoundVariable[motiveBody, result], "Explicit"]
		]]
	]
]

(* ::Subsection:: *)
(*Change, Simplify and Decide*)


(* The goal replaced by a statement equal to it by computation, which a rewrite can then reach into: the
   new goal's solution solves the goal as it is. The comparison is outside the kernel's check, so its type
   queries check. *)
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

(* the state with the goal closed by reflexivity, or None *)
closedByReflexivity[state_, goal_] := Replace[
	withOpenGoals[state, Quiet @ catchKernelFailure[reflexivity[state, goal]]],
	_Failure -> None
]


(* A closed proposition gets its decision from the instances of Decidable[p], as Lean's decide: the
   prelude's decide == and <= on the natural numbers, And, Or, Not, True and False, and an environment may
   declare more; the kernel computes Decide of it to True, and DecideSoundness turns
   EqualityReflexivity[True] into a proof of the goal. *)
decide[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	If[ ! AllTrue[$decisionConstants, Function[name, constantDeclaredQ[environment, name]]],
		tacticFailure["DecisionUnavailable", "The environment of the goal `1` lacks the decisions of the prelude.", data, goal]
	];
	With[{decision = findInstance[environment, current["Context"], makeApplication[preludeConstant[Decidable], {current["Type"]}]]},
		If[ decision === None,
			tacticFailure["NotDecidable", "No instance of Decidable decides the goal `1`.", data, goal]
		];
		(* the computation of a closed decision remembers its steps, as a kernel check does *)
		Replace[withKernelCaches[weakHeadNormalForm[environment, current["Context"], makeApplication[preludeConstant[Decide], {current["Type"], decision}]]], {
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

$decisionConstants = HoldComplete /@ Unevaluated[{Decidable, Decide, DecideSoundness, Booleans, "true", EqualityReflexivity}]

SetAttributes[preludeConstant, HoldAll]
preludeConstant[name_] := constantReference[HoldComplete[name], {}]


(* ::Subsection:: *)
(*Ring*)


(* An equation of natural numbers that holds in every commutative semiring: both sides are normalized to
   polynomials in their atoms, with proofs from the prelude's laws (Ring.wl), and the kernel checks the
   proof before it closes the goal. *)
ring[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	If[ ! AllTrue[$ringConstants, Function[name, constantDeclaredQ[environment, name]]],
		tacticFailure["RingUnavailable", "The environment of the goal `1` lacks the arithmetic of the prelude and its laws.", data, goal]
	];
	Replace[weakHeadNormalForm[environment, current["Context"], current["Type"]], {
		application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] /; naturalNumberTypeQ[environment, current["Context"], type] :>
			Replace[ringEquationProof[arithmeticReduced[environment, current["Context"], left], arithmeticReduced[environment, current["Context"], right]], {
				None :> tacticFailure["NotRingEquation", "The two sides of the goal `1` are not equal in every commutative semiring.", data, goal],
				proof_ :> solvedByCheckedProof[data, goal, current, proof]
			}],
		application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] /; integerTypeQ[environment, type] && integerRingAvailableQ[environment] :>
			Replace[integerRingEquationProof[integerArithmeticReduced[environment, current["Context"], left], integerArithmeticReduced[environment, current["Context"], right]], {
				None :> tacticFailure["NotRingEquation", "The two sides of the goal `1` are not equal in every commutative ring.", data, goal],
				proof_ :> solvedByCheckedProof[data, goal, current, proof]
			}],
		application[application[application[constantReference[HoldComplete[Equal], _], type_], _], _] /; integerTypeQ[environment, type] :>
			classRing[data, goal, current, integerTypeQ],
		application[application[application[constantReference[HoldComplete[Equal], _], type_], _], _] /; rationalTypeQ[environment, type] :>
			classRing[data, goal, current, rationalTypeQ],
		_ :> tacticFailure["EquationExpected", "The goal `1` is not an equation of natural numbers, integers or rationals.", data, goal]
	}]
]

(* A term of integers with its atoms reduced as those of natural numbers are, the natural numbers it casts
   included: a field of a pair written out is the term in it *)
integerArithmeticReduced[environment_, context_, term_] := Replace[term, {
	application[application[head : constantReference[HoldComplete["integerAddition" | "integerMultiplication" | "integerSubtraction"], _], a_], b_] :>
		makeApplication[head, {integerArithmeticReduced[environment, context, a], integerArithmeticReduced[environment, context, b]}],
	application[application[head : constantReference[HoldComplete["integerPower"], _], a_], b_] :>
		makeApplication[head, {integerArithmeticReduced[environment, context, a], arithmeticReduced[environment, context, b]}],
	application[head : constantReference[HoldComplete["integerNegation"], _], a_] :> Construct[application, head, integerArithmeticReduced[environment, context, a]],
	application[head : constantReference[HoldComplete["integerOfNatural"], _], a_] :> Construct[application, head, arithmeticReduced[environment, context, a]],
	_ :> With[{reduced = reducedHeadWithoutUnfolding[environment, context, term]},
		If[reduced === term, term, integerArithmeticReduced[environment, context, reduced]]
	]
}]

(* A term of natural numbers with its atoms, the subterms that are no sum, product, power or successor,
   reduced as far as they reduce without unfolding a definition: a field of a pair written out is the
   term in it, Pair[a, b][[1]] is a. The term is equal to it by computation, which is all the kernel
   needs of a proof built from the reduced one. *)
arithmeticReduced[environment_, context_, term_] := Replace[term, {
	application[application[head : constantReference[HoldComplete[Plus | Times | Power], _], a_], b_] :>
		makeApplication[head, {arithmeticReduced[environment, context, a], arithmeticReduced[environment, context, b]}],
	application[head : constantReference[HoldComplete[NaturalNumberSuccessor], _], a_] :> Construct[application, head, arithmeticReduced[environment, context, a]],
	_ :> With[{reduced = reducedHeadWithoutUnfolding[environment, context, term]},
		If[reduced === term, term, arithmeticReduced[environment, context, reduced]]
	]
}]

(* the goal solved by a proof that the kernel checks first; the proof shares its subterms many times
   over, which the kernel's caches check once *)
solvedByCheckedProof[data_, goal_, current_, proof_] := (
	Replace[catchKernelFailure[withKernelCaches[checkHasType[data["Environment"], current["Context"], proof, current["Type"]]]],
		_Failure :> tacticFailure["ProofRejected", "The kernel rejects the proof built for the goal `1`.", data, goal]
	];
	solveGoal[data, goal, proof, {}]
)

$ringConstants = HoldComplete /@ Unevaluated[{
	NonNegativeIntegers, Plus, Times, Power, Equal, EqualityReflexivity, EqualitySymmetry, EqualityTransitivity, EqualityCongruence,
	AdditionAssociativity, AdditionCommutativity, AdditionZeroLeft, AdditionZeroRight, MultiplicationAssociativity, MultiplicationCommutativity,
	MultiplicationZeroLeft, MultiplicationZeroRight, MultiplicationOneLeft, MultiplicationDistributivityLeft, MultiplicationDistributivityRight,
	PowerZero, PowerOne, PowerSuccessor, PowerAddition
}]

(* ::Subsection:: *)
(*Wolfram oracles*)


(* These tactics ask Wolfram for what a proof needs, and the kernel checks the proof built from the
   answer: a wrong answer makes the tactic fail, and can never make a false statement a theorem.

   "FindInstance": for a goal Exists[{Typed[x1, Naturals], ...}, p], with p built from == and <= of
   arithmetic on the variables and literals, and the connectives, Wolfram's FindInstance finds the
   witnesses over the natural numbers. ExistsIntroduction takes them, and "Decide" proves p of them by
   computing; an instance it cannot decide is left as the new goal. *)
findInstance[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	If[ ! AllTrue[$oracleConstants, Function[name, constantDeclaredQ[environment, name]]],
		tacticFailure["OracleUnavailable", "The environment of the goal `1` lacks the natural numbers and existential statements of the prelude.", data, goal]
	];
	With[{existentials = existentialPrefix[environment, current["Context"], current["Type"], <||>]},
		If[ First[existentials] === <||>,
			tacticFailure["ExistentialExpected", "The goal `1` is not an existential statement over the natural numbers.", data, goal]
		];
		With[{witnesses = foundWitnesses[data, goal, existentials]},
			{newGoal = freshMetavariableId[]},
			{witnessed = witnessedProof[environment, current["Context"], current["Type"], witnesses, newGoal]},
			decidedInstance[
				solveGoal[data, goal, First[witnessed], {newGoal -> <|"Context" -> current["Context"], "Type" -> Last[witnessed], "Case" -> None|>}],
				newGoal
			]
		]
	]
]

$oracleConstants = HoldComplete /@ Unevaluated[{Exists, ExistsIntroduction, NonNegativeIntegers, Equal, LessEqual}]

(* {<|id -> variable, ...|>, body}: the variables of the existential statements over the natural numbers
   at the head of statement, outermost first, each a fresh free variable of the body standing for the
   Wolfram variable given *)
existentialPrefix[environment_, context_, statement_, variables_Association] := Replace[weakHeadNormalForm[environment, context, statement], {
	application[application[constantReference[HoldComplete[Exists], _], type_], predicate_] /; naturalNumberTypeQ[environment, context, type] :>
		With[{id = freshFreeVariable[]},
			existentialPrefix[
				environment,
				extendContext[context, id, HoldComplete[x], type, "Explicit"],
				betaNormalize[application[predicate, freeVariable[id]]],
				Append[variables, id -> Subscript[\[FormalX], Length[variables] + 1]]
			]
		],
	_ :> {variables, statement, context}
}]

naturalNumberTypeQ[environment_, context_, type_] := MatchQ[weakHeadNormalForm[environment, context, type], constantReference[HoldComplete[NonNegativeIntegers], _]]

(* the integers of TypeTheoryEnvironment["Integers"], a quotient of pairs of natural numbers *)
integerTypeQ[environment_, type_] := type === constantReference[HoldComplete[Integers], {}] && constantDeclaredQ[environment, HoldComplete["integerRelation"]]

rationalTypeQ[environment_, type_] := type === constantReference[HoldComplete[Rationals], {}] && constantDeclaredQ[environment, HoldComplete["rationalRelation"]]

(* Where the environment lacks the laws the integers' normal forms are built from, as while the integers'
   library is built, and for the rationals: an equation of integers is one of classes once each integer
   variable it mentions is the class of a pair, and the soundness of quotients makes it the relation of the
   two pairs, an equation of natural numbers that holds in every commutative semiring where the integers'
   holds in every commutative ring; an equation of rationals likewise gives an equation of integers. The
   equation is first a goal with only the hypotheses it mentions, so that no other hypothesis is
   generalized with a variable into the goal of its classes. *)
classRing[data_, goal_, current_, typeQ_] := With[{narrowedGoal = freshMetavariableId[], context = neededContext[current["Context"], current["Type"]]},
	{
		narrowed = solveGoal[data, goal, metavariable[narrowedGoal], {narrowedGoal -> <|"Context" -> context, "Type" -> current["Type"], "Case" -> None|>}],
		variables = Select[Keys[context], Function[id, And[
			typeQ[data["Environment"], context[id]["Type"]],
			! FreeQ[current["Type"], freeVariable[id]]
		]]]
	},
	Replace[
		catchKernelFailure @ With[
			{
				classes = Fold[
					Function[{state, id}, With[{eliminated = eliminate[state, First[state["Goals"]], context[id]["Name"], "Induction"]},
						introduceVariable[eliminated, First[eliminated["Goals"]], Automatic]
					]],
					narrowed,
					variables
				]
			},
			With[{related = applyTerm[classes, First[classes["Goals"]], HoldComplete[QuotientSoundness]]},
				ring[related, First[related["Goals"]]]
			]
		],
		_Failure :> tacticFailure["NotRingEquation", "The two sides of the goal `1` are not equal in every commutative ring.", data, goal]
	]
]

(* the hypotheses that term mentions, with those that their types and values mention, in order *)
neededContext[context_Association, term_] := With[
	{
		needed = FixedPoint[
			Function[ids, Union[ids, mentionedFreeVariables[Function[id, {context[id]["Type"], Lookup[context[id], "Value", {}]}] /@ ids]]],
			Intersection[mentionedFreeVariables[term], Keys[context]]
		]
	},
	KeySelect[context, Function[id, MemberQ[needed, id]]]
]

mentionedFreeVariables[term_] := Union[Cases[term, freeVariable[id_] :> id, {0, Infinity}]]

(* the witnesses FindInstance finds for the variables, in order, or a Failure *)
foundWitnesses[data_, goal_, {variables_Association, body_, context_}] := With[
	{condition = wolframCondition[data, goal, context, variables, body]},
	Replace[
		TimeConstrained[Quiet @ FindInstance[condition && And @@ Thread[Values[variables] >= 0], Values[variables], Integers], 10, $Aborted],
		{
			{solution_List, ___} /; AllTrue[ReplaceAll[Values[variables], solution], Function[value, IntegerQ[value] && value >= 0]] :> ReplaceAll[Values[variables], solution],
			{} :> tacticFailure["NoInstance", "Wolfram's FindInstance finds no natural numbers that make the goal `1` true.", data, goal],
			_ :> tacticFailure["NoInstance", "Wolfram's FindInstance finds no instance of the goal `1` in ten seconds.", data, goal]
		}
	]
]

(* the proposition as a condition on the Wolfram variables; a definition such as Less or Unequal is
   unfolded to find its form *)
wolframCondition[data_, goal_, context_, variables_, proposition_] := Replace[proposition, {
	application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] /; naturalNumberTypeQ[data["Environment"], context, type] :>
		wolframExpression[data, goal, variables, left] == wolframExpression[data, goal, variables, right],
	application[application[constantReference[HoldComplete[LessEqual], _], left_], right_] :>
		wolframExpression[data, goal, variables, left] <= wolframExpression[data, goal, variables, right],
	application[application[constantReference[HoldComplete[And], _], left_], right_] :>
		wolframCondition[data, goal, context, variables, left] && wolframCondition[data, goal, context, variables, right],
	application[application[constantReference[HoldComplete[Or], _], left_], right_] :>
		wolframCondition[data, goal, context, variables, left] || wolframCondition[data, goal, context, variables, right],
	constantReference[HoldComplete[True], _] :> True,
	constantReference[HoldComplete[False], _] :> False,
	dependentFunctionType[_, premise_, constantReference[HoldComplete[False], _], _] :> ! wolframCondition[data, goal, context, variables, premise],
	other_ :> With[{reduced = weakHeadNormalForm[data["Environment"], context, other]},
		If[ reduced =!= other,
			wolframCondition[data, goal, context, variables, reduced],
			tacticFailure["NotTranslatable", "The goal `1` is not built from == and <= of arithmetic on natural numbers and the connectives.", data, goal]
		]
	]
}]

(* subtraction of natural numbers stops at 0 *)
wolframExpression[data_, goal_, variables_, term_] := Replace[term, {
	freeVariable[id_] /; KeyExistsQ[variables, id] :> variables[id],
	naturalLiteral[n_Integer] :> n,
	constantReference[HoldComplete[NaturalNumberZero], _] :> 0,
	application[constantReference[HoldComplete[NaturalNumberSuccessor], _], argument_] :> wolframExpression[data, goal, variables, argument] + 1,
	application[application[constantReference[HoldComplete[operation : Plus | Times | Power | Subtract], _], left_], right_] :> With[
		{first = wolframExpression[data, goal, variables, left], second = wolframExpression[data, goal, variables, right]},
		Replace[operation, {Plus :> first + second, Times :> first * second, Power :> first ^ second, Subtract :> Max[first - second, 0]}]
	],
	_ :> tacticFailure["NotTranslatable", "In the goal `1`, the term `2` is not arithmetic on the variables and natural number literals.", data, goal, {displayCoreTerm[data["Environment"], <||>, term]}]
}]

(* {proof, instance}: ExistsIntroduction applied to each witness in turn, the statement left for the
   last being instance, whose proof is the metavariable newGoal *)
witnessedProof[environment_, context_, statement_, {}, newGoal_] := {metavariable[newGoal], statement}
witnessedProof[environment_, context_, statement_, {witness_, rest___}, newGoal_] := Replace[weakHeadNormalForm[environment, context, statement], {
	application[application[constantReference[HoldComplete[Exists], levels_], type_], predicate_] :> With[
		{inner = witnessedProof[environment, context, betaNormalize[application[predicate, naturalLiteral[witness]]], {rest}, newGoal]},
		{makeApplication[constantReference[HoldComplete[ExistsIntroduction], levels], {type, predicate, naturalLiteral[witness], First[inner]}], Last[inner]}
	]
}]

(* "PolynomialReduce": an equation of natural numbers that follows from the equations among the
   hypotheses by a polynomial combination, whose cofactors Wolfram's PolynomialReduce, or else linear
   algebra, finds (Ring.wl); or an equation of integers from the equations of integers among them *)
polynomialReduce[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	If[ ! AllTrue[Join[$ringConstants, HoldComplete /@ Unevaluated[{Subtract, AdditionSubtractionCancellation}]], Function[name, constantDeclaredQ[environment, name]]],
		tacticFailure["RingUnavailable", "The environment of the goal `1` lacks the arithmetic of the prelude and its laws.", data, goal]
	];
	Replace[weakHeadNormalForm[environment, current["Context"], current["Type"]], {
		application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] /; naturalNumberTypeQ[environment, current["Context"], type] :>
			Replace[ringCombinationProof[arithmeticReduced[environment, current["Context"], left], arithmeticReduced[environment, current["Context"], right], equationHypotheses[environment, current["Context"]]], {
				None :> tacticFailure[
					"NoCombination",
					"Wolfram finds no polynomial combination of the equations among the hypotheses that gives the goal `1`.",
					data,
					goal
				],
				proof_ :> solvedByCheckedProof[data, goal, current, proof]
			}],
		application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] /; integerTypeQ[environment, type] && integerRingAvailableQ[environment] :>
			Replace[integerCombinationProof[
				integerArithmeticReduced[environment, current["Context"], left],
				integerArithmeticReduced[environment, current["Context"], right],
				integerEquationHypotheses[environment, current["Context"]]
			], {
				None :> tacticFailure[
					"NoCombination",
					"Wolfram finds no polynomial combination with integer cofactors of the equations among the hypotheses that gives the goal `1`.",
					data,
					goal
				],
				proof_ :> solvedByCheckedProof[data, goal, current, proof]
			}],
		_ :> tacticFailure["EquationExpected", "The goal `1` is not an equation of natural numbers or of integers.", data, goal]
	}]
]

(* "LinearArithmetic": an inequality, an equation or False, of natural numbers, that follows linearly
   from the inequalities and equations among the hypotheses, each monomial counted as a variable;
   Wolfram's FindInstance finds the multipliers, and "Ring" checks the sum (Ring.wl) *)
linearArithmetic[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	If[ ! AllTrue[Join[$ringConstants, $linearConstants], Function[name, constantDeclaredQ[environment, name]]],
		tacticFailure["RingUnavailable", "The environment of the goal `1` lacks the arithmetic of the prelude and its laws.", data, goal]
	];
	With[{inequalities = inequalityHypotheses[environment, current["Context"]]},
		Replace[
			Replace[weakHeadNormalForm[environment, current["Context"], current["Type"]], {
				application[application[constantReference[HoldComplete[LessEqual], _], left_], right_] :>
					ringLinearProof[arithmeticReduced[environment, current["Context"], left], arithmeticReduced[environment, current["Context"], right], inequalities],
				application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] /; naturalNumberTypeQ[environment, current["Context"], type] :>
					With[
						{
							one = ringLinearProof[arithmeticReduced[environment, current["Context"], left], arithmeticReduced[environment, current["Context"], right], inequalities],
							other = ringLinearProof[arithmeticReduced[environment, current["Context"], right], arithmeticReduced[environment, current["Context"], left], inequalities]
						},
						If[one === None || other === None, None, makeApplication[constantReference[HoldComplete[LessEqualAntisymmetry], {}], {left, right, one, other}]]
					],
				constantReference[HoldComplete[False], _] :> ringContradictionProof[inequalities],
				_ :> tacticFailure["InequalityExpected", "The goal `1` is not an inequality or an equation of natural numbers, or False.", data, goal]
			}],
			{
				None :> tacticFailure["NoLinearCombination", "Wolfram finds no linear combination of the inequalities among the hypotheses that gives the goal `1`.", data, goal],
				proof_ :> solvedByCheckedProof[data, goal, current, proof]
			}
		]
	]
]

$linearConstants = HoldComplete /@ Unevaluated[{
	LessEqual, Less, Or, FalseElimination, EqualitySubstitution, LessEqualReflexivity, LessEqualZero, LessEqualTotality, AdditionMonotonicity, MultiplicationMonotonicity,
	LessEqualTransitivity, LessEqualAddition, LessIrreflexivity, LessEqualAntisymmetry
}]

(* {{a, b, proof}, ...} for the hypotheses that are inequalities a <= b of natural numbers, an equation
   giving two *)
inequalityHypotheses[environment_, context_] := Catenate @ KeyValueMap[
	Function[{id, entry}, Replace[weakHeadNormalForm[environment, context, entry["Type"]], {
		application[application[constantReference[HoldComplete[LessEqual], _], a_], b_] :>
			{{arithmeticReduced[environment, context, a], arithmeticReduced[environment, context, b], freeVariable[id]}},
		application[application[application[constantReference[HoldComplete[Equal], _], type_], a_], b_] /; naturalNumberTypeQ[environment, context, type] :>
			ringEquationInequalities[arithmeticReduced[environment, context, a], arithmeticReduced[environment, context, b], freeVariable[id]],
		_ :> {}
	}]],
	context
]

(* "FindEquationalProof": an equation from the hypotheses that are equations of its type for all values
   of their variables, by replaying a proof that Wolfram's FindEquationalProof finds (Equational.wl) *)
findEquationalProof[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	Replace[weakHeadNormalForm[environment, current["Context"], current["Type"]], {
		application[application[application[constantReference[HoldComplete[Equal], _], _], side_], side_] :> reflexivity[data, goal],
		application[application[application[constantReference[HoldComplete[Equal], _], type_], left_], right_] :> With[
			{hypotheses = equationalHypotheses[environment, current["Context"], type]},
			If[ hypotheses === {},
				tacticFailure["NoEquationalHypotheses", "No hypothesis of the goal `1` is an equation of its type for all values of its variables.", data, goal]
			];
			Replace[equationalProof[environment, current["Context"], {type, left, right}, hypotheses], {
				reason_String :> tacticFailure["NoEquationalProof", "Wolfram's FindEquationalProof gives no proof of the goal `1` to replay: `2`.", data, goal, {reason}],
				proof_ :> solvedByCheckedProof[data, goal, current, proof]
			}]
		],
		_ :> tacticFailure["EquationExpected", "The goal `1` is not an equation.", data, goal]
	}]
]

(* {{id, binderCount}, ...}: the hypotheses that are equations of the type for all values of their
   variables, all of the type, compared outside the kernel's check, so the type queries check *)
equationalHypotheses[environment_, context_, type_] := KeyValueMap[
	Function[{id, entry}, Replace[universalEquationBinders[environment, context, entry["Type"], type, 0], {count_Integer :> {id, count}, None :> Nothing}]],
	context
]

universalEquationBinders[environment_, context_, statement_, type_, count_Integer] := Replace[statement, {
	dependentFunctionType[name_, domain_, codomain_, binder_] /; definitionallyEqualQ[environment, context, domain, type] :> With[{id = freshFreeVariable[]},
		universalEquationBinders[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[codomain, freeVariable[id]], type, count + 1]
	],
	application[application[application[constantReference[HoldComplete[Equal], _], equalityType_], _], _] /; definitionallyEqualQ[environment, context, equalityType, type] :> count,
	_ :> None
}]

(* {{a, b, proof}, ...} for the hypotheses that are equations a == b of natural numbers *)
integerEquationHypotheses[environment_, context_] := KeyValueMap[
	Function[{id, entry}, Replace[weakHeadNormalForm[environment, context, entry["Type"]], {
		application[application[application[constantReference[HoldComplete[Equal], _], type_], a_], b_] /; integerTypeQ[environment, type] :>
			{integerArithmeticReduced[environment, context, a], integerArithmeticReduced[environment, context, b], freeVariable[id]},
		_ :> Nothing
	}]],
	context
]

equationHypotheses[environment_, context_] := KeyValueMap[
	Function[{id, entry}, Replace[weakHeadNormalForm[environment, context, entry["Type"]], {
		application[application[application[constantReference[HoldComplete[Equal], _], type_], a_], b_] /; naturalNumberTypeQ[environment, context, type] :>
			{arithmeticReduced[environment, context, a], arithmeticReduced[environment, context, b], freeVariable[id]},
		_ :> Nothing
	}]],
	context
]

(* the instance proved by "Decide" where it decides it, or left as the goal; an instance decided false
   means Wolfram's answer was wrong *)
decidedInstance[state_, goal_] := Replace[catchKernelFailure[decide[state, goal]], {
	Failure["DecidedFalse", _] :> tacticFailure["InstanceRejected", "The witnesses Wolfram found do not prove the goal `1`.", state, goal],
	_Failure :> state,
	decided_ :> decided
}]

(* a rewritten goal a == a is closed by reflexivity *)
closeIfSidesSame[data_, goal_, type_] := If[
	MatchQ[type, application[application[application[constantReference[equality_, _], _], side_], side_] /; equalityTypeQ[data["Environment"], equality]],
	reflexivity[data, goal],
	data
]


(* ::Subsection:: *)
(*Sums of squares*)


(* "SumOfSquares": an inequality x <= y of integers whose difference y - x, times a positive integer d, is
   a sum c1 g1^2 + ... of squares of polynomials, which Wolfram finds (SumsOfSquares.wl).
   IntegerLessEqualOfMultiple takes the equation d (y - x) == c1 g1 g1 + ..., which "Ring" proves, and the
   proof that the sum is at least 0, made of IntegerSquareNonnegative, IntegerNonnegativeScaling and
   IntegerNonnegativeAddition. The atoms of the polynomials are the subterms that are no sum, difference,
   product, negation or power by a literal of integers, nor the integer of a sum, product, power by a
   literal or literal of natural numbers. An inequality of natural numbers is that of their integers, by
   IntegerOfNaturalLessEqual, and a goal x >= y, x < y or x > y is the inequality it unfolds to. *)
sumOfSquares[data_, goal_] := With[{current = currentGoal[data, goal], environment = data["Environment"]},
	If[ ! AllTrue[Join[$ringConstants, $sumOfSquaresConstants], Function[name, constantDeclaredQ[environment, name]]],
		tacticFailure["SumOfSquaresUnavailable", "The environment of the goal `1` lacks the integers of TypeTheoryEnvironment[\"Integers\"] and their order.", data, goal]
	];
	Replace[inequalitySides[environment, current["Context"], current["Type"]], {
		{"Integers", smaller_, larger_} :> integerSumOfSquares[data, goal, data, goal, smaller, larger],
		{"NaturalNumbers", smaller_, larger_} :> With[{integerGoal = freshMetavariableId[]},
			{
				state = solveGoal[
					data,
					goal,
					makeApplication[constantReference[HoldComplete[IntegerOfNaturalLessEqual], {}], {smaller, larger, metavariable[integerGoal]}],
					{integerGoal -> <|"Context" -> current["Context"], "Type" -> integerLessEqual[integerOfNatural[smaller], integerOfNatural[larger]], "Case" -> None|>}
				]
			},
			integerSumOfSquares[state, integerGoal, data, goal, integerOfNatural[smaller], integerOfNatural[larger]]
		],
		None :> tacticFailure["InequalityExpected", "The goal `1` is not an inequality of integers or of natural numbers.", data, goal]
	}]
]

$sumOfSquaresConstants = HoldComplete /@ Unevaluated[{
	Integers, QuotientSoundness, "integerLessEqual", "integerOfNatural", "integerAddition", "integerSubtraction", "integerMultiplication", "integerNegation",
	IntegerLessEqualOfMultiple, IntegerNonnegativeAddition, IntegerNonnegativeScaling, IntegerSquareNonnegative, IntegerLessEqualReflexivity, IntegerOfNaturalLessEqual
}]

(* {"Integers" | "NaturalNumbers", x, y} for a goal that is x <= y of integers or of natural numbers, or
   that unfolds to it, as x >= y, x < y and x > y do; or None *)
inequalitySides[environment_, context_, type_] := Replace[reducedHeadWithoutUnfolding[environment, context, type], {
	application[application[constantReference[HoldComplete["integerLessEqual"], _], smaller_], larger_] :> {"Integers", smaller, larger},
	application[application[constantReference[HoldComplete[LessEqual], _], smaller_], larger_] :> {"NaturalNumbers", smaller, larger},
	reduced_ :> Replace[headUnfolded[environment, reduced], unfolded : Except[None] :> inequalitySides[environment, context, unfolded]]
}]

(* the definition at the head of term unfolded, or None if its head is no definition *)
headUnfolded[environment_, term_] := Replace[applicationSpine[term], {
	{constantReference[name_, levels_], arguments_List} /; constantRecord[environment, name]["Kind"] === "Definition" :> With[{record = constantRecord[environment, name]},
		makeApplication[instantiateUniverseParameters[record["Value"], record["UniverseParameters"], levels], arguments]
	],
	_ :> None
}]

(* The goal target of state, smaller <= larger of integers, solved by a sum of squares; a failure shows
   the goal goal of data, the one the tactic was given. Each atom of the sides is a Wolfram variable. *)
integerSumOfSquares[state_, target_, data_, goal_, smaller_, larger_] := With[{polynomials = integerPolynomial /@ {smaller, larger}},
	{atoms = DeleteDuplicates[Cases[polynomials, integerAtom[atom_] :> atom, {0, Infinity}]]},
	{variables = Table[Subscript[\[FormalX], k], {k, Length[atoms]}]},
	Replace[
		sumOfSquaresCertificate[ReplaceAll[Last[polynomials] - First[polynomials], Thread[(integerAtom /@ atoms) -> variables]], variables],
		{
			None :> tacticFailure["NoSumOfSquares", "Wolfram finds no sum of squares of polynomials that is a positive multiple of the larger side less the smaller in the goal `1`.", data, goal],
			{scale_Integer, squares_List} :> certifiedInequality[
				state,
				target,
				data,
				goal,
				{smaller, larger, scale - 1},
				Function[square, {First[square], integerTermOfPolynomial[Last[square], variables, atoms]}] /@ squares
			]
		}
	]
]

(* The goal solved by IntegerLessEqualOfMultiple applied to d and to the sum s of the squares, its
   equation a new goal that "Ring" proves, and the proof that s is at least 0 checked by the kernel first.
   The premises are read off the lemma's type. *)
certifiedInequality[state_, target_, data_, goal_, {smaller_, larger_, d_Integer}, squares_List] := With[
	{
		environment = state["Environment"],
		context = currentGoal[state, target]["Context"],
		equationGoal = freshMetavariableId[],
		sum = nonnegativeSum[squares]
	},
	{lemma = makeApplication[constantReference[HoldComplete[IntegerLessEqualOfMultiple], {}], {naturalLiteral[d], smaller, larger, First[sum]}]},
	Replace[
		catchKernelFailure @ Replace[lemmaPremises[environment, context, lemma, metavariable[equationGoal]], {equation_, nonnegativity_} :> (
			withKernelCaches[checkHasType[environment, context, Last[sum], nonnegativity]];
			solveGoal[state, target, makeApplication[lemma, {metavariable[equationGoal], Last[sum]}], {equationGoal -> <|"Context" -> context, "Type" -> equation, "Case" -> None|>}]
		)],
		{
			_Failure :> tacticFailure["ProofRejected", "The kernel rejects the proof built for the goal `1`.", data, goal],
			solved_ :> Replace[catchKernelFailure[ring[solved, equationGoal]], _Failure :> tacticFailure[
				"NotRingEquation",
				"\"Ring\" does not prove the equation of the sum of squares that Wolfram finds for the goal `1`, as when an atom of its sides is not a variable.",
				data,
				goal
			]]
		}
	]
]

(* {A, B} for a lemma whose type is A -> B -> C, the premise A taken to be proved by proof *)
lemmaPremises[environment_, context_, lemma_, proof_] := Replace[weakHeadNormalForm[environment, context, inferType[environment, context, lemma]], {
	dependentFunctionType[_, first_, rest_, _] :> Replace[weakHeadNormalForm[environment, context, instantiateBoundVariable[rest, proof]], {
		dependentFunctionType[_, second_, _, _] :> {first, second},
		_ :> kernelFailure["PremiseExpected", "The lemma has fewer premises than expected.", {}]
	}],
	_ :> kernelFailure["PremiseExpected", "The lemma has fewer premises than expected.", {}]
}]

(* {s, proof of 0 <= s} for s the sum of the c g g, right nested; 0 for no squares *)
nonnegativeSum[{}] := {integerLiteral[0], makeApplication[constantReference[HoldComplete[IntegerLessEqualReflexivity], {}], {integerLiteral[0]}]}
nonnegativeSum[{square_}] := nonnegativeSquare @@ square
nonnegativeSum[{square_, rest__}] := With[{first = nonnegativeSquare @@ square, others = nonnegativeSum[{rest}]},
	{
		integerAddition[First[first], First[others]],
		makeApplication[constantReference[HoldComplete[IntegerNonnegativeAddition], {}], {First[first], First[others], Last[first], Last[others]}]
	}
]

(* {c g g, proof of 0 <= c g g}, a coefficient 1 left out *)
nonnegativeSquare[1, term_] := {integerMultiplication[term, term], makeApplication[constantReference[HoldComplete[IntegerSquareNonnegative], {}], {term}]}
nonnegativeSquare[coefficient_Integer, term_] := With[{square = nonnegativeSquare[1, term]},
	{
		integerMultiplication[integerLiteral[coefficient], First[square]],
		makeApplication[constantReference[HoldComplete[IntegerNonnegativeScaling], {}], {naturalLiteral[coefficient], First[square], Last[square]}]
	}
]

(* the term of integers as a Wolfram polynomial, each atom integerAtom[atom] *)
integerPolynomial[term_] := Replace[term, {
	application[application[constantReference[HoldComplete["integerAddition"], _], a_], b_] :> integerPolynomial[a] + integerPolynomial[b],
	application[application[constantReference[HoldComplete["integerSubtraction"], _], a_], b_] :> integerPolynomial[a] - integerPolynomial[b],
	application[application[constantReference[HoldComplete["integerMultiplication"], _], a_], b_] :> integerPolynomial[a] * integerPolynomial[b],
	application[constantReference[HoldComplete["integerNegation"], _], a_] :> -integerPolynomial[a],
	application[application[constantReference[HoldComplete["integerPower"], _], a_], naturalLiteral[k_Integer]] :> integerPolynomial[a] ^ k,
	application[constantReference[HoldComplete["integerOfNatural"], _], n_] :> naturalPolynomial[n],
	_ :> integerAtom[term]
}]

(* the integer of a term of natural numbers as a Wolfram polynomial: its sums, products, powers by
   literals and literals carry over, and the integer of any other subterm is an atom *)
naturalPolynomial[term_] := Replace[term, {
	naturalLiteral[n_Integer] :> n,
	constantReference[HoldComplete[NaturalNumberZero], _] :> 0,
	application[constantReference[HoldComplete[NaturalNumberSuccessor], _], a_] :> naturalPolynomial[a] + 1,
	application[application[constantReference[HoldComplete[Plus], _], a_], b_] :> naturalPolynomial[a] + naturalPolynomial[b],
	application[application[constantReference[HoldComplete[Times], _], a_], b_] :> naturalPolynomial[a] * naturalPolynomial[b],
	application[application[constantReference[HoldComplete[Power], _], a_], naturalLiteral[k_Integer]] :> naturalPolynomial[a] ^ k,
	_ :> integerAtom[integerOfNatural[term]]
}]

(* the polynomial, with integer coefficients, as a term of integers, each variable standing for its atom *)
integerTermOfPolynomial[polynomial_, variables_List, atoms_List] := Replace[
	Function[rule, integerMonomialTerm[Last[rule], Catenate[MapThread[ConstantArray, {atoms, First[rule]}]]]] /@ CoefficientRules[polynomial, variables],
	{
		{} :> integerLiteral[0],
		monomials_List :> Fold[integerAddition, monomials]
	}
]

(* the coefficient times the product of the factors, a coefficient 1 left out and a negative one negated *)
integerMonomialTerm[coefficient_Integer?Negative, factors_List] := integerNegation[integerMonomialTerm[-coefficient, factors]]
integerMonomialTerm[coefficient_Integer, {}] := integerLiteral[coefficient]
integerMonomialTerm[1, factors_List] := Fold[integerMultiplication, factors]
integerMonomialTerm[coefficient_Integer, factors_List] := integerMultiplication[integerLiteral[coefficient], Fold[integerMultiplication, factors]]

integerLiteral[n_Integer] := integerOfNatural[naturalLiteral[n]]
integerOfNatural[term_] := application[constantReference[HoldComplete["integerOfNatural"], {}], term]
integerNegation[term_] := application[constantReference[HoldComplete["integerNegation"], {}], term]
integerAddition[a_, b_] := makeApplication[constantReference[HoldComplete["integerAddition"], {}], {a, b}]
integerMultiplication[a_, b_] := makeApplication[constantReference[HoldComplete["integerMultiplication"], {}], {a, b}]
integerLessEqual[a_, b_] := makeApplication[constantReference[HoldComplete["integerLessEqual"], {}], {a, b}]


(* ::Subsection:: *)
(*Induction*)


(* The recursor of the variable's type, applied to its parameters, the goal as a function of the
   variable's indices and the variable (the motive), one new goal per constructor (the minor premises),
   the indices and the variable itself. The indices must be distinct variables. The hypotheses that
   depend on the variable or its indices are reverted into the motive, so each new goal, the goal for
   that constructor, states them again, and so does each induction hypothesis: the recursor's result is
   applied to them. "Induction" gives each new goal the minor premise's type, the constructor's fields
   and an induction hypothesis per recursive field; "Cases" gives it the fields alone. *)
(* a variable of a quotient type is eliminated by the quotient's induction, any other by its inductive
   type's recursor *)
eliminate[data_, goal_, variableName_HoldComplete, mode : "Induction" | "Cases"] := With[
	{current = currentGoal[data, goal], environment = data["Environment"]},
	{id = hypothesisId[data, goal, current["Context"], variableName]},
	{spine = applicationSpine[weakHeadNormalForm[environment, current["Context"], current["Context"][id]["Type"]]]},
	If[ quotientTypeQ[environment, First[spine]],
		quotientElimination[data, goal, current, id, spine, variableName],
		inductiveElimination[data, goal, variableName, mode]
	]
]

quotientTypeQ[environment_, head_] := MatchQ[head, constantReference[name_, _] /; MatchQ[constantRecord[environment, name], KeyValuePattern[{"Kind" -> "Quotient", "QuotientRole" -> "Type"}]]]

(* A class q of the quotient of α by r: the goal, with the hypotheses that mention q, is a proposition P[q],
   and the quotient's induction proves it from the one goal ForAll[{Typed[a, α]}, P[class of a]], as
   Lean's induction using Quot.ind. Into data, a quotient is eliminated by lifting a function instead. *)
quotientElimination[data_, goal_, current_, id_, {head : constantReference[name_, levels_], {alpha_, relation_}}, variableName_] := With[
	{
		environment = data["Environment"],
		context = current["Context"],
		induction = Last[constantRecord[data["Environment"], name]["QuotientNames"]],
		dependents = dependentHypotheses[current["Context"], {id}],
		newGoal = freshMetavariableId[]
	},
	{goalBody = makeDependentFunctionType[context, dependents, current["Type"]]},
	{motive = makeLambda[context, {id}, goalBody]},
	{premiseType = Replace[
		instantiateUniverseParameters[constantRecord[environment, induction]["Type"], constantRecord[environment, induction]["UniverseParameters"], levels],
		dependentFunctionType[_, _, dependentFunctionType[_, _, dependentFunctionType[_, _, dependentFunctionType[_, premise_, _, _], _], _], _] :>
			betaNormalize[instantiateBoundVariables[premise, {alpha, relation, motive}]]
	]},
	If[ ! levelEquivalentQ[sortLevel[environment, context, goalBody], 0],
		tacticFailure["QuotientEliminationIntoData", "In the goal `1`, the class `2` can only be eliminated into a proposition; lift a function to the classes instead.", data, goal, {HoldForm @@ variableName}]
	];
	solveGoal[
		data,
		goal,
		makeApplication[constantReference[induction, levels], Join[{alpha, relation, motive, metavariable[newGoal], freeVariable[id]}, freeVariable /@ dependents]],
		{newGoal -> <|"Context" -> KeyDrop[context, Join[{id}, dependents]], "Type" -> premiseType, "Case" -> HoldComplete[QuotientIntroduction]|>}
	]
]

inductiveElimination[data_, goal_, variableName_HoldComplete, mode : "Induction" | "Cases"] := Module[
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
	recursorLevels = If[TrueQ[recursorRecord["EliminationUniverse"]], Prepend[Last[head], motiveUniverse[data, goal, eliminationLevel]], Last[head]];
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
