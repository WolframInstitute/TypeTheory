(* ::Package:: *)

(*
Elaboration: from a surface syntax tree to a core term, filling in what the surface leaves out.

A surface term omits implicit arguments (Equal[a, b] stands for Equal[A, a, b]) and universe levels.
Elaboration inserts a metavariable for each, solves them by first-order unification of types, and
fails if any remain. It is not trusted: every term it produces is checked again by the kernel, with no
metavariables in sight, before it is used. A mistake here can make elaboration fail, never let an
ill-typed term through.

State, bound with Block for one elaboration (see withElaborationState):

	$metavariableTypes, $metavariableAssignments    metavariable types and solutions (TypeChecking.wl)
	$levelAssignments                               universe level metavariable solutions
	$elaborationEnvironment                         the environment
	$elaborationContext                             the local context
	$elaborationScope                               <|HoldComplete[symbol] -> {term, type}, ...|>: what each name stands for
	$universeParameterNames                         {HoldComplete[u], ...}: the universe parameters a term may mention

A binder's variable stands for a fresh free variable; With[{x = v}, b] makes x stand for v itself. A
symbol whose value is a TypeTheoryTerm stands for that term, and one whose value is a finished
TypeTheoryProof stands for its proof, so terms and proofs can be built up in a notebook.

While a tactic elaborates a term for a goal, $goalMetavariableTypes gives the types of the proof's open
goals, which may occur in the goal's type.

True, False, Not, And and Or are overloaded: they stand for the propositions or, in an environment that
declares them, for the Booleans BooleanTrue, BooleanFalse, BooleanNot, BooleanAnd and BooleanOr. The
type decides: where a type or Prop is expected they are the propositions, where Booleans is expected
the Booleans; elsewhere each meaning is tried, and the one that fits is taken. A name both meanings fit
waits, in $pendingOverloads, until its type is known. A name still undecided when the binders around
it close, or when the term is finished, is ambiguous, and Typed must say which it is.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[withElaborationState]
PackageScoped[elaborateSyntax]
PackageScoped[elaborateClosedTerm]
PackageScoped[elaborateClosedType]
PackageScoped[elaborateInContext]
PackageScoped[finishElaboration]
PackageScoped[unify]
PackageScoped[unifyOrFail]
PackageScoped[instantiateMetavariables]
PackageScoped[newMetavariable]
PackageScoped[unsolvedMetavariables]
PackageScoped[freshMetavariableId]
PackageScoped[attemptOrRestore]
PackageScoped[$goalMetavariableTypes]
PackageScoped[$levelAssignments]
PackageScoped[$elaborationEnvironment]
PackageScoped[$elaborationContext]
PackageScoped[$elaborationScope]
PackageScoped[$universeParameterNames]
PackageScoped[overloadedNameQ]
PackageScoped[settleOverloads]


(* ::Section:: *)
(*Usage Messages*)


withElaborationState::usage = "withElaborationState[{environment, context, scope, universeParameters}, body] evaluates body with fresh elaboration state."
elaborateSyntax::usage = "elaborateSyntax[syntax, expected] gives {term, type} for a syntax tree, with expected the expected type or None; metavariables may remain."
elaborateClosedTerm::usage = "elaborateClosedTerm[environment, HoldComplete[term], expected, universeParameters] gives {coreTerm, coreType} for a \
closed surface term, checked by the kernel; expected is a core type or None."
elaborateClosedType::usage = "elaborateClosedType[environment, HoldComplete[type], universeParameters] gives the core term of a closed surface type, checked to be a type."
elaborateInContext::usage = "elaborateInContext[environment, context, scope, HoldComplete[term], expected] gives {coreTerm, coreType} for a surface term in a local context, checked by the kernel."
finishElaboration::usage = "finishElaboration[environment, context, {term, type}, expected] solves the remaining metavariables away, fails if any remain, and checks the term with the kernel."
unify::usage = "unify[a, b] gives True if it can solve metavariables so that a and b are definitionally equal, recording the solutions."
unifyOrFail::usage = "unifyOrFail[actual, expected, syntax] unifies actual with expected, or throws a type mismatch failure for syntax."
instantiateMetavariables::usage = "instantiateMetavariables[term] replaces every solved metavariable in term by its solution."
newMetavariable::usage = "newMetavariable[type] gives a fresh metavariable of the given type."
unsolvedMetavariables::usage = "unsolvedMetavariables[term] gives the metavariables and universe level metavariables left in term."
freshMetavariableId::usage = "freshMetavariableId[] gives an identifier no metavariable has used."
attemptOrRestore::usage = "attemptOrRestore[attempt] evaluates attempt and gives True if it gives True; otherwise it undoes the solutions attempt recorded and gives False."
$goalMetavariableTypes::usage = "$goalMetavariableTypes is the Association from the open goals of a proof to their types while a tactic elaborates a term."
$levelAssignments::usage = "$levelAssignments is the Association of solved universe level metavariables while elaborating."
$elaborationEnvironment::usage = "$elaborationEnvironment is the environment while elaborating."
$elaborationContext::usage = "$elaborationContext is the local context while elaborating."
$elaborationScope::usage = "$elaborationScope gives the term and type each variable name stands for while elaborating."
$universeParameterNames::usage = "$universeParameterNames is the list of universe parameters a term may mention while elaborating."
overloadedNameQ::usage = "overloadedNameQ[environment, HoldComplete[name]] gives True if name stands for more than one constant of environment, as True does for the proposition and the Boolean."
settleOverloads::usage = "settleOverloads[term] decides the overloaded names still waiting for their type, and gives term with the solutions found."


(* ::Section:: *)
(*Function Definitions*)


$metavariableCounter = 0
$levelMetavariableCounter = 0
$levelAssignments = <||>
$elaborationEnvironment = None
$elaborationContext = <||>
$elaborationScope = <||>
$universeParameterNames = {}
$goalMetavariableTypes = <||>
$pendingOverloads = {}


SetAttributes[withElaborationState, HoldRest]
withElaborationState[{environment_, context_, scope_, universeParameters_}, body_] := Block[
	{
		$metavariableTypes = $goalMetavariableTypes,
		$metavariableAssignments = <||>,
		$levelAssignments = <||>,
		$pendingOverloads = {},
		$elaborationEnvironment = environment,
		$elaborationContext = context,
		$elaborationScope = scope,
		$universeParameterNames = universeParameters
	},
	body
]


elaborateClosedTerm[environment_, held_HoldComplete, expected_, universeParameters_List] := elaborateInContext[environment, <||>, <||>, held, expected, universeParameters]

(* a type is expected, which makes True, And and the other overloaded names propositions *)
elaborateClosedType[environment_, held_HoldComplete, universeParameters_List] := With[
	{
		result = withElaborationState[
			{environment, <||>, <||>, universeParameters},
			finishElaboration[environment, <||>, elaborateSyntax[toSyntax @@ held, universeSort[newLevelMetavariable[]]], None]
		]
	},
	sortLevel[environment, <||>, First[result]];
	First[result]
]

elaborateInContext[environment_, context_, scope_, held_HoldComplete, expected_] := elaborateInContext[environment, context, scope, held, expected, {}]
elaborateInContext[environment_, context_, scope_, held_HoldComplete, expected_, universeParameters_List] := withElaborationState[
	{environment, context, scope, universeParameters},
	With[{syntax = toSyntax @@ held},
		With[{result = elaborateSyntax[syntax, expected]},
			If[expected =!= None, unifyOrFail[Last[result], expected, syntax]];
			finishElaboration[environment, context, result, expected]
		]
	]
]

finishElaboration[environment_, context_, {term_, type_}, expected_] := With[{finalTerm = settleOverloads[term]},
	If[ unsolvedMetavariables[finalTerm] =!= {},
		kernelFailure["UnsolvedImplicitArgument", "Could not infer every implicit argument and universe level of `1`.", {displayCoreTerm[environment, context, finalTerm]}]
	];
	(* the kernel checks the elaborated term on its own, with no metavariables but the open goals of a proof *)
	Block[{$metavariableTypes = $goalMetavariableTypes, $metavariableAssignments = <||>},
		If[ expected === None,
			{finalTerm, inferType[environment, context, finalTerm]},
			checkHasType[environment, context, finalTerm, expected];
			{finalTerm, expected}
		]
	]
]


(* ::Subsection:: *)
(*Syntax*)


elaborateSyntax[syntax_, expected_] := Replace[syntax, {
	syntaxApplication[syntaxSymbol[HoldComplete[Function]], {binders_, body_}] :> elaborateFunction[listElements[binders], body, expected],
	syntaxApplication[syntaxSymbol[HoldComplete[ForAll | RightTee]], {binders_, body_}] :> elaborateForAll[listElements[binders], body],
	syntaxApplication[syntaxSymbol[HoldComplete[Exists]], {binders_, body_}] :>
		elaborateSyntax[syntaxHead[Exists, {syntaxHead[Function, {binders, body}]}], expected],
	syntaxApplication[syntaxSymbol[HoldComplete[Implies]], {domain_, codomain_}] :> elaborateArrow[{domain}, codomain],
	syntaxApplication[syntaxSymbol[HoldComplete[TypeSpecifier]], {syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {domains_, codomain_}]}] :>
		elaborateArrow[listElements[domains], codomain],
	syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {domains_, codomain_}] :> elaborateArrow[listElements[domains], codomain],
	syntaxApplication[syntaxSymbol[HoldComplete[TypeUniverse]], {level_}] :> With[{elaborated = elaborateLevel[level]},
		{universeSort[elaborated], universeSort[normalizeLevel[levelSuccessor[elaborated, 1]]]}
	],
	syntaxApplication[syntaxSymbol[HoldComplete[Typed]], {term_, type_}] :> elaborateAscription[term, type],
	syntaxApplication[syntaxSymbol[HoldComplete[With]], {bindings_, body_}] :> elaborateWith[listElements[bindings], body, expected],
	syntaxApplication[syntaxSymbol[HoldComplete[head : Plus | Times]], arguments_List] /; Length[arguments] > 2 :>
		elaborateSyntax[leftFold[head, arguments], expected],
	(* a - b is read as Plus[a, Times[-1, b]], and a - 3 as Plus[a, -3]: both are Subtract *)
	syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {first_, syntaxApplication[syntaxSymbol[HoldComplete[Times]], {syntaxInteger[-1], second_}]}] :>
		elaborateSyntax[syntaxHead[Subtract, {first, second}], expected],
	syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {first_, syntaxInteger[k_Integer?Negative]}] :>
		elaborateSyntax[syntaxHead[Subtract, {first, syntaxInteger[-k]}], expected],
	syntaxApplication[syntaxSymbol[name_], arguments_List] /; ! KeyExistsQ[$elaborationScope, name] && overloadedNameQ[$elaborationEnvironment, name] :>
		elaborateOverloaded[name, arguments, syntax, expected],
	(* a && b && c is a && (b && c), as in Lean *)
	syntaxApplication[syntaxSymbol[HoldComplete[head : And | Or]], arguments_List] /; Length[arguments] > 2 :>
		elaborateSyntax[rightFold[head, arguments], expected],
	syntaxApplication[syntaxSymbol[HoldComplete[Subscript]], {constant_, levels__}] :> insertImplicitArguments[constantWithLevels[constant, {levels}]],
	syntaxApplication[syntaxSymbol[HoldComplete[Construct]], {head_, arguments___}] :> applyExplicitly[elaborateHead[head], {arguments}, head],
	syntaxApplication[syntaxSymbol[HoldComplete[Part]], {structureTerm_, syntaxInteger[index_Integer?Positive]}] :> elaborateProjection[structureTerm, index],
	syntaxSymbol[held_] /; KeyExistsQ[$elaborationScope, held] :> $elaborationScope[held],
	syntaxString[name_] /; KeyExistsQ[$elaborationScope, HoldComplete[name]] :> $elaborationScope[HoldComplete[name]],
	syntaxSymbol[name_] /; overloadedNameQ[$elaborationEnvironment, name] :> elaborateOverloaded[name, {}, syntax, expected],
	_ /; declaredConstantSyntaxQ[syntax] :> insertImplicitArguments[constantWithFreshLevels[heldFromSyntax[syntax]]],
	syntaxApplication[head_, arguments_List] :> applyArguments[elaborateHead[head], arguments, head, expected],
	syntaxInteger[n_Integer?NonNegative] :> {naturalLiteral[n], naturalNumberTypeForElaboration[syntax]},
	syntaxSymbol[HoldComplete[symbol_Symbol]] /; storedValueQ[symbol] :> elaborateStoredValue[symbol, expected],
	_ :> elaborationFailure["`1` is not a term of the type theory: it is neither a variable in scope nor a declared constant.", syntax]
}]

listElements[syntaxApplication[syntaxSymbol[HoldComplete[List]], elements_List]] := elements
listElements[single_] := {single}

rightFold[head_, arguments_List] := Fold[
	Function[{accumulated, previous}, syntaxApplication[syntaxSymbol[HoldComplete[head]], {previous, accumulated}]],
	Last[arguments],
	Reverse[Most[arguments]]
]

leftFold[head_, arguments_List] := Fold[
	Function[{accumulated, next}, syntaxApplication[syntaxSymbol[HoldComplete[head]], {accumulated, next}]],
	First[arguments],
	Rest[arguments]
]

declaredConstantSyntaxQ[syntax : (_syntaxSymbol | _syntaxString | _syntaxApplication)] := constantDeclaredQ[$elaborationEnvironment, heldFromSyntax[syntax]]
declaredConstantSyntaxQ[_] := False

SetAttributes[{storedValueQ, elaborateStoredValue}, HoldFirst]
storedValueQ[symbol_Symbol] := MatchQ[OwnValues[symbol], {Verbatim[RuleDelayed][_, _TypeTheoryTerm | TypeTheoryProof[_Association]]}]

(* a finished proof is already a core term, which finishElaboration checks again like any other *)
elaborateStoredValue[symbol_Symbol, expected_] := Replace[First[OwnValues[symbol]], {
	Verbatim[RuleDelayed][_, term_TypeTheoryTerm] :> elaborateSyntax[termSyntax[term], expected],
	Verbatim[RuleDelayed][_, proof : TypeTheoryProof[_Association]] :> {completedProofTerm[proof], proofStatement[proof]}
}]

elaborationFailure[template_String, syntax_] := kernelFailure["ElaborationFailed", template, {HoldForm @@ heldFromSyntax[syntax]}]

naturalNumberTypeForElaboration[syntax_] := Replace[naturalNumberSettings[$elaborationEnvironment], {
	settings_Association :> constantReference[settings["Type"], {}],
	_ :> elaborationFailure["The literal `1` needs an environment with natural numbers.", syntax]
}]


(* ::Subsection:: *)
(*Constants and applications*)


constantWithFreshLevels[held_HoldComplete] := With[{record = constantRecord[$elaborationEnvironment, held]},
	With[{levels = Table[newLevelMetavariable[], Length[record["UniverseParameters"]]]},
		{constantReference[held, levels], instantiateUniverseParameters[record["Type"], record["UniverseParameters"], levels]}
	]
]

constantWithLevels[constantSyntax_, levelSyntaxes_List] := With[{held = heldFromSyntax[constantSyntax]},
	If[ ! constantDeclaredQ[$elaborationEnvironment, held],
		elaborationFailure["`1` is not a declared constant.", constantSyntax]
	];
	With[{record = constantRecord[$elaborationEnvironment, held], levels = elaborateLevel /@ levelSyntaxes},
		If[ Length[levels] =!= Length[record["UniverseParameters"]],
			elaborationFailure["`1` is given the wrong number of universe levels.", constantSyntax]
		];
		{constantReference[held, levels], instantiateUniverseParameters[record["Type"], record["UniverseParameters"], levels]}
	]
]

(* a constant on its own gets its leading implicit arguments *)
insertImplicitArguments[{term_, type_}] := Replace[
	weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[type]],
	{
		dependentFunctionType[_, domain_, codomain_, binder_] /; binder =!= "Explicit" :> With[{implicit = newMetavariable[domain]},
			insertImplicitArguments[{application[term, implicit], instantiateBoundVariable[codomain, implicit]}]
		],
		_ :> {term, type}
	}
]

elaborateHead[syntax : syntaxSymbol[held_]] /; ! KeyExistsQ[$elaborationScope, held] && declaredConstantSyntaxQ[syntax] := constantWithFreshLevels[held]
elaborateHead[syntax : syntaxString[name_]] /; ! KeyExistsQ[$elaborationScope, HoldComplete[name]] && declaredConstantSyntaxQ[syntax] :=
	constantWithFreshLevels[HoldComplete[name]]
elaborateHead[syntax_syntaxApplication] /; declaredConstantSyntaxQ[syntax] := constantWithFreshLevels[heldFromSyntax[syntax]]
elaborateHead[syntaxApplication[syntaxSymbol[HoldComplete[Subscript]], {constant_, levels__}]] := constantWithLevels[constant, {levels}]
elaborateHead[syntax_] := elaborateSyntax[syntax, None]

(* Implicit binders get metavariables, and each explicit binder takes the next argument, elaborated at
   once against its binder's type. An argument whose type is still an unknown applied to arguments, as
   the proof of P[x] for an implicit predicate P, waits: the type of the whole application is unified
   with the expected type first, which is what usually determines P. *)
applyArguments[{function_, functionType_}, arguments_List, headSyntax_, expected_] :=
	finishApplication[collectArguments[function, functionType, arguments, {}, headSyntax], expected]

collectArguments[term_, type_, {}, postponed_List, _] := {term, type, postponed}
collectArguments[term_, type_, arguments_List, postponed_List, headSyntax_] := Replace[
	weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[type]],
	{
		dependentFunctionType[_, domain_, codomain_, binder_] /; binder =!= "Explicit" :> With[{implicit = newMetavariable[domain]},
			collectArguments[application[term, implicit], instantiateBoundVariable[codomain, implicit], arguments, postponed, headSyntax]
		],
		dependentFunctionType[_, domain_, codomain_, _] /; flexibleTypeQ[domain] :> With[{placeholder = newMetavariable[domain]},
			collectArguments[
				application[term, placeholder],
				instantiateBoundVariable[codomain, placeholder],
				Rest[arguments],
				Append[postponed, {placeholder, First[arguments]}],
				headSyntax
			]
		],
		dependentFunctionType[_, domain_, codomain_, _] :> With[{argument = checkAgainst[First[arguments], domain]},
			collectArguments[application[term, argument], instantiateBoundVariable[codomain, argument], Rest[arguments], postponed, headSyntax]
		],
		_ :> elaborationFailure["`1` is applied to more arguments than its type takes.", headSyntax]
	}
]

finishApplication[{term_, type_, {}}, _] := {term, type}
finishApplication[{term_, type_, postponed_List}, expected_] := (
	If[expected =!= None, attemptOrRestore[unify[type, expected]]];
	Scan[
		Function[pending, With[{placeholder = First[pending], syntax = Last[pending]},
			If[ ! unify[placeholder, checkAgainst[syntax, instantiateMetavariables[$metavariableTypes[First[placeholder]]]]],
				elaborationFailure["`1` is not the argument the expected type of the application requires.", syntax]
			]
		]],
		postponed
	];
	{term, type}
)

(* an unsolved metavariable applied to arguments *)
flexibleTypeQ[type_] := With[{spine = applicationSpine[instantiateMetavariables[type]]},
	unassignedMetavariableQ[First[spine]] && Last[spine] =!= {}
]

checkAgainst[syntax_, expected_] := With[{result = elaborateSyntax[syntax, expected]},
	unifyOrFail[Last[result], expected, syntax];
	First[result]
]

(* Construct[f, a, ...]: each argument fills the next binder, implicit or not, and nothing is filled in *)
applyExplicitly[{function_, functionType_}, {}, _] := {function, functionType}
applyExplicitly[{function_, functionType_}, {argument_, rest___}, headSyntax_] := Replace[
	weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[functionType]],
	{
		dependentFunctionType[_, domain_, codomain_, _] :> With[{value = checkAgainst[argument, domain]},
			applyExplicitly[{application[function, value], instantiateBoundVariable[codomain, value]}, {rest}, headSyntax]
		],
		_ :> elaborationFailure["`1` is applied to more arguments than its type takes.", headSyntax]
	}
]

(* t[[i]]: the field i of t, whose type must be a structure *)
elaborateProjection[structureSyntax_, index_Integer] := With[{elaborated = elaborateSyntax[structureSyntax, None]},
	With[
		{
			structure = Replace[
				First @ applicationSpine[weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[Last[elaborated]]]],
				{
					constantReference[name_, _] /; structureLikeQ[$elaborationEnvironment, name] :> name,
					_ :> elaborationFailure["The type of `1` is not a structure, so it has no fields.", structureSyntax]
				}
			]
		},
		(* the solutions found so far go in first: the kernel infers the projection's type, and would see a
		   solved universe level metavariable as an unknown *)
		{projected = projection[structure, index - 1, instantiateMetavariables[First[elaborated]]]},
		{projected, inferType[$elaborationEnvironment, $elaborationContext, projected]}
	]
]


(* ::Subsection:: *)
(*Binders*)


(* Opens binders one by one, each type elaborated in the context the earlier binders made. A bare
   symbol takes its type from the expected function type. *)
openBinders[binders_List, expected_] := Fold[openBinder, <|"Context" -> $elaborationContext, "Scope" -> $elaborationScope, "Ids" -> {}, "Expected" -> expected|>, binders]

openBinder[state_Association, binder_] := Block[{$elaborationContext = state["Context"], $elaborationScope = state["Scope"]},
	With[{parsed = parseBinder[binder]},
		With[
			{
				id = freshFreeVariable[],
				(* with the solutions found while elaborating it: the kernel, inferring types in this context,
				   would not see that a universe level metavariable in it is solved *)
				type = instantiateMetavariables[Replace[parsed["Type"], {None :> expectedDomain[state["Expected"], binder], typeSyntax_ :> elaborateTypeSyntax[typeSyntax]}]]
			},
			<|
				"Context" -> extendContext[state["Context"], id, parsed["Name"], type, parsed["Binder"]],
				"Scope" -> Append[state["Scope"], parsed["Name"] -> {freeVariable[id], type}],
				"Ids" -> Append[state["Ids"], id],
				"Expected" -> expectedBody[state["Expected"], id]
			|>
		]
	]
]

parseBinder[syntaxApplication[syntaxSymbol[HoldComplete[Typed]], {syntaxSymbol[name_], type_}]] := <|"Name" -> name, "Type" -> type, "Binder" -> "Explicit"|>
parseBinder[syntaxApplication[syntaxSymbol[HoldComplete[Typed]], {syntaxString[name_], type_}]] := <|"Name" -> HoldComplete[name], "Type" -> type, "Binder" -> "Explicit"|>
parseBinder[syntaxApplication[syntaxSymbol[HoldComplete[Annotation]], {binder_, syntaxString[kind : "Implicit" | "StrictImplicit" | "InstanceImplicit"]}]] :=
	Append[parseBinder[binder], "Binder" -> kind]
parseBinder[syntaxSymbol[name_]] := <|"Name" -> name, "Type" -> None, "Binder" -> "Explicit"|>
parseBinder[syntaxString[name_]] := <|"Name" -> HoldComplete[name], "Type" -> None, "Binder" -> "Explicit"|>
parseBinder[other_] := elaborationFailure["`1` is not a binder: write Typed[x, type] or Annotation[Typed[x, type], \"Implicit\"].", other]

expectedDomain[expected_, binder_] := Replace[
	If[expected === None, None, weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[expected]]],
	{
		dependentFunctionType[_, domain_, _, _] :> domain,
		_ :> elaborationFailure["The type of the variable `1` is needed: write Typed[x, type].", binder]
	}
]

expectedBody[None, _] := None
expectedBody[expected_, id_] := Replace[
	weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[expected]],
	{dependentFunctionType[_, _, codomain_, _] :> instantiateBoundVariable[codomain, freeVariable[id]], _ :> None}
]

(* The body's type is unified with its expected type inside the binders, before the function is closed:
   an implicit argument of the body solved by the expected type is then solved in terms of the bound
   variables, and abstracted with them, instead of naming a variable outside its binder. *)
elaborateFunction[binders_List, body_, expected_] := With[{start = Length[$pendingOverloads], opened = openBinders[binders, expected]},
	Block[{$elaborationContext = opened["Context"], $elaborationScope = opened["Scope"]},
		With[{result = elaborateSyntax[body, opened["Expected"]]},
			If[opened["Expected"] =!= None, attemptOrRestore[unify[Last[result], opened["Expected"]]]];
			(* an overloaded name inside may mention the bound variables, so it is decided before they go out of scope *)
			resolvePendingOverloads[start, True];
			{
				makeLambda[instantiateContext[$elaborationContext], opened["Ids"], instantiateMetavariables[First[result]]],
				makeDependentFunctionType[instantiateContext[$elaborationContext], opened["Ids"], instantiateMetavariables[Last[result]]]
			}
		]
	]
]

elaborateForAll[binders_List, body_] := With[{start = Length[$pendingOverloads], opened = openBinders[binders, None], outerContext = $elaborationContext},
	With[
		{
			term = Block[{$elaborationContext = opened["Context"], $elaborationScope = opened["Scope"]},
				With[{bodyType = elaborateTypeSyntax[body]},
					resolvePendingOverloads[start, True];
					makeDependentFunctionType[instantiateContext[$elaborationContext], opened["Ids"], instantiateMetavariables[bodyType]]
				]
			]
		},
		{term, inferType[$elaborationEnvironment, outerContext, term]}
	]
]

(* A -> B: the result does not depend on the argument, so B is elaborated outside the binder *)
elaborateArrow[domains_List, codomain_] := With[
	{term = Fold[
		Function[{accumulated, domain}, dependentFunctionType[HoldComplete[\[FormalX]], domain, accumulated, "Explicit"]],
		elaborateTypeSyntax[codomain],
		Reverse[elaborateTypeSyntax /@ domains]
	]},
	{term, inferType[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[term]]}
]

elaborateTypeSyntax[syntax_] := With[{result = elaborateSyntax[syntax, universeSort[newLevelMetavariable[]]]},
	Replace[weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[Last[result]]], {
		_universeSort :> First[result],
		_metavariable :> (unify[Last[result], universeSort[newLevelMetavariable[]]]; First[result]),
		_ :> elaborationFailure["`1` is not a type.", syntax]
	}]
]

elaborateAscription[term_, type_] := With[{elaboratedType = elaborateTypeSyntax[type]},
	{checkAgainst[term, elaboratedType], elaboratedType}
]

elaborateWith[{}, body_, expected_] := elaborateSyntax[body, expected]
elaborateWith[{syntaxApplication[syntaxSymbol[HoldComplete[Set]], {syntaxString[name_], value_}], rest___}, body_, expected_] :=
	elaborateWith[{syntaxApplication[syntaxSymbol[HoldComplete[Set]], {syntaxSymbol[HoldComplete[name]], value}], rest}, body, expected]
elaborateWith[{syntaxApplication[syntaxSymbol[HoldComplete[Set]], {syntaxSymbol[name_], value_}], rest___}, body_, expected_] :=
	With[{definition = elaborateSyntax[value, None]},
		Block[{$elaborationScope = Append[$elaborationScope, name -> definition]},
			elaborateWith[{rest}, body, expected]
		]
	]
elaborateWith[{other_, ___}, _, _] := elaborationFailure["`1` is not a binding: write With[{x = value}, body].", other]


(* ::Subsection:: *)
(*Overloaded names*)


(* each overloaded name, with the proposition it stands for first and the Boolean second *)
$overloadedNames = <|
	HoldComplete[True] -> {HoldComplete[True], HoldComplete[BooleanTrue]},
	HoldComplete[False] -> {HoldComplete[False], HoldComplete[BooleanFalse]},
	HoldComplete[Not] -> {HoldComplete[Not], HoldComplete[BooleanNot]},
	HoldComplete[And] -> {HoldComplete[And], HoldComplete[BooleanAnd]},
	HoldComplete[Or] -> {HoldComplete[Or], HoldComplete[BooleanOr]}
|>

overloadedNameQ[environment_, name_HoldComplete] := Length[declaredMeanings[environment, name]] > 1

declaredMeanings[environment_, name_HoldComplete] := Select[Lookup[$overloadedNames, name, {}], Function[meaning, constantDeclaredQ[environment, meaning]]]

elaborateOverloaded[name_HoldComplete, arguments_List, syntax_, expected_] := Replace[
	chosenMeaning[declaredMeanings[$elaborationEnvironment, name], arguments, expected],
	{
		meaning_HoldComplete :> elaborateMeaning[meaning, arguments, expected],
		None :> postponeOverload[name, arguments, syntax, expected]
	}
]

(* the meaning the expected type allows, or the one meaning that fits, or None if both fit; if neither
   fits, the proposition, whose elaboration then says why *)
chosenMeaning[{proposition_, boolean_}, arguments_List, expected_] := Replace[
	expectedMeaning[{proposition, boolean}, arguments, expected],
	None :> With[{fitting = Select[{proposition, boolean}, Function[meaning, meaningFitsQ[meaning, arguments, expected]]]},
		Replace[fitting, {{only_} :> only, {} :> proposition, _ :> None}]
	]
]
chosenMeaning[{only_}, _, _] := only

(* a type or Prop is expected only of the proposition, and Booleans only of the Boolean; a connective
   with no arguments is a function, which the expected type does not decide this way *)
expectedMeaning[{proposition_, boolean_}, arguments_List, expected_] /; expected =!= None && (arguments =!= {} || MatchQ[proposition, HoldComplete[True | False]]) :=
	Replace[weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[expected]], {
		_universeSort :> proposition,
		constantReference[HoldComplete[Booleans], {}] :> boolean,
		_ :> None
	}]
expectedMeaning[_, _, _] := None

(* a trial, with the elaboration state restored after *)
meaningFitsQ[meaning_HoldComplete, arguments_List, expected_] := Block[
	{
		$metavariableAssignments = $metavariableAssignments,
		$levelAssignments = $levelAssignments,
		$metavariableTypes = $metavariableTypes,
		$pendingOverloads = $pendingOverloads
	},
	TrueQ @ Quiet @ catchKernelFailure[
		With[{result = elaborateMeaning[meaning, arguments, expected]}, expected === None || unify[Last[result], expected]]
	]
]

(* the constant itself, applied to the arguments; a && b && c is a && (b && c) for propositions, as Lean's
   ∧, and (a && b) && c for Booleans, as Lean's && *)
elaborateMeaning[meaning_HoldComplete, {}, _] := insertImplicitArguments[constantWithFreshLevels[meaning]]
elaborateMeaning[meaning : HoldComplete[head : And | Or], arguments_List, expected_] /; Length[arguments] > 2 :=
	applyArguments[constantWithFreshLevels[meaning], {First[arguments], rightFold[head, Rest[arguments]]}, syntaxSymbol[meaning], expected]
elaborateMeaning[meaning : HoldComplete[head : BooleanAnd | BooleanOr], arguments_List, expected_] /; Length[arguments] > 2 :=
	applyArguments[constantWithFreshLevels[meaning], {leftFold[head, Most[arguments]], Last[arguments]}, syntaxSymbol[meaning], expected]
elaborateMeaning[meaning_HoldComplete, arguments_List, expected_] := applyArguments[constantWithFreshLevels[meaning], arguments, syntaxSymbol[meaning], expected]

(* a name both meanings fit is a metavariable of the expected type until that type decides *)
postponeOverload[name_HoldComplete, arguments_List, syntax_, expected_] := With[
	{type = Replace[expected, None :> newMetavariable[universeSort[newLevelMetavariable[]]]]},
	With[{placeholder = newMetavariable[type]},
		AppendTo[$pendingOverloads, <|"Placeholder" -> placeholder, "Name" -> name, "Arguments" -> arguments, "Syntax" -> syntax|>];
		{placeholder, type}
	]
]

(* Decides the waiting names from position start + 1 on, one whose type now decides it at a time, since
   deciding one can decide others. With final, a name nothing decides is ambiguous. *)
resolvePendingOverloads[start_Integer, final_] := With[
	{
		decided = SelectFirst[
			Function[entry, {entry, chosenMeaning[declaredMeanings[$elaborationEnvironment, entry["Name"]], entry["Arguments"], pendingType[entry]]}] /@ Drop[$pendingOverloads, start],
			Function[pair, Last[pair] =!= None],
			None
		]
	},
	Which[
		decided =!= None,
			$pendingOverloads = DeleteCases[$pendingOverloads, First[decided], {1}, 1];
			decideOverload @@ decided;
			resolvePendingOverloads[start, final],
		final && Length[$pendingOverloads] > start,
			ambiguityFailure[$pendingOverloads[[start + 1]]],
		True,
			Null
	]
]

pendingType[entry_Association] := instantiateMetavariables[$metavariableTypes[First[entry["Placeholder"]]]]

decideOverload[entry_Association, meaning_HoldComplete] := With[{type = pendingType[entry]},
	With[{result = elaborateMeaning[meaning, entry["Arguments"], type]},
		unifyOrFail[Last[result], type, entry["Syntax"]];
		If[ ! unify[entry["Placeholder"], First[result]],
			elaborationFailure["`1` is not the term its use requires.", entry["Syntax"]]
		]
	]
]

ambiguityFailure[entry_Association] := If[ entry["Arguments"] === {} && MatchQ[entry["Name"], HoldComplete[Not | And | Or]],
	kernelFailure[
		"Ambiguous",
		"`1` could be the operation on propositions or on Booleans here: write `2` for the one on Booleans, or give its type with Typed.",
		{HoldForm @@ entry["Name"], HoldForm @@ Last[$overloadedNames[entry["Name"]]]}
	],
	kernelFailure[
		"Ambiguous",
		"`1` could be a proposition or a Boolean here: say which with Typed[`1`, TypeUniverse[0]] or Typed[`1`, Booleans].",
		{HoldForm @@ heldFromSyntax[entry["Syntax"]]}
	]
]

settleOverloads[term_] := (
	resolvePendingOverloads[0, True];
	instantiateMetavariables[term]
)


(* ::Subsection:: *)
(*Universe levels*)


elaborateLevel[syntaxInteger[n_Integer?NonNegative]] := n
elaborateLevel[syntaxSymbol[held_]] /; MemberQ[$universeParameterNames, held] := levelParameter[held]
elaborateLevel[syntaxString[name_]] /; MemberQ[$universeParameterNames, HoldComplete[name]] := levelParameter[HoldComplete[name]]
elaborateLevel[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {level_, syntaxInteger[k_Integer?NonNegative]}]] := normalizeLevel[levelSuccessor[elaborateLevel[level], k]]
elaborateLevel[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {syntaxInteger[k_Integer?NonNegative], level_}]] := normalizeLevel[levelSuccessor[elaborateLevel[level], k]]
elaborateLevel[syntaxApplication[syntaxSymbol[HoldComplete[Max]], levels_List]] := normalizeLevel[levelMaximum @@ (elaborateLevel /@ levels)]
elaborateLevel[syntaxApplication[syntaxSymbol[HoldComplete[ImpredicativeMaximum]], {a_, b_}]] :=
	normalizeLevel[levelImpredicativeMaximum[elaborateLevel[a], elaborateLevel[b]]]
elaborateLevel[other_] := elaborationFailure["`1` is not a universe level; a universe parameter must be declared with the option \"UniverseParameters\".", other]


(* ::Subsection:: *)
(*Metavariables*)


freshMetavariableId[] := ++$metavariableCounter

newMetavariable[type_] := With[{id = freshMetavariableId[]},
	$metavariableTypes[id] = type;
	metavariable[id]
]

newLevelMetavariable[] := levelMetavariable[++$levelMetavariableCounter]

instantiateLevels[level_] := ReplaceRepeated[level, levelMetavariable[id_] /; KeyExistsQ[$levelAssignments, id] :> $levelAssignments[id]]

instantiateMetavariables[term_] := ReplaceRepeated[term, metavariable[id_] /; KeyExistsQ[$metavariableAssignments, id] :> $metavariableAssignments[id]] /. {
	universeSort[level_] :> universeSort[normalizeLevel[instantiateLevels[level]]],
	constantReference[name_, levels_List] :> constantReference[name, Function[level, normalizeLevel[instantiateLevels[level]]] /@ levels]
}

unsolvedMetavariables[term_] := Union[Cases[term, _metavariable | _levelMetavariable, {0, Infinity}]]

(* A binder's type may have metavariables that were solved after the binder was opened; they must be
   filled in before the binder is abstracted, or a solution naming a variable would escape its binder. *)
instantiateContext[context_Association] := Function[entry, Append[entry, "Type" -> instantiateMetavariables[entry["Type"]]]] /@ context


(* ::Subsection:: *)
(*Unification*)


unify[a_, b_] := unifyTerms[instantiateMetavariables[a], instantiateMetavariables[b]]

unifyTerms[a_, b_] := Which[
	a === b,
		True,
	unassignedMetavariableQ[a],
		assignMetavariable[a, b],
	unassignedMetavariableQ[b],
		assignMetavariable[b, a],
	patternApplicationQ[a],
		assignPattern[a, b],
	patternApplicationQ[b],
		assignPattern[b, a],
	MatchQ[a, _universeSort] && MatchQ[b, _universeSort],
		unifyLevels[First[a], First[b]],
	MatchQ[{a, b}, {_dependentFunctionType, _dependentFunctionType} | {_lambdaAbstraction, _lambdaAbstraction}],
		unifyBinders[a, b],
	True,
		attemptOrRestore[unifySpines[a, b]] || unifyReduced[a, b]
]

unassignedMetavariableQ[metavariable[id_]] := ! KeyExistsQ[$metavariableAssignments, id]
unassignedMetavariableQ[_] := False

(* A metavariable applied to distinct variables of the context, ?f[x, y], unifies with a term t by
   ?f = Function[{x, y}, t]: the most general solution, as in higher-order pattern unification. *)
patternApplicationQ[term_] := With[{spine = applicationSpine[term]},
	And[
		unassignedMetavariableQ[First[spine]],
		MatchQ[Last[spine], {__freeVariable}],
		DuplicateFreeQ[Last[spine]],
		AllTrue[Last[spine], Function[variable, KeyExistsQ[$elaborationContext, First[variable]]]]
	]
]

assignPattern[term_, value_] := With[{spine = applicationSpine[term]},
	assignMetavariable[First[spine], makeLambda[instantiateContext[$elaborationContext], First /@ Last[spine], value]]
]

(* A solution must have the metavariable's type; unifying the two types is what solves universe levels,
   such as the level of Equal in a == b once the type of a is known. *)
assignMetavariable[metavariable[id_], value_] := If[ ! FreeQ[value, metavariable[id]],
	False,
	$metavariableAssignments[id] = value;
	With[{valueType = Quiet @ catchKernelFailure[inferType[$elaborationEnvironment, $elaborationContext, value]]},
		FailureQ[valueType] || ! KeyExistsQ[$metavariableTypes, id] || unify[$metavariableTypes[id], valueType]
	]
]

(* undo the solutions a failed attempt recorded *)
SetAttributes[attemptOrRestore, HoldFirst]
attemptOrRestore[attempt_] := With[{assignments = $metavariableAssignments, levels = $levelAssignments},
	If[ TrueQ[attempt],
		True,
		$metavariableAssignments = assignments;
		$levelAssignments = levels;
		False
	]
]

unifySpines[a_, b_] := With[{spineA = applicationSpine[a], spineB = applicationSpine[b]},
	And[
		Length[Last[spineA]] == Length[Last[spineB]],
		unifyHeads[First[spineA], First[spineB]],
		AllTrue[Transpose[{Last[spineA], Last[spineB]}], Function[pair, unify[First[pair], Last[pair]]]]
	]
]

unifyHeads[constantReference[name_, levels_List], constantReference[name_, otherLevels_List]] :=
	Length[levels] == Length[otherLevels] && AllTrue[Transpose[{levels, otherLevels}], Apply[unifyLevels]]
unifyHeads[a_, b_] := a === b

unifyBinders[(head : dependentFunctionType | lambdaAbstraction)[name_, domain_, body_, binder_], head_[_, otherDomain_, otherBody_, _]] := And[
	unify[domain, otherDomain],
	With[{id = freshFreeVariable[]},
		Block[{$elaborationContext = extendContext[$elaborationContext, id, name, instantiateMetavariables[domain], binder]},
			unify[instantiateBoundVariable[body, freeVariable[id]], instantiateBoundVariable[otherBody, freeVariable[id]]]
		]
	]
]

unifyReduced[a_, b_] := With[
	{
		reducedA = weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, a],
		reducedB = weakHeadNormalForm[$elaborationEnvironment, $elaborationContext, b]
	},
	Which[
		reducedA =!= a || reducedB =!= b,
			unify[reducedA, reducedB],
		MatchQ[a, _naturalLiteral] || MatchQ[b, _naturalLiteral],
			unifyLiterals[a, b],
		MatchQ[a, _lambdaAbstraction],
			unifyEta[a, b],
		MatchQ[b, _lambdaAbstraction],
			unifyEta[b, a],
		FreeQ[{a, b}, _metavariable | _levelMetavariable],
			definitionallyEqualQ[$elaborationEnvironment, $elaborationContext, a, b],
		True,
			False
	]
]

unifyLiterals[a_, b_] := With[{formA = toConstructorForm[$elaborationEnvironment, a], formB = toConstructorForm[$elaborationEnvironment, b]},
	(formA =!= a || formB =!= b) && unify[formA, formB]
]

unifyEta[lambdaAbstraction[name_, domain_, body_, binder_], other_] := With[{id = freshFreeVariable[]},
	Block[{$elaborationContext = extendContext[$elaborationContext, id, name, instantiateMetavariables[domain], binder]},
		unify[instantiateBoundVariable[body, freeVariable[id]], application[other, freeVariable[id]]]
	]
]

unifyLevels[a_, b_] := With[{first = normalizeLevel[instantiateLevels[a]], second = normalizeLevel[instantiateLevels[b]]},
	Which[
		first === second,
			True,
		MatchQ[first, _levelMetavariable],
			assignLevel[first, second],
		MatchQ[second, _levelMetavariable],
			assignLevel[second, first],
		(* the successor is injective: u + 2 = ?w + 1 is u + 1 = ?w *)
		MatchQ[{first, second}, {levelSuccessor[_, _], levelSuccessor[_, _]}],
			With[{common = Min[Last[first], Last[second]]}, unifyLevels[lowerLevel[first, common], lowerLevel[second, common]]],
		MatchQ[first, levelSuccessor[_levelMetavariable, _]] && IntegerQ[second] && second >= Last[first],
			unifyLevels[First[first], second - Last[first]],
		MatchQ[second, levelSuccessor[_levelMetavariable, _]] && IntegerQ[first] && first >= Last[second],
			unifyLevels[First[second], first - Last[second]],
		True,
			levelEquivalentQ[first, second]
	]
]

lowerLevel[levelSuccessor[level_, k_], k_] := level
lowerLevel[levelSuccessor[level_, k_], j_] := levelSuccessor[level, k - j]

assignLevel[levelMetavariable[id_], level_] := (
	$levelAssignments[id] = level;
	True
)

unifyOrFail[actual_, expected_, syntax_] := If[ ! unify[actual, expected],
	kernelFailure[
		"TypeMismatch",
		"`1` has type `2`, but the expected type is `3`.",
		{
			HoldForm @@ heldFromSyntax[syntax],
			displayCoreTerm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[actual]],
			displayCoreTerm[$elaborationEnvironment, $elaborationContext, instantiateMetavariables[expected]]
		}
	]
]
