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
	$metavariableContexts                           the free variables in scope where each metavariable was made
	$levelAssignments                               universe level metavariable solutions
	$elaborationEnvironment                         the environment
	$elaborationContext                             the local context
	$elaborationScope                               <|HoldComplete[symbol] -> {term, type}, ...|>: what each name stands for
	$universeParameterNames                         {HoldComplete[u], ...}: the universe parameters a term may mention

A binder's variable stands for a fresh free variable; With[{x = v}, b] makes x stand for v itself. A
symbol whose value is a TypeTheoryTerm stands for that term, and one whose value is a finished
TypeTheoryProof stands for its proof, so terms and proofs can be built up in a notebook. A symbol whose
value is a declared constant stands for that constant, as Naturals = NonNegativeIntegers does, and so
does InductiveRecursor[Naturals] for the recursor.

While a tactic elaborates a term for a goal, $goalMetavariableTypes gives the types of the proof's open
goals, which may occur in the goal's type, and $goalMetavariableContexts their hypotheses.

A metavariable has the local context it was made in, as in Lean: its solution may name only the
variables of that context. A metavariable left unsolved in a function when its binders close is lifted
out of them, so it never names a variable after the variable's binder is gone.

True, False, Not, And and Or are overloaded: they stand for the propositions or, in an environment that
declares them, for the Booleans' constants "true", "false", "not", "and" and "or", named by strings. The
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
PackageScoped[$goalMetavariableContexts]
PackageScoped[$metavariableContexts]
PackageScoped[$levelAssignments]
PackageScoped[$elaborationEnvironment]
PackageScoped[$elaborationContext]
PackageScoped[$elaborationScope]
PackageScoped[$universeParameterNames]
PackageScoped[overloadedNameQ]
PackageScoped[aliasResolvedName]
PackageScoped[settleOverloads]
PackageScoped[explicitTerm]


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
newMetavariable::usage = "newMetavariable[type] gives a fresh metavariable of the given type, made in the local context. \
newMetavariable[type, {id, ...}] gives one made in the context of the free variables ids."
unsolvedMetavariables::usage = "unsolvedMetavariables[term] gives the metavariables and universe level metavariables left in term."
freshMetavariableId::usage = "freshMetavariableId[] gives an identifier no metavariable has used."
attemptOrRestore::usage = "attemptOrRestore[attempt] evaluates attempt and gives True if it gives True; otherwise it undoes the solutions attempt recorded and gives False."
$goalMetavariableTypes::usage = "$goalMetavariableTypes is the Association from the open goals of a proof to their types while a tactic elaborates a term."
$goalMetavariableContexts::usage = "$goalMetavariableContexts is the Association from the open goals of a proof to the ids of their hypotheses while a tactic elaborates a term."
$metavariableContexts::usage = "$metavariableContexts is the Association from metavariable identifiers to the ids of the free variables in scope where each was made, while elaborating."
$levelAssignments::usage = "$levelAssignments is the Association of solved universe level metavariables while elaborating."
$elaborationEnvironment::usage = "$elaborationEnvironment is the environment while elaborating."
$elaborationContext::usage = "$elaborationContext is the local context while elaborating."
$elaborationScope::usage = "$elaborationScope gives the term and type each variable name stands for while elaborating."
$universeParameterNames::usage = "$universeParameterNames is the list of universe parameters a term may mention while elaborating."
overloadedNameQ::usage = "overloadedNameQ[environment, HoldComplete[name]] gives True if name stands for more than one constant of environment, as True does for the proposition and the Boolean."
settleOverloads::usage = "settleOverloads[term] decides the overloaded names still waiting for their type, and gives term with the solutions found."
explicitTerm::usage = "explicitTerm[environment, HoldComplete[term], {HoldComplete[u], ...}] gives the core term of a term that gives every argument and every \
universe level, or that is a core term already, unchecked, or None if the term is not that explicit."
aliasResolvedName::usage = "aliasResolvedName[environment, HoldComplete[name]] gives the held name of the constant name stands for: a symbol whose value is a declared constant of environment stands for that constant, as Naturals does for NonNegativeIntegers, also inside InductiveRecursor."


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
$goalMetavariableContexts = <||>
$metavariableContexts = <||>
$pendingOverloads = {}


SetAttributes[withElaborationState, HoldRest]
withElaborationState[{environment_, context_, scope_, universeParameters_}, body_] := Block[
	{
		$metavariableTypes = $goalMetavariableTypes,
		$metavariableContexts = $goalMetavariableContexts,
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
		withKernelCaches[
			If[ expected === None,
				{finalTerm, inferType[environment, context, finalTerm]},
				checkHasType[environment, context, finalTerm, expected];
				{finalTerm, expected}
			]
		]
	]
]


(* ::Subsection:: *)
(*Syntax*)


elaborateSyntax[syntax_, expected_] := Replace[syntax, {
	syntaxApplication[syntaxSymbol[HoldComplete[Function]], {binders_, body_}] :> elaborateFunction[listElements[binders], body, expected],
	syntaxApplication[syntaxSymbol[HoldComplete[ForAll | RightTee]], {binders_, body_}] :> elaborateForAll[listElements[binders], body],
	syntaxApplication[syntaxSymbol[HoldComplete[Exists]], {binders_, body_}] :> elaborateSyntax[nestedExistential[listElements[binders], body], expected],
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
	_ /; declaredConstantSyntaxQ[syntax] :> insertImplicitArguments[constantWithFreshLevels[constantNameOfSyntax[syntax]]],
	syntaxApplication[head_, arguments_List] :> applyArguments[elaborateHead[head], arguments, head, expected],
	syntaxInteger[n_Integer?NonNegative] :> {naturalLiteral[n], naturalNumberTypeForElaboration[syntax]},
	syntaxSymbol[HoldComplete[symbol_Symbol]] /; storedValueQ[symbol] :> elaborateStoredValue[symbol, expected],
	_ :> elaborationFailure["`1` is not a term of the type theory: it is neither a variable in scope nor a declared constant.", syntax]
}]

(* Exists[{x, y}, p] is Exists[{x}, Exists[{y}, p]], as in Lean, each Exists applied to a predicate *)
nestedExistential[{binder_}, body_] := syntaxHead[Exists, {syntaxHead[Function, {syntaxHead[List, {binder}], body}]}]
nestedExistential[{binder_, rest__}, body_] := nestedExistential[{binder}, syntaxHead[Exists, {syntaxHead[List, {rest}], body}]]

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

declaredConstantSyntaxQ[syntax : (_syntaxSymbol | _syntaxString | _syntaxApplication)] := constantDeclaredQ[$elaborationEnvironment, constantNameOfSyntax[syntax]]
declaredConstantSyntaxQ[_] := False

constantNameOfSyntax[syntax_] := aliasResolvedName[$elaborationEnvironment, heldFromSyntax[syntax]]

(* the constant a held name names: a symbol whose value is a declared constant names that constant *)
aliasResolvedName[environment_, held_HoldComplete] := Replace[held, {
	HoldComplete[symbol_Symbol] :> Replace[aliasedConstant[environment, symbol], None :> HoldComplete[symbol]],
	HoldComplete[InductiveRecursor[symbol_Symbol]] :> Replace[aliasedConstant[environment, symbol], {
		HoldComplete[constant_] :> HoldComplete[InductiveRecursor[constant]],
		None :> HoldComplete[InductiveRecursor[symbol]]
	}]
}]

(* an overloaded name is left to its own rules, which decide between its meanings by type *)
SetAttributes[aliasedConstant, HoldRest]
aliasedConstant[environment_, symbol_Symbol] := Replace[OwnValues[symbol], {
	{Verbatim[RuleDelayed][_, constant_Symbol]} /; constantDeclaredQ[environment, HoldComplete[constant]] && ! overloadedNameQ[environment, HoldComplete[constant]] :>
		HoldComplete[constant],
	_ :> None
}]

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
	If[record["Kind"] === "RewriteRule", elaborationFailure["`1` is a rewrite rule, not a term.", toSyntax @@ held]];
	With[{levels = Table[newLevelMetavariable[], Length[record["UniverseParameters"]]]},
		{constantReference[held, levels], instantiateUniverseParameters[record["Type"], record["UniverseParameters"], levels]}
	]
]

constantWithLevels[constantSyntax_, levelSyntaxes_List] := With[{held = constantNameOfSyntax[constantSyntax]},
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

elaborateHead[syntax : syntaxSymbol[held_]] /; ! KeyExistsQ[$elaborationScope, held] && declaredConstantSyntaxQ[syntax] := constantWithFreshLevels[constantNameOfSyntax[syntax]]
elaborateHead[syntax : syntaxString[name_]] /; ! KeyExistsQ[$elaborationScope, HoldComplete[name]] && declaredConstantSyntaxQ[syntax] :=
	constantWithFreshLevels[HoldComplete[name]]
elaborateHead[syntax_syntaxApplication] /; declaredConstantSyntaxQ[syntax] := constantWithFreshLevels[constantNameOfSyntax[syntax]]
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
parseBinder[syntaxApplication[syntaxSymbol[HoldComplete[TypedImplicit]], {name_, type_}]] :=
	Append[parseBinder[syntaxApplication[syntaxSymbol[HoldComplete[Typed]], {name, type}]], "Binder" -> "Implicit"]
parseBinder[syntaxSymbol[name_]] := <|"Name" -> name, "Type" -> None, "Binder" -> "Explicit"|>
parseBinder[syntaxString[name_]] := <|"Name" -> HoldComplete[name], "Type" -> None, "Binder" -> "Explicit"|>
parseBinder[other_] := elaborationFailure["`1` is not a binder: write Typed[x, type] or TypedImplicit[x, type].", other]

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
			liftMetavariables[opened["Ids"], {result, boundVariableTypes[opened["Ids"]]}];
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
					liftMetavariables[opened["Ids"], {bodyType, boundVariableTypes[opened["Ids"]]}];
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
	HoldComplete[True] -> {HoldComplete[True], HoldComplete["true"]},
	HoldComplete[False] -> {HoldComplete[False], HoldComplete["false"]},
	HoldComplete[Not] -> {HoldComplete[Not], HoldComplete["not"]},
	HoldComplete[And] -> {HoldComplete[And], HoldComplete["and"]},
	HoldComplete[Or] -> {HoldComplete[Or], HoldComplete["or"]}
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
		$metavariableContexts = $metavariableContexts,
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
	applyArguments[constantWithFreshLevels[meaning], {First[arguments], rightFold[head, Rest[arguments]]}, nameSyntax[meaning], expected]
elaborateMeaning[meaning : HoldComplete["and" | "or"], arguments_List, expected_] /; Length[arguments] > 2 :=
	applyArguments[
		constantWithFreshLevels[meaning],
		{Fold[Function[{accumulated, next}, syntaxApplication[nameSyntax[meaning], {accumulated, next}]], First[arguments], Rest[Most[arguments]]], Last[arguments]},
		nameSyntax[meaning],
		expected
	]
elaborateMeaning[meaning_HoldComplete, arguments_List, expected_] := applyArguments[constantWithFreshLevels[meaning], arguments, nameSyntax[meaning], expected]

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

(* the Boolean meaning is named by a string, which says which of the two is meant where nothing else does *)
ambiguityFailure[entry_Association] := Which[
	entry["Arguments"] === {} && MatchQ[entry["Name"], HoldComplete[Not | And | Or]],
		kernelFailure[
			"Ambiguous",
			"`1` could be the operation on propositions or on Booleans here: write `2` for the one on Booleans, or give its type with Typed.",
			{HoldForm @@ entry["Name"], First[Last[$overloadedNames[entry["Name"]]]]}
		],
	entry["Arguments"] === {},
		kernelFailure[
			"Ambiguous",
			"`1` could be a proposition or a Boolean here: write `2` for the Boolean, or Typed[`1`, TypeUniverse[0]] for the proposition.",
			{HoldForm @@ entry["Name"], First[Last[$overloadedNames[entry["Name"]]]]}
		],
	True,
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
(*Explicit terms*)


(* A term that leaves elaboration nothing to infer, as Normal and an import from another proof assistant
   write it, is translated straight into a core term, with no inference and no unification: every universe
   level is given with Subscript, and every argument is given, with Construct or to an explicit binder.
   Names in scope become bound variables, and the rest constants. The translation is not checked, and needs
   not be: the declaration it goes into has the kernel check it, as every declaration does. Anything else,
   an implicit argument to infer, an overloaded name, an ascription, makes the term not explicit, and it is
   elaborated as usual. *)
(* a core term, as an import builds it, is already explicit *)
explicitTerm[_, HoldComplete[term : (_application | _lambdaAbstraction | _dependentFunctionType | _localDefinition | _projection | _constantReference | _universeSort | _naturalLiteral)], _] := term
explicitTerm[environment_, held_HoldComplete, universeParameters_List] := Block[
	{$elaborationEnvironment = environment, $universeParameterNames = universeParameters},
	Catch[explicitCore[toSyntax @@ held, {}], $notExplicitTag]
]

(* the scope lists the binders around a subterm, innermost first, as {HoldComplete[name], type} *)
explicitCore[syntaxApplication[syntaxSymbol[HoldComplete[Construct]], {head_, arguments___}], scope_] :=
	makeApplication[explicitHead[head, scope], Function[argument, explicitCore[argument, scope]] /@ {arguments}]
explicitCore[syntaxApplication[syntaxSymbol[HoldComplete[head : ForAll | Function]], {binders_, body_}], scope_] := explicitBinders[head, listElements[binders], body, scope]
explicitCore[syntaxApplication[syntaxSymbol[HoldComplete[With]], {bindings_, body_}], scope_] := explicitDefinitions[listElements[bindings], body, scope]
explicitCore[syntaxApplication[syntaxSymbol[HoldComplete[TypeUniverse]], {level_}], _] := universeSort[elaborateLevel[level]]
explicitCore[syntaxApplication[syntaxSymbol[HoldComplete[Part]], {structureTerm_, syntaxInteger[index_Integer?Positive]}], scope_] :=
	With[{structureCore = explicitCore[structureTerm, scope]}, projection[explicitStructure[structureCore, scope], index - 1, structureCore]]
explicitCore[syntaxInteger[n_Integer?NonNegative], _] /; naturalNumberSettings[$elaborationEnvironment] =!= None := naturalLiteral[n]
explicitCore[syntax : (syntaxSymbol[_] | syntaxString[_] | syntaxApplication[syntaxSymbol[HoldComplete[Subscript]], {_, __}]), scope_] := onItsOwn[explicitHead[syntax, scope]]
(* A -> B, written as Implies or TypeSpecifier: its binders are anonymous, as the elaborator writes them *)
explicitCore[syntaxApplication[syntaxSymbol[HoldComplete[Implies]], {domain_, codomain_}], scope_] := explicitArrow[{domain}, codomain, scope]
explicitCore[syntaxApplication[syntaxSymbol[HoldComplete[TypeSpecifier]], {syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {domains_, codomain_}]}], scope_] :=
	explicitArrow[listElements[domains], codomain, scope]
(* f[a, ...] is exact when each binder of the type of f that an argument fills is explicit, for elaboration
   would fill an implicit one itself; but a declared constant named f[a, ...], as InductiveRecursor[Paint]
   is, is that constant, as elaboration reads it, after an overloaded name and a difference *)
explicitCore[syntax : syntaxApplication[head : (syntaxSymbol[_] | syntaxString[_] | syntaxApplication[syntaxSymbol[HoldComplete[Subscript | Function | Part]], _] | _syntaxApplication?declaredConstantSyntaxQ), arguments_List], scope_] /;
	! notationHeadQ[head, Length[arguments]] :=
	Which[
		readBeforeNamesQ[syntax, scope],
			Throw[None, $notExplicitTag],
		declaredConstantSyntaxQ[syntax],
			onItsOwn[explicitConstantReference[syntax]],
		True,
			With[{headCore = explicitHead[head, scope], argumentCores = Function[argument, explicitCore[argument, scope]] /@ arguments},
				If[! explicitArgumentsQ[headCore, argumentCores, scope], Throw[None, $notExplicitTag]];
				makeApplication[headCore, argumentCores]
			]
	]
explicitCore[_, _] := Throw[None, $notExplicitTag]

(* a constant at the head of an application takes the arguments given, and no others *)
explicitHead[syntaxApplication[syntaxSymbol[HoldComplete[Subscript]], {constant_, levels__}], _] := With[{name = explicitConstantName[constant]},
	If[ Length[constantRecord[$elaborationEnvironment, name]["UniverseParameters"]] =!= Length[{levels}],
		Throw[None, $notExplicitTag]
	];
	constantReference[name, Function[level, elaborateLevel[level]] /@ {levels}]
]
explicitHead[syntax : (syntaxSymbol[_] | syntaxString[_]), scope_] := With[{held = heldFromSyntax[syntax]},
	Replace[FirstPosition[scope, {Verbatim[held], _}, None, {1}, Heads -> False], {
		{position_Integer} :> boundVariable[position - 1],
		None :> explicitConstantReference[syntax]
	}]
]
explicitHead[syntax_syntaxApplication, _] /; declaredConstantSyntaxQ[syntax] := explicitConstantReference[syntax]
explicitHead[syntax_, scope_] := explicitCore[syntax, scope]

(* a declared constant named without universe levels, which elaboration fills in for a constant that has them *)
explicitConstantReference[syntax_] := With[{name = explicitConstantName[syntax]},
	If[constantRecord[$elaborationEnvironment, name]["UniverseParameters"] =!= {}, Throw[None, $notExplicitTag]];
	constantReference[name, {}]
]

(* a constant on its own gets its leading implicit arguments, which only elaboration finds *)
onItsOwn[reference_constantReference] /; leadingImplicitQ[constantRecord[$elaborationEnvironment, First[reference]]["Type"]] := Throw[None, $notExplicitTag]
onItsOwn[core_] := core

(* what elaboration reads before it looks for a declared constant of the name: an overloaded name applied,
   unless a variable in scope has the name, and a difference written as a sum *)
readBeforeNamesQ[syntaxApplication[syntaxSymbol[name_], _], scope_] /; ! MemberQ[scope, {Verbatim[name], _}] && overloadedNameQ[$elaborationEnvironment, name] := True
readBeforeNamesQ[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {_, syntaxApplication[syntaxSymbol[HoldComplete[Times]], {syntaxInteger[-1], _}] | syntaxInteger[_Integer?Negative]}], _] := True
readBeforeNamesQ[_, _] := False

(* the heads elaboration reads as notation, whatever constant they also name: a sum of three terms is a
   sum of sums *)
notationHeadQ[syntaxSymbol[HoldComplete[Function | ForAll | RightTee | Exists | Implies | TypeSpecifier | Rule | TypeUniverse | Typed | With | Subscript | Construct | Part]], _] := True
notationHeadQ[syntaxSymbol[HoldComplete[Plus | Times | And | Or]], count_Integer] := count =!= 2
notationHeadQ[_, _] := False

(* whether a constant of this type, on its own, gets implicit arguments from elaboration *)
leadingImplicitQ[dependentFunctionType[_, _, _, binder_]] := binder =!= "Explicit"
leadingImplicitQ[type_] := MatchQ[weakHeadNormalForm[$elaborationEnvironment, <||>, type], dependentFunctionType[_, _, _, Except["Explicit"]]]

(* each domain lies under the binders of the domains before it, which name nothing a term can refer to *)
explicitArrow[domains_List, codomain_, scope_] := Module[{inner = scope, cores = {}},
	Scan[
		Function[domain, With[{core = explicitCore[domain, inner]},
			cores = Append[cores, core];
			inner = Prepend[inner, {HoldComplete[anonymousBinder], core}]
		]],
		domains
	];
	Fold[
		Function[{accumulated, domainCore}, dependentFunctionType[HoldComplete[\[FormalX]], domainCore, accumulated, "Explicit"]],
		explicitCore[codomain, inner],
		Reverse[cores]
	]
]

(* The binders the arguments fill are read off the type of the head as written. A type that is not a
   function type as written may unfold to one, as DecidableEq Nat does, or become one once the arguments
   before are put in, as the type of a recursor whose motive gives a function does: that type is read as
   the kernel types the application. *)
explicitArgumentsQ[headCore_, argumentCores_List, scope_] := Replace[
	writtenBindersQ[explicitHeadType[headCore, scope], Length[argumentCores]],
	None :> unfoldedBindersQ[headCore, argumentCores, scope]
]

explicitHeadType[constantReference[name_, _], _] := constantRecord[$elaborationEnvironment, name]["Type"]
explicitHeadType[boundVariable[index_Integer], scope_] := Last[First[Drop[scope, index]]]
explicitHeadType[lambda_lambdaAbstraction, _] := lambdaBinders[lambda]
explicitHeadType[_, _] := None

(* a function as written takes the binders of its lambdas *)
lambdaBinders[lambdaAbstraction[name_, domain_, body_, binder_]] := dependentFunctionType[name, domain, lambdaBinders[body], binder]
lambdaBinders[_] := None

(* True or False when the type as written decides, None when it does not *)
writtenBindersQ[_, 0] := True
writtenBindersQ[dependentFunctionType[_, _, codomain_, "Explicit"], count_Integer] := writtenBindersQ[codomain, count - 1]
writtenBindersQ[_dependentFunctionType, _] := False
writtenBindersQ[_, _] := None

(* each argument is checked against its binder's type before it goes into the types after, as the kernel
   checks it, so an argument that does not fit makes the term not explicit *)
unfoldedBindersQ[headCore_, argumentCores_List, scope_] := With[{opened = openScope[scope]},
	TrueQ[Quiet @ catchKernelFailure[unfoldedBindersFrom[
		First[opened],
		inferType[$elaborationEnvironment, First[opened], openBound[headCore, Last[opened]]],
		Function[argument, openBound[argument, Last[opened]]] /@ argumentCores
	]]]
]

unfoldedBindersFrom[_, _, {}] := True
unfoldedBindersFrom[context_, type_, {argument_, rest___}] := Replace[weakHeadNormalForm[$elaborationEnvironment, context, type], {
	dependentFunctionType[_, domain_, codomain_, "Explicit"] :> (
		checkHasType[$elaborationEnvironment, context, argument, domain];
		unfoldedBindersFrom[context, instantiateBoundVariable[codomain, argument], {rest}]
	),
	_ :> False
}]

(* a declared constant that names no overloaded meaning, which only elaboration decides *)
explicitConstantName[syntax_] := With[{name = constantNameOfSyntax[syntax]},
	If[ constantDeclaredQ[$elaborationEnvironment, name] && ! overloadedNameQ[$elaborationEnvironment, name] && constantRecord[$elaborationEnvironment, name]["Kind"] =!= "RewriteRule",
		name,
		Throw[None, $notExplicitTag]
	]
]

explicitBinders[head_, binders_List, body_, scope_] := Module[{entries = {}, inner = scope},
	Scan[
		Function[binder, With[{parsed = parseBinder[binder]},
			If[parsed["Type"] === None, Throw[None, $notExplicitTag]];
			With[{entry = {parsed["Name"], explicitCore[parsed["Type"], inner], parsed["Binder"]}},
				entries = Append[entries, entry];
				inner = Prepend[inner, Take[entry, 2]]
			]
		]],
		binders
	];
	Fold[
		Function[{core, entry}, Replace[head, {ForAll -> dependentFunctionType, Function -> lambdaAbstraction}][First[entry], entry[[2]], core, Last[entry]]],
		explicitCore[body, inner],
		Reverse[entries]
	]
]

(* each value goes in for its name, as elaboration puts it in, once it is checked as elaboration checks it *)
explicitDefinitions[{}, body_, scope_] := explicitCore[body, scope]
explicitDefinitions[{syntaxApplication[syntaxSymbol[HoldComplete[Set]], {name : (syntaxSymbol[_] | syntaxString[_]), syntaxApplication[syntaxSymbol[HoldComplete[Typed]], {value_, type_}]}], rest___}, body_, scope_] :=
	With[{held = heldFromSyntax[name], typeCore = explicitCore[type, scope], valueCore = explicitCore[value, scope]},
		If[! bindingChecksQ[valueCore, typeCore, scope], Throw[None, $notExplicitTag]];
		instantiateBoundVariable[explicitDefinitions[{rest}, body, Prepend[scope, {held, typeCore}]], valueCore]
	]
explicitDefinitions[_, _, _] := Throw[None, $notExplicitTag]

(* the type of a binding is a type, and its value has it, with the binders in scope opened: a value put in
   for a name it is not used under would otherwise go unchecked *)
bindingChecksQ[valueCore_, typeCore_, scope_] := With[{opened = openScope[scope]},
	TrueQ[Quiet @ catchKernelFailure[
		sortLevel[$elaborationEnvironment, First[opened], openBound[typeCore, Last[opened]]];
		checkHasType[$elaborationEnvironment, First[opened], openBound[valueCore, Last[opened]], openBound[typeCore, Last[opened]]];
		True
	]]
]

(* A projection names its structure, the head of the type of the term projected from: the kernel infers it,
   with the binders in scope opened. A term it cannot type so, as one that needs the value of a With to
   type, is left to elaboration. *)
explicitStructure[structureCore_, scope_] := Module[{context, ids, opened},
	{context, ids} = openScope[scope];
	opened = openBound[structureCore, ids];
	Replace[Quiet @ catchKernelFailure[First @ applicationSpine[weakHeadNormalForm[$elaborationEnvironment, context, inferType[$elaborationEnvironment, context, opened]]]], {
		constantReference[name_, _] /; structureLikeQ[$elaborationEnvironment, name] :> name,
		_ :> Throw[None, $notExplicitTag]
	}]
]

(* the binders in scope as free variables, outermost first: the context they make, and their ids, innermost first *)
openScope[scope_] := Module[{context = <||>, ids = {}},
	Scan[
		Function[entry, With[{id = freshFreeVariable[]},
			context = extendContext[context, id, First[entry], openBound[Last[entry], ids], "Explicit"];
			ids = Prepend[ids, id]
		]],
		Reverse[scope]
	];
	{context, ids}
]

(* the bound variables of a term, 0 innermost, as the free variables ids, innermost first *)
openBound[term_, ids_List] := Fold[Function[{core, id}, instantiateBoundVariable[core, freeVariable[id]]], term, ids]


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

newMetavariable[type_] := newMetavariable[type, Keys[$elaborationContext]]
newMetavariable[type_, context_List] := With[{id = freshMetavariableId[]},
	$metavariableTypes[id] = type;
	$metavariableContexts[id] = context;
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

boundVariableTypes[ids_List] := Function[id, $elaborationContext[id]["Type"]] /@ ids

(* Before the variables ids are abstracted, each metavariable left unsolved in terms whose context has one
   of them is replaced by a new one made outside them, applied to them, as Lean's elimMVarDeps does: ?m,
   made with x in scope, becomes ?n[x], where ?n has the type (x : A) -> T. A solution found for it later,
   under another binder, may then depend on the variable there, and no solution names x once x is gone.
   The variables of its context from the first of ids on are abstracted, with the ones after that depend
   on them; they must be in the local context, or the lifting fails. *)
liftMetavariables[ids_List, terms_] := AllTrue[
	Select[reachableMetavariables[terms], Function[id, IntersectingQ[Lookup[$metavariableContexts, id, {}], ids]]],
	Function[id, liftMetavariable[id, Drop[$metavariableContexts[id], First @ FirstPosition[$metavariableContexts[id], Alternatives @@ ids, None, {1}] - 1]]]
]

liftMetavariable[id_, local_List] := And[
	SubsetQ[Keys[$elaborationContext], local],
	With[
		{
			lifted = newMetavariable[
				makeDependentFunctionType[instantiateContext[$elaborationContext], local, instantiateMetavariables[$metavariableTypes[id]]],
				Drop[$metavariableContexts[id], -Length[local]]
			]
		},
		$metavariableAssignments[id] = makeApplication[lifted, freeVariable /@ local];
		True
	]
]

(* the unsolved metavariables of terms and of their types, in the order they were made, which puts each after the ones its type mentions *)
reachableMetavariables[terms_] := Sort @ FixedPoint[
	Function[ids, Union[ids, unsolvedMetavariableIds[Lookup[$metavariableTypes, ids, Nothing]]]],
	unsolvedMetavariableIds[terms]
]

unsolvedMetavariableIds[term_] := Union @ Cases[instantiateMetavariables[term], metavariable[id_] :> id, {0, Infinity}]

freeVariableIds[term_] := Union @ Cases[term, freeVariable[id_] :> id, {0, Infinity}]

(* Whether term may stand where only the variables allowed are in scope, as a solution of a metavariable
   made there: it names no other variable, and each unsolved metavariable in it made in a larger context is
   restricted to the variables both contexts have, as Lean's checkAssignment does, by a solution that is a
   new metavariable made in the smaller context. A solution found for it later then names no variable the
   solution it is part of must not. *)
withinContextQ[_, All] := True
withinContextQ[term_, allowed_List] := And[
	SubsetQ[allowed, freeVariableIds[instantiateMetavariables[term]]],
	AllTrue[unsolvedMetavariableIds[term], Function[id, restrictedQ[id, allowed]]]
]

restrictedQ[id_, allowed_List] := With[{context = Lookup[$metavariableContexts, id, All]},
	Or[
		context === All || SubsetQ[allowed, context],
		With[{kept = Select[context, Function[variable, MemberQ[allowed, variable]]]},
			withinContextQ[$metavariableTypes[id], kept] && (
				$metavariableAssignments[id] = newMetavariable[instantiateMetavariables[$metavariableTypes[id]], kept];
				True
			)
		]
	]
]


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
   ?f = Function[{x, y}, t]: the most general solution, as in higher-order pattern unification. A
   variable applied to the pattern's variables is that variable: ?f[x, y] against g[x, y], with g a
   variable, gives ?f = g, and so is a constant applied to exactly them, as "not"[a]. A constant
   applied to more keeps its function, so the solution reads (n) ↦ 0 + n rather than Plus[0]. *)
patternApplicationQ[term_] := With[{spine = applicationSpine[term]},
	And[
		unassignedMetavariableQ[First[spine]],
		MatchQ[Last[spine], {__freeVariable}],
		DuplicateFreeQ[Last[spine]],
		AllTrue[Last[spine], Function[variable, KeyExistsQ[$elaborationContext, First[variable]]]]
	]
]

(* the metavariables of value made under the pattern's variables are lifted out of them first, for the solution abstracts them *)
assignPattern[term_, value_] := With[{spine = applicationSpine[term]},
	liftMetavariables[First /@ Last[spine], value] && assignMetavariable[First[spine], etaReducedSolution[First /@ Last[spine], instantiateMetavariables[value]]]
]

(* the trailing arguments of value that are the trailing pattern variables, in order and nowhere else, are dropped with their binders *)
etaReducedSolution[ids_List, value_] := With[{valueSpine = applicationSpine[value]},
	With[
		{
			droppable = LengthWhile[
				Range[Min[Length[ids], Length[Last[valueSpine]]]],
				Function[k, And[
					Last[valueSpine][[-k]] === freeVariable[ids[[-k]]],
					FreeQ[Fold[application, First[valueSpine], Drop[Last[valueSpine], -k]], freeVariable[ids[[-k]]]]
				]]
			]
		},
		With[{dropped = If[MatchQ[First[valueSpine], _freeVariable] || droppable === Length[Last[valueSpine]], droppable, 0]},
			makeLambda[instantiateContext[$elaborationContext], Drop[ids, -dropped], Fold[application, First[valueSpine], Drop[Last[valueSpine], -dropped]]]
		]
	]
]

(* A solution must have the metavariable's type; unifying the two types is what solves universe levels,
   such as the level of Equal in a == b once the type of a is known. It names only variables of the
   context the metavariable was made in. *)
assignMetavariable[metavariable[id_], value_] := If[ ! FreeQ[value, metavariable[id]] || ! withinContextQ[value, Lookup[$metavariableContexts, id, All]],
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

(* as the kernel compares terms: reduced without unfolding definitions first, then with *)
unifyReduced[a_, b_] := With[
	{
		coreA = reducedHeadWithoutUnfolding[$elaborationEnvironment, $elaborationContext, a],
		coreB = reducedHeadWithoutUnfolding[$elaborationEnvironment, $elaborationContext, b]
	},
	If[coreA =!= a || coreB =!= b, unify[coreA, coreB], unifyUnfolded[a, b]]
]

unifyUnfolded[a_, b_] := With[
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
