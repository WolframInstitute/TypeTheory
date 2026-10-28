(* ::Package:: *)

(*
Type inference, weak head normalization and definitional equality: the trusted kernel.

Every function takes the environment and a local context, an Association

	<|id -> <|"Name" -> HoldComplete[name], "Type" -> type, "Binder" -> binder|>, ...|>

giving the type of each freeVariable[id]. Going under a binder replaces its bound variable with a
fresh free variable, so the kernel never manipulates loose bound variables.

inferType checks: an application checks its argument against the domain, a binder checks that its
domain is a type. Definitional equality and reduction ask the types of the terms they compare, and
inside a declaration's check, where those terms are checked or reducts of checked terms, they infer
them without checking, as Lean's kernel does in its infer-only mode.

Reduction implements beta, zeta (local definitions), delta (unfolding definitions; theorems are never
unfolded), iota (a recursor applied to a constructor, natural literals read as constructors, and
K-like recursors such as that of Equal), a quotient's lift or induction applied to a class
(Quotients.wl), and addition of natural literals on Wolfram Language integers when the environment
registers an addition, and the rewrite rules of an axiom where the environment's rules allow them.
Definitional equality adds eta for functions and proof irrelevance: two proofs of the same proposition
are equal. It decides in the order of Lean's kernel: each side reduced without unfolding a definition,
then proof irrelevance, then lazy delta, which compares the arguments of one definition at both heads
before unfolding it.

Under rules without Prop, every universe level must be at least 1 whatever its universe parameters are,
so no type is a proposition, and proof irrelevance and K-like reduction never apply. Under rules with
quantities a binder may carry a quantity, 0 or 1, and two function types are equal only if their binders
have the same quantity; elsewhere a binder with a quantity does not check (Quantities.wl).

Metavariables only appear while elaborating; their types and assignments are read from
$metavariableTypes and $metavariableAssignments, which the elaborator binds.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[inferType]
PackageScoped[withKernelCaches]
PackageScoped[withCheckedTerms]
PackageScoped[$termsChecked]
PackageScoped[projectionFunctionQ]
PackageScoped[weakHeadNormalForm]
PackageScoped[reducedHeadWithoutUnfolding]
PackageScoped[definitionallyEqualQ]
PackageScoped[sortLevel]
PackageScoped[checkHasType]
PackageScoped[freshFreeVariable]
PackageScoped[extendContext]
PackageScoped[extendLocalDefinition]
PackageScoped[makeLambda]
PackageScoped[makeDependentFunctionType]
PackageScoped[toConstructorForm]
PackageScoped[structureLikeQ]
PackageScoped[$metavariableTypes]
PackageScoped[$metavariableAssignments]


(* ::Section:: *)
(*Usage Messages*)


inferType::usage = "inferType[environment, context, term] gives the type of term, checking it; a term that does not type-check throws a kernel failure."
weakHeadNormalForm::usage = "weakHeadNormalForm[environment, context, term] reduces term until its head can no longer reduce."
reducedHeadWithoutUnfolding::usage = "reducedHeadWithoutUnfolding[environment, context, term] reduces the head of term as far as it reduces without unfolding a definition."
definitionallyEqualQ::usage = "definitionallyEqualQ[environment, context, a, b] gives True if a and b are equal by computation, eta and proof irrelevance."
sortLevel::usage = "sortLevel[environment, context, type] gives the level of the sort type belongs to, or throws a kernel failure if type is not a type."
checkHasType::usage = "checkHasType[environment, context, term, type] throws a kernel failure unless term has a type definitionally equal to type."
freshFreeVariable::usage = "freshFreeVariable[] gives an identifier no free variable has used."
withKernelCaches::usage = "withKernelCaches[body] evaluates body remembering the kernel's inferred types, weak head normal forms and definitional equalities, unless an enclosing check already does."
withCheckedTerms::usage = "withCheckedTerms[body] evaluates body with the kernel's caches, where every term compared is checked or a reduct of a checked term, \
so that definitional equality and reduction infer the types they ask without checking them."
$termsChecked::usage = "$termsChecked is True where every term the kernel compares is checked or a reduct of a checked term, as inside withCheckedTerms; \
elaboration and tactics set it to False, as their terms are not checked until elaboration finishes."
projectionFunctionQ::usage = "projectionFunctionQ[value] gives True if the core term value takes arguments and projects a field out of the last, \
as a structure's projection function does: a definition with such a value is an abbreviation, which lazy delta unfolds first."
extendContext::usage = "extendContext[context, id, HoldComplete[name], type, binder] gives context with freeVariable[id] of type type."
extendLocalDefinition::usage = "extendLocalDefinition[context, id, HoldComplete[name], type, value] gives context with freeVariable[id] of type type standing for value."
makeLambda::usage = "makeLambda[context, {id, ...}, body] abstracts the free variables id, ..., innermost last, into functions."
makeDependentFunctionType::usage = "makeDependentFunctionType[context, {id, ...}, body] abstracts the free variables id, ..., innermost last, into a function type."
toConstructorForm::usage = "toConstructorForm[environment, term] writes a natural literal as a constructor application, and gives any other term unchanged."
structureLikeQ::usage = "structureLikeQ[environment, HoldComplete[name]] gives True if name is a structure: an inductive type with one constructor, \
no indices and no recursive fields, whose fields projections read."
$metavariableTypes::usage = "$metavariableTypes is the Association from metavariable identifiers to their types while elaborating."
$metavariableAssignments::usage = "$metavariableAssignments is the Association from metavariable identifiers to their solutions while elaborating."


(* ::Section:: *)
(*Function Definitions*)


$metavariableTypes = <||>
$metavariableAssignments = <||>
$freeVariableCounter = 0

(* While it checks a declaration, the kernel remembers the types it has inferred, the weak head normal
   forms it has computed and the definitional equalities it has decided, for a proof meets the same
   subterms again and again. The free variables of a term are fresh for each binder opened, so a term
   means the same wherever it occurs in one check of one environment; outside a check, while elaborating,
   metavariables get solved, and nothing is remembered. A type inferred without checking is remembered
   apart, so that a check never takes it for a checked one. *)
$inferTypeCache = None
$uncheckedTypeCache = None
$weakHeadNormalFormCache = None
$definitionalEqualityCache = None

SetAttributes[withKernelCaches, HoldFirst]
withKernelCaches[body_] := If[ AssociationQ[$inferTypeCache],
	body,
	Block[{$inferTypeCache = <||>, $uncheckedTypeCache = <||>, $weakHeadNormalFormCache = <||>, $definitionalEqualityCache = <||>, $looseBoundRangeCache = <||>}, body]
]

(* Lean's kernel infers the types that definitional equality and reduction ask in infer-only mode: an
   application's arguments are not checked against their binders, nor a function's domain as a type, nor a
   local definition's value against its type. That is sound where every term compared is checked, or a reduct
   of a checked term. A declaration's check is such a place: it checks the declaration's type before its
   value, and every subterm before comparing the types of its parts, so a comparison meets only the types of
   checked terms, the binder types of checked types, and their reducts. $termsChecked says the kernel is in
   such a place; elsewhere, as while elaborating, the queries check. *)
$termsChecked = False
$inferOnly = False

SetAttributes[withCheckedTerms, HoldFirst]
withCheckedTerms[body_] := withKernelCaches[Block[{$termsChecked = True}, body]]

typeQuery[environment_, context_, term_] := If[ $termsChecked,
	Block[{$inferOnly = True}, inferType[environment, context, term]],
	inferType[environment, context, term]
]

freshFreeVariable[] := ++$freeVariableCounter

extendContext[context_Association, id_Integer, name_, type_, binder : (_String | {_String, _})] := Append[context, id -> <|"Name" -> name, "Type" -> type, "Binder" -> binder|>]

makeLambda[context_Association, ids_List, body_] := Fold[
	Function[{accumulated, id}, With[{entry = context[id]}, Construct[lambdaAbstraction, entry["Name"], entry["Type"], abstractFreeVariable[accumulated, id], entry["Binder"]]]],
	body,
	Reverse[ids]
]

makeDependentFunctionType[context_Association, ids_List, body_] := Fold[
	Function[{accumulated, id}, With[{entry = context[id]}, Construct[dependentFunctionType, entry["Name"], entry["Type"], abstractFreeVariable[accumulated, id], entry["Binder"]]]],
	body,
	Reverse[ids]
]


(* ::Subsection:: *)
(*Type inference*)


(* a checked type answers a query that does not check, never the other way *)
inferType[environment_, context_, term_] := Which[
	! AssociationQ[$inferTypeCache],
		inferTypeOf[environment, context, term],
	$inferOnly,
		Lookup[
			$inferTypeCache,
			Key[{environment, term}],
			Lookup[$uncheckedTypeCache, Key[{environment, term}], $uncheckedTypeCache[{environment, term}] = inferTypeOf[environment, context, term]]
		],
	True,
		Lookup[$inferTypeCache, Key[{environment, term}], $inferTypeCache[{environment, term}] = inferTypeOf[environment, context, term]]
]

inferTypeOf[environment_, context_, term_] := Replace[term, {
	boundVariable[index_] :> kernelFailure["LooseBoundVariable", "A bound variable with index `1` occurs outside its binder.", {index}],
	freeVariable[id_] :> Lookup[context, id, kernelFailure["UnknownVariable", "The free variable `1` is not in the local context.", {id}]]["Type"],
	metavariable[id_] :> Lookup[$metavariableTypes, id, kernelFailure["Metavariable", "The term contains an unsolved metavariable.", {}]],
	universeSort[level_] :> (
		If[ ! rulesSetting[environment, "Prop"] && FreeQ[level, _levelMetavariable] && ! levelNeverZeroQ[level], noPropFailure[environment, level]];
		universeSort[normalizeLevel[levelSuccessor[level, 1]]]
	),
	constantReference[name_, levels_List] :> constantType[environment, name, levels],
	naturalLiteral[_Integer?NonNegative] :> naturalNumberType[environment],
	(* a primitive of cubical type theory with rules of its own types its arguments together *)
	application[_, _] :> Replace[cubicalSpineType[environment, context, term], None :> spineType[environment, context, term]],
	lambdaAbstraction[name_, domain_, body_, binder_] :> lambdaType[environment, context, name, domain, body, binder],
	dependentFunctionType[name_, domain_, codomain_, binder_] :> functionTypeSort[environment, context, name, domain, codomain, binder],
	localDefinition[name_, type_, value_, body_] :> localDefinitionType[environment, context, name, type, value, body],
	projection[structure_, index_Integer?NonNegative, structureTerm_] :> projectionType[environment, context, structure, index, structureTerm],
	_cubicalSystem :> kernelFailure["SystemTerm", "A system has no type of its own: it is only the side of a composition or a Glue type.", {}],
	_intervalUniverse :> kernelFailure["IntervalUniverseTerm", "The sort of the interval has no type.", {}],
	_ :> kernelFailure["IllFormedTerm", "`1` is not a term.", {term}]
}]

cubicalSpineType[environment_, context_, term_] := If[ ! cubicalDeclaredQ[environment],
	None,
	Replace[applicationSpine[term], {
		{constantReference[name_, levels_List], arguments_List} /; cubicalRole[environment, name] =!= None :>
			cubicalApplicationType[environment, context, constantRecord[environment, name], levels, arguments],
		_ -> None
	}]
]

constantType[environment_, name_, levels_List] := constantTypeOf[environment, name, levels, constantRecord[environment, name]]

constantTypeOf[environment_, name_, levels_, record_] := (
	Which[
		record["Kind"] === "RewriteRule",
			kernelFailure["RewriteRuleTerm", "`1` is a rewrite rule, not a term.", {HoldForm @@ name}],
		Length[levels] =!= Length[record["UniverseParameters"]],
			kernelFailure["UniverseArity", "`1` takes `2` universe levels, not `3`.", {HoldForm @@ name, Length[record["UniverseParameters"]], Length[levels]}],
		record["Kind"] === "Cubical",
			cubicalConstantType[environment, record, instantiateUniverseParameters[record["Type"], record["UniverseParameters"], levels]],
		True,
			instantiateUniverseParameters[record["Type"], record["UniverseParameters"], levels]
	]
)

noPropFailure[_, 0] := kernelFailure["NoProp", "TypeUniverse[0] is Prop, which the rules of this environment do not have.", {}]
noPropFailure[environment_, level_] := kernelFailure[
	"NoProp",
	"`1` would be Prop for some universe parameters, which the rules of this environment do not have; a level such as u + 1 is never 0.",
	{displayCoreTerm[environment, <||>, universeSort[level]]}
]

naturalNumberType[environment_] := Replace[naturalNumberSettings[environment], {
	settings_Association :> constantReference[settings["Type"], {}],
	_ :> kernelFailure["NoNaturalNumbers", "A natural number literal needs an environment with natural numbers registered.", {}]
}]

(* An application's arguments are checked in one pass along its spine, as Lean's kernel infers a spine: each argument
   against its binder's domain, instantiated with the arguments before it, and the codomain instantiated with all of
   them once at the end. Taking one argument at a time instead, each argument instantiated the whole rest of the
   function's type, so a spine of n arguments cost n substitutions of its telescope. In infer-only mode the arguments
   are not checked, and only the codomain is instantiated. *)
spineType[environment_, context_, term_] := spineTypeOf[environment, context, applicationSpine[term]]

spineTypeOf[environment_, context_, {head_, arguments_}] := spineTypeFrom[environment, context, head, inferType[environment, context, head], {}, arguments]

(* prefix: the head applied to the arguments taken so far; type: the head's type under the binders passed since the
   last reduction, whose bound variables stand for the pending arguments, innermost last *)
spineTypeFrom[environment_, context_, prefix_, type_, pending_List, {}] := instantiateBoundVariables[type, pending]
spineTypeFrom[environment_, context_, prefix_, dependentFunctionType[_, domain_, codomain_, _], pending_List, {argument_, rest___}] := (
	If[! $inferOnly, checkHasType[environment, context, argument, instantiateBoundVariables[domain, pending]]];
	spineTypeFrom[environment, context, application[prefix, argument], codomain, Append[pending, argument], {rest}]
)
(* a type that is not a function type as it stands may reduce to one *)
spineTypeFrom[environment_, context_, prefix_, type_, pending_List, arguments : {argument_, rest___}] := Replace[
	weakHeadNormalForm[environment, context, instantiateBoundVariables[type, pending]],
	{
		functionType_dependentFunctionType :> spineTypeFrom[environment, context, prefix, functionType, {}, arguments],
		functionType_ :> Replace[pathApplicationType[environment, context, functionType, argument], {
			None :> kernelFailure[
				"FunctionExpected",
				"`1` is applied to an argument, but its type `2` is not a function type.",
				{displayCoreTerm[environment, context, prefix], displayCoreTerm[environment, context, functionType]}
			],
			pathType_ :> spineTypeFrom[environment, context, application[prefix, argument], pathType, {}, {rest}]
		}]
	}
]

(* Inside a declaration's check both sides of the comparison are checked: the term's type is inferred from the term,
   checked just now, and the expected type is the caller's: a binder's domain in a checked function type, with checked
   arguments put in (spineTypeFrom), a local definition's type, checked just before (localDefinitionType), or the
   declaration's type, checked before its value (Declarations.wl). *)
checkHasType[environment_, context_, term_, expected_] := checkInferredType[environment, context, term, inferType[environment, context, term], expected]

checkInferredType[environment_, context_, term_, actual_, expected_] := (
	If[ ! definitionallyEqualQ[environment, context, actual, expected] && ! cubicalFitQ[environment, context, term, actual, expected],
		kernelFailure[
			"TypeMismatch",
			"`1` has type `2`, but the expected type is `3`.",
			{displayCoreTerm[environment, context, term], displayCoreTerm[environment, context, actual], displayCoreTerm[environment, context, expected]}
		]
	]
)

(* a function of the interval of cubical type theory is a path between its values at the endpoints *)
lambdaType[environment_, context_, name_, domain_, body_, binder_] := Block[{lambdaId = freshFreeVariable[], lambdaContext, lambdaBodyType},
	checkBinderQuantity[environment, name, binder];
	If[! $inferOnly, checkIntervalDomain[environment, context, domain]];
	lambdaContext = extendContext[context, lambdaId, name, domain, binder];
	lambdaBodyType = inferType[environment, lambdaContext, instantiateBoundVariable[body, freeVariable[lambdaId]]];
	Replace[intervalLambdaType[environment, lambdaContext, lambdaId, name, domain, body, lambdaBodyType], None :>
		Construct[dependentFunctionType, name, domain, abstractFreeVariable[lambdaBodyType, lambdaId], binder]
	]
]

(* a function type of the interval is a pretype, as the interval is: it has the sort of the interval, which
   is no universe, so no variable may have it *)
functionTypeSort[environment_, context_, name_, domain_, codomain_, binder_] /; cubicalDeclaredQ[environment] && intervalTypeQ[environment, domain] := (
	checkBinderQuantity[environment, name, binder];
	intervalUniverse[]
)
functionTypeSort[environment_, context_, name_, domain_, codomain_, binder_] := Block[{functionTypeId = freshFreeVariable[]},
	checkBinderQuantity[environment, name, binder];
	universeSort[normalizeLevel[levelImpredicativeMaximum[
		sortLevel[environment, context, domain],
		sortLevel[environment, extendContext[context, functionTypeId, name, domain, binder], instantiateBoundVariable[codomain, freeVariable[functionTypeId]]]
	]]]
]

(* The body is inferred with the variable in the context, its value beside it for computation to unfold,
   as in Lean's kernel: putting the value in the body would infer its type again at every use. *)
localDefinitionType[environment_, context_, name_, type_, value_, body_] := (
	If[ ! $inferOnly,
		sortLevel[environment, context, type];
		checkHasType[environment, context, value, type]
	];
	With[{id = freshFreeVariable[]},
		instantiateBoundVariable[
			abstractFreeVariable[inferType[environment, extendLocalDefinition[context, id, name, type, value], instantiateBoundVariable[body, freeVariable[id]]], id],
			value
		]
	]
)

extendLocalDefinition[context_Association, id_Integer, name_, type_, value_] := Append[context, id -> <|"Name" -> name, "Type" -> type, "Binder" -> "Explicit", "Value" -> value|>]

sortLevel[environment_, context_, type_] := Replace[
	weakHeadNormalForm[environment, context, inferType[environment, context, type]],
	{
		universeSort[level_] :> level,
		other_ :> kernelFailure[
			"TypeExpected",
			"`1` is not a type: its type is `2`.",
			{displayCoreTerm[environment, context, type], displayCoreTerm[environment, context, other]}
		]
	}
]


(* ::Subsection:: *)
(*Projections*)


structureLikeQ[environment_, name_HoldComplete] := And[
	constantDeclaredQ[environment, name],
	MatchQ[
		constantRecord[environment, name],
		KeyValuePattern[{"Kind" -> "InductiveType", "Constructors" -> {_}, "NumberOfIndices" -> 0, "Recursive" -> False}]
	]
]

(* The type of field index of a term of a structure: the constructor's type with the structure's
   parameters and the earlier fields, as projections of the term, filled in. A proof of a proposition
   only yields proofs, nor a proof whose type depends on a field that is data: projecting data out of a
   proof would contradict proof irrelevance. These are the rules of Lean 4's kernel. *)
projectionType[environment_, context_, structure_, index_, structureTerm_] := Block[
	{projectedType, projectedHead, projectedParameters, projectedRecord, projectedFieldsType, projectedFieldType, projectedFromProofQ},
	projectedType = weakHeadNormalForm[environment, context, inferType[environment, context, structureTerm]];
	{projectedHead, projectedParameters} = applicationSpine[projectedType];
	If[ ! MatchQ[projectedHead, constantReference[structure, _]] || ! structureLikeQ[environment, structure],
		kernelFailure["ProjectionType", "The type of `1` is not the structure `2`.", {displayCoreTerm[environment, context, structureTerm], HoldForm @@ structure}]
	];
	projectedRecord = constantRecord[environment, structure];
	projectedFieldsType = Fold[
		Function[{type, value}, instantiateLeadingBinder[environment, context, type, value]],
		instantiateUniverseParameters[constantRecord[environment, First[projectedRecord["Constructors"]]]["Type"], projectedRecord["UniverseParameters"], Last[projectedHead]],
		projectedParameters
	];
	projectedFromProofQ = levelEquivalentQ[sortLevel[environment, context, projectedType], 0];
	projectedFieldType = Fold[
		Function[{type, earlier}, instantiateEarlierField[environment, context, structure, structureTerm, projectedFromProofQ, type, earlier]],
		projectedFieldsType,
		Range[0, index - 1]
	];
	Replace[weakHeadNormalForm[environment, context, projectedFieldType], {
		dependentFunctionType[_, domain_, _, _] :> (
			If[ projectedFromProofQ && ! levelEquivalentQ[sortLevel[environment, context, domain], 0],
				projectionFromProofFailure[environment, context, structureTerm]
			];
			domain
		),
		_ :> kernelFailure["ProjectionIndex", "The structure `1` has no field `2`.", {HoldForm @@ structure, index + 1}]
	}]
]

instantiateEarlierField[environment_, context_, structure_, structureTerm_, propositionQ_, type_, earlier_Integer] := Replace[
	weakHeadNormalForm[environment, context, type],
	{
		dependentFunctionType[_, domain_, codomain_, _] /; boundVariableOccursQ[codomain, 0] :> (
			If[ propositionQ && ! levelEquivalentQ[sortLevel[environment, context, domain], 0],
				projectionFromProofFailure[environment, context, structureTerm]
			];
			instantiateBoundVariable[codomain, projection[structure, earlier, structureTerm]]
		),
		dependentFunctionType[_, _, codomain_, _] :> instantiateBoundVariable[codomain, projection[structure, earlier, structureTerm]],
		other_ :> kernelFailure["FunctionExpected", "`1` is not a function type.", {displayCoreTerm[environment, context, other]}]
	}
]

projectionFromProofFailure[environment_, context_, structureTerm_] :=
	kernelFailure["ProjectionFromProof", "`1` is a proof, so only proofs that do not depend on data can be projected out of it.", {displayCoreTerm[environment, context, structureTerm]}]

instantiateLeadingBinder[environment_, context_, type_, value_] := Replace[weakHeadNormalForm[environment, context, type], {
	dependentFunctionType[_, _, codomain_, _] :> instantiateBoundVariable[codomain, value],
	other_ :> kernelFailure["FunctionExpected", "`1` is not a function type.", {displayCoreTerm[environment, context, other]}]
}]


(* ::Subsection:: *)
(*Reduction*)


weakHeadNormalForm[environment_, context_, term_] := If[ AssociationQ[$weakHeadNormalFormCache],
	Lookup[$weakHeadNormalFormCache, Key[{environment, term}], $weakHeadNormalFormCache[{environment, term}] = reducedHead[environment, context, term]],
	reducedHead[environment, context, term]
]

reducedHead[environment_, context_, term_] := Block[{$unfoldDefinitions = True}, FixedPoint[Function[current, reduceHead[environment, context, current]], term]]

(* reduced as far as it reduces without unfolding a definition, as Lean's whnf_core: an equation is
   compared at this point before its definitions unfold, by proof irrelevance and then by the arguments of
   one definition at both heads, as two applications of the same constant often are equal by their
   arguments, and unfolding first can mean a long computation, as Nat.sub on a variable and a large
   literal is *)
reducedHeadWithoutUnfolding[environment_, context_, term_] := Block[{$unfoldDefinitions = False}, FixedPoint[Function[current, reduceHead[environment, context, current]], term]]

$unfoldDefinitions = True

(* A step of reduction passes its values on in calls. W15 renames the variables of a scoping construct nested in
   another, a With in a With or a rule in a With, by walking the inner body, and a term put there by the outer
   pattern is walked as the tree it writes out to: a term that shares its subterms many times over, as a sum of
   integers does, costs each step twice the step before. *)
reduceHead[environment_, context_, term_] := reduceSpineOf[environment, context, term, applicationSpine[term]]

reduceSpineOf[environment_, context_, term_, {head_, arguments_}] := endpointOrReduced[environment, context, term, head, arguments, reduceSpine[environment, context, term, head, arguments]]

(* in cubical type theory, a path that is stuck at an endpoint is that endpoint of its type *)
endpointOrReduced[environment_, context_, term_, head_, arguments_, reduced_] := If[ reduced === term && arguments =!= {} && cubicalDeclaredQ[environment],
	reducePathEndpoint[environment, context, term, head, arguments],
	reduced
]

(* a function of several variables applied to arguments for them takes them all in one substitution, as in
   Lean's kernel, not one substitution each *)
reduceSpine[_, _, _, function_lambdaAbstraction, arguments : {__}] := betaReduced[peelFunctions[function, Length[arguments]], arguments]
reduceSpine[_, _, _, localDefinition[_, _, value_, body_], arguments_List] := makeApplication[instantiateBoundVariable[body, value], arguments]
reduceSpine[_, _, _, metavariable[id_] /; KeyExistsQ[$metavariableAssignments, id], arguments_List] :=
	makeApplication[$metavariableAssignments[id], arguments]
reduceSpine[environment_, context_, term_, constantReference[name_, levels_List], arguments_List] :=
	reduceConstant[environment, context, term, name, levels, arguments]
reduceSpine[environment_, context_, term_, projection[structure_, index_, structureTerm_], arguments_List] :=
	reduceProjection[environment, context, term, structure, index, structureTerm, arguments]
reduceSpine[_, context_, _, freeVariable[id_], arguments_List] /; KeyExistsQ[Lookup[context, id, <||>], "Value"] := makeApplication[context[id]["Value"], arguments]
reduceSpine[_, _, term_, _, _] := term

betaReduced[{body_, count_}, arguments_] := makeApplication[instantiateBoundVariables[body, Take[arguments, count]], Drop[arguments, count]]

(* {body, count}: the body under the outermost functions nested in term, count of them and at most limit *)
peelFunctions[term_, limit_Integer] := NestWhile[
	Function[state, {state[[1, 3]], state[[2]] + 1}],
	{term, 0},
	Function[state, state[[2]] < limit && MatchQ[First[state], _lambdaAbstraction]]
]

(* a registered operation on natural numbers computes on literals before it unfolds *)
reduceConstant[environment_, context_, term_, name_, levels_, arguments_] := constantReduct[environment, context, term, name, levels, arguments, literalOperationResult[environment, context, name, arguments]]

constantReduct[environment_, context_, term_, name_, levels_, arguments_, None] := reduceByKind[environment, context, term, name, levels, arguments, constantRecord[environment, name]]
constantReduct[_, _, _, _, _, _, result_] := result

reduceByKind[environment_, context_, term_, name_, levels_, arguments_, record_] := Which[
	record["Kind"] === "Definition" && $unfoldDefinitions,
		unfoldDefinition[record, levels, arguments],
	record["Kind"] === "Definition",
		term,
	record["Kind"] === "Recursor",
		reduceRecursor[environment, context, term, record, levels, arguments],
	record["Kind"] === "Axiom",
		rewriteAxiom[environment, context, term, name, levels, arguments],
	record["Kind"] === "Quotient",
		reduceQuotient[environment, context, term, record, arguments],
	record["Kind"] === "Cubical",
		reduceCubical[environment, context, term, record, levels, arguments],
	True,
		term
]

(* An axiom applied to arguments that match the left side of one of its rewrite rules gives the right
   side: a variable of the rule takes the argument at its place, a part without variables must equal the
   argument there, and a constant applied to patterns must be the argument's head after reduction. The
   first rule that matches is taken. The comparisons are of the arguments of the term reduced, and of
   closed parts of a rule, checked with the rule. *)
rewriteAxiom[environment_, context_, term_, name_, levels_, arguments_] :=
	firstRewrite[environment, context, term, levels, arguments, rewriteRuleRecords[environment, name]]

firstRewrite[_, _, term_, _, _, {}] := term
firstRewrite[environment_, context_, term_, levels_, arguments_, {record_, rest___}] := Replace[
	matchRewriteRule[environment, context, record, levels, arguments],
	None :> firstRewrite[environment, context, term, levels, arguments, {rest}]
]

matchRewriteRule[environment_, context_, record_, levels_, arguments_] := Module[
	{numberOfVariables = record["NumberOfVariables"], patternHead, patterns, levelValues, substitution},
	{patternHead, patterns} = applicationSpine[ruleBody[record["LeftHandSide"], numberOfVariables]];
	levelValues = matchLevels[Last[patternHead], levels, record["UniverseParameters"]];
	substitution = If[ Length[arguments] < Length[patterns] || levelValues === None,
		None,
		Fold[
			Function[{accumulated, pair}, If[ accumulated === None,
				None,
				matchPattern[environment, context, numberOfVariables, record["UniverseParameters"], levelValues, First[pair], Last[pair], accumulated]
			]],
			<||>,
			Transpose[{patterns, Take[arguments, Length[patterns]]}]
		]
	];
	If[ substitution === None,
		None,
		makeApplication[
			instantiateUniverseParameters[record["RightHandSide"], record["UniverseParameters"], levelValues],
			Join[Function[index, substitution[index]] /@ Range[numberOfVariables - 1, 0, -1], Drop[arguments, Length[patterns]]]
		]
	]
]

ruleBody[term_, 0] := term
ruleBody[lambdaAbstraction[_, _, body_, _], n_Integer?Positive] := ruleBody[body, n - 1]

(* the rule's universe parameters are levels of its head, so the head's levels give them all *)
matchLevels[patternLevels_List, levels_List, universeParameters_List] := With[
	{bound = Association @ Cases[Transpose[{patternLevels, levels}], {levelParameter[parameter_], level_} :> (parameter -> level)]},
	If[ Length[patternLevels] == Length[levels] && AllTrue[
			Transpose[{patternLevels, levels}],
			Function[pair, levelEquivalentQ[ReplaceAll[First[pair], levelParameter[parameter_] /; KeyExistsQ[bound, parameter] :> bound[parameter]], Last[pair]]]
		],
		Lookup[bound, universeParameters],
		None
	]
]

matchPattern[environment_, context_, numberOfVariables_, universeParameters_, levelValues_, pattern_, argument_, substitution_] := Which[
	MatchQ[pattern, boundVariable[_]],
		With[{index = First[pattern]},
			Which[
				! KeyExistsQ[substitution, index], Append[substitution, index -> argument],
				definitionallyEqualQ[environment, context, substitution[index], argument], substitution,
				True, None
			]
		],
	NoneTrue[Range[0, numberOfVariables - 1], Function[index, boundVariableOccursQ[pattern, index]]],
		If[ definitionallyEqualQ[environment, context, instantiateUniverseParameters[pattern, universeParameters, levelValues], argument], substitution, None],
	True,
		With[{patternSpine = applicationSpine[pattern], argumentSpine = applicationSpine[weakHeadNormalForm[environment, context, argument]]},
			If[ And[
					Length[Last[patternSpine]] == Length[Last[argumentSpine]],
					headsEqualQ[environment, context, instantiateUniverseParameters[First[patternSpine], universeParameters, levelValues], First[argumentSpine]]
				],
				Fold[
					Function[{accumulated, pair}, If[ accumulated === None,
						None,
						matchPattern[environment, context, numberOfVariables, universeParameters, levelValues, First[pair], Last[pair], accumulated]
					]],
					substitution,
					Transpose[{Last[patternSpine], Last[argumentSpine]}]
				],
				None
			]
		]
]

unfoldDefinition[record_, levels_, arguments_] :=
	makeApplication[instantiateUniverseParameters[record["Value"], record["UniverseParameters"], levels], arguments]

(* a projection of the constructor applied to its parameters and fields is that field *)
reduceProjection[environment_, context_, term_, structure_, index_, structureTerm_, arguments_List] :=
	projectedField[environment, term, index, arguments, constantRecord[environment, structure], applicationSpine[weakHeadNormalForm[environment, context, structureTerm]]]

projectedField[environment_, term_, index_, arguments_, record_, spine_] := Replace[spine, {
	{constantReference[constructor_, _], constructorArguments_List} /; And[
		record["Constructors"] === {constructor},
		Length[constructorArguments] == record["NumberOfParameters"] + constantRecord[environment, constructor]["NumberOfFields"]
	] :> makeApplication[First @ Drop[constructorArguments, record["NumberOfParameters"] + index], arguments],
	_ :> term
}]

toConstructorForm[environment_, naturalLiteral[n_Integer]] := Replace[naturalNumberSettings[environment], {
	settings_Association /; n == 0 :> constantReference[settings["Zero"], {}],
	settings_Association :> Construct[application, constantReference[settings["Successor"], {}], naturalLiteral[n - 1]],
	_ :> naturalLiteral[n]
}]
toConstructorForm[_, term_] := term


(* A recursor applied to all its arguments up to the major premise: parameters, motives, one for each type
   of its block, minor premises, indices, major premise, then any further arguments. *)
reduceRecursor[environment_, context_, term_, record_, levels_, arguments_] :=
	reduceRecursorOf[environment, context, term, record, levels, arguments, Lookup[record, {"NumberOfParameters", "NumberOfMotives", "NumberOfMinors", "NumberOfIndices"}]]

reduceRecursorOf[environment_, context_, term_, record_, levels_, arguments_, counts_List] := If[ Length[arguments] < Total[counts] + 1,
	term,
	reduceRecursorApplication[environment, context, term, record, levels, TakeList[arguments, Join[counts, {1, All}]]]
]

(* the constructor's own parameters come before its fields: those of the block, or of the nested type
   whose recursor this is *)
reduceRecursorApplication[environment_, context_, term_, record_, levels_, {parameters_, motives_, minors_, indices_, {major_}, rest_}] := recursorReduct[
	environment, context, term, record, levels, parameters, motives, minors, major, rest,
	applicationSpine[toConstructorForm[environment, weakHeadNormalForm[environment, context, major]]]
]

recursorReduct[_, _, _, record_, levels_, parameters_, motives_, minors_, _, rest_, {constantReference[constructor_, _], constructorArguments_}] /;
	constructorApplicationQ[record, constructor, constructorArguments] :=
	applyRecursorRule[record, levels, parameters, motives, minors, constructor, Drop[constructorArguments, record["Rules"][constructor]["NumberOfParameters"]], rest]
recursorReduct[environment_, context_, term_, record_, levels_, parameters_, motives_, minors_, major_, rest_, _] /; TrueQ[record["KLike"]] :=
	reduceKLike[environment, context, term, record, levels, parameters, motives, minors, major, rest]
recursorReduct[environment_, context_, term_, record_, levels_, parameters_, motives_, minors_, major_, rest_, _] :=
	structureReduct[term, record, levels, parameters, motives, minors, rest, structureFields[environment, context, record, major]]

structureReduct[_, record_, levels_, parameters_, motives_, minors_, rest_, fields_List] := applyRecursorRule[record, levels, parameters, motives, minors, First[Keys[record["Rules"]]], fields, rest]
structureReduct[term_, _, _, _, _, _, _, None] := term

(* Eta for structures, as Lean's kernel reduces a recursor: a major premise of a structure type that is
   not a constructor application is the constructor applied to its projections, so a match on a pair p
   computes with p.1 and p.2. A proposition is left alone, since data cannot be projected out of a proof. *)
structureFields[environment_, context_, record_, major_] := If[ ! structureLikeQ[environment, record["InductiveType"]],
	None,
	projectionsOf[environment, context, record, record["InductiveType"], major, weakHeadNormalForm[environment, context, typeQuery[environment, context, major]]]
]

projectionsOf[environment_, context_, record_, name_, major_, majorType_] := If[ ! MatchQ[First[applicationSpine[majorType]], constantReference[name, _]] || propositionTypeQ[environment, context, majorType],
	None,
	Table[Construct[projection, name, index, major], {index, 0, record["Rules"][First[Keys[record["Rules"]]]]["NumberOfFields"] - 1}]
]

propositionTypeQ[environment_, context_, type_] := MatchQ[weakHeadNormalForm[environment, context, typeQuery[environment, context, type]], universeSort[level_] /; levelEquivalentQ[level, 0]]

constructorApplicationQ[record_, constructor_, constructorArguments_] := And[
	KeyExistsQ[record["Rules"], constructor],
	Length[constructorArguments] == record["Rules"][constructor]["NumberOfParameters"] + record["Rules"][constructor]["NumberOfFields"]
]

applyRecursorRule[record_, levels_, parameters_, motives_List, minors_, constructor_, fields_, rest_] := makeApplication[
	instantiateUniverseParameters[record["Rules"][constructor]["RightHandSide"], record["UniverseParameters"], levels],
	Join[parameters, motives, minors, fields, rest]
]

(* K-like: the inductive is a proposition with one constructor and no fields, so its recursor reduces
   on any major premise whose type matches the constructor's, not only on the constructor itself. The
   types compared are those of the major premise and of the constructor applied to the parameters, all
   arguments of the recursor application reduced. *)
reduceKLike[environment_, context_, term_, record_, levels_, parameters_, motives_, minors_, major_, rest_] := reduceKLikeAt[
	environment, context, term, record, levels, parameters, motives, minors, major, rest,
	First[Keys[record["Rules"]]],
	makeApplication[constantReference[First[Keys[record["Rules"]]], If[TrueQ[record["EliminationUniverse"]], Rest[levels], levels]], parameters]
]

reduceKLikeAt[environment_, context_, term_, record_, levels_, parameters_, motives_, minors_, major_, rest_, constructor_, constructorApplication_] := If[
	definitionallyEqualQ[environment, context, typeQuery[environment, context, major], typeQuery[environment, context, constructorApplication]],
	applyRecursorRule[record, levels, parameters, motives, minors, constructor, {}, rest],
	term
]


(* ::Subsection:: *)
(*Definitional equality*)


(* Every comparison below is of the two terms first compared, their arguments, their binders' domains and bodies
   opened with a fresh variable, their reducts, or the types of these: checked terms or reducts of checked terms
   when the first two are, so the type queries may infer only (typeQuery). *)
definitionallyEqualQ[environment_, context_, a_, b_] := a === b || If[ AssociationQ[$definitionalEqualityCache],
	Lookup[$definitionalEqualityCache, Key[{environment, a, b}], $definitionalEqualityCache[{environment, a, b}] = definitionallyEqualCases[environment, context, a, b]],
	definitionallyEqualCases[environment, context, a, b]
]

definitionallyEqualCases[_, _, universeSort[first_], universeSort[second_]] := levelEquivalentQ[first, second]
(* two literals are equal if their numbers are, which comparing them as successors would find only after
   one step for each *)
definitionallyEqualCases[_, _, naturalLiteral[first_], naturalLiteral[second_]] := first == second
(* two function types are equal only if their binders have the same quantity, the binders' kinds aside *)
definitionallyEqualCases[environment_, context_, (head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_], head_[_, otherDomain_, otherBody_, otherBinder_]] :=
	And[
		head === lambdaAbstraction || binderQuantity[binder] === binderQuantity[otherBinder],
		definitionallyEqualQ[environment, context, domain, otherDomain],
		With[{id = freshFreeVariable[]},
			definitionallyEqualQ[
				environment,
				extendContext[context, id, name, domain, binder],
				instantiateBoundVariable[body, freeVariable[id]],
				instantiateBoundVariable[otherBody, freeVariable[id]]
			]
		]
	]
definitionallyEqualCases[environment_, context_, first_cubicalSystem, second_cubicalSystem] := systemsEqualQ[environment, context, first, second]
definitionallyEqualCases[_, _, _cubicalSystem, _] := False
definitionallyEqualCases[_, _, _, _cubicalSystem] := False
definitionallyEqualCases[_, _, _intervalUniverse, _] := False
definitionallyEqualCases[_, _, _, _intervalUniverse] := False
(* two elements of the interval are equal by their normal forms *)
definitionallyEqualCases[environment_, context_, a_, b_] := Or[
	cubicalDeclaredQ[environment] && intervalEqualQ[environment, context, a, b],
	reducedEqualQ[environment, context, a, b]
]

(* Lean's order: each side reduced as far as it reduces without unfolding a definition, then, where neither
   reduces, proof irrelevance, which decides two proofs by their propositions, then lazy delta. Proof
   irrelevance is asked once for the two sides as they reduce no further, never of the sides on the way. *)
reducedEqualQ[environment_, context_, a_, b_] := coresEqualQ[environment, context, a, b, reducedHeadWithoutUnfolding[environment, context, a], reducedHeadWithoutUnfolding[environment, context, b]]

coresEqualQ[environment_, context_, a_, b_, coreA_, coreB_] := If[ coreA =!= a || coreB =!= b,
	definitionallyEqualQ[environment, context, coreA, coreB],
	Replace[proofIrrelevance[environment, context, a, b], None :> lazyDeltaEqualQ[environment, context, a, b]]
]

(* one definition applied to equal arguments at both heads, tried before unfolding it *)
sameHeadArgumentsEqualQ[environment_, context_, a_, b_] := sameHeadSpinesEqualQ[environment, context, applicationSpine[a], applicationSpine[b]]

sameHeadSpinesEqualQ[environment_, context_, {headA_, argumentsA_}, {headB_, argumentsB_}] := And[
	MatchQ[headA, _constantReference],
	argumentsA =!= {},
	Length[argumentsA] == Length[argumentsB],
	headsEqualQ[environment, context, headA, headB],
	argumentsEqualQ[environment, context, argumentsA, argumentsB]
]

(* Lean's lazy delta reduction. Where neither side reduces further without unfolding a definition, the
   side whose definition at its head is higher, defined in terms of the other's, unfolds one step, or
   both do at the same height, until the sides are the same or neither has a definition at its head: an
   application of a definition defined by another meets an application of that other before either
   unfolds into what may be a long computation. As in Lean's kernel the steps are a loop, and between
   them the sides are compared only by identity, and by their arguments where one definition is at both
   heads, from the first pair on; unfolding leaves a proof a proof of the same proposition, so proof
   irrelevance, asked of the first pair, is not asked again. The last pair is compared in full, or by
   its weak head normal forms where nothing unfolded. *)
lazyDeltaEqualQ[environment_, context_, a_, b_] := Block[{lazyDeltaPair = {a, b}, lazyDeltaNext},
	lazyDeltaNext = lazyDeltaStep[environment, context, a, b];
	While[ ListQ[lazyDeltaNext] && lazyDeltaNext[[1]] =!= lazyDeltaNext[[2]],
		lazyDeltaPair = lazyDeltaNext;
		lazyDeltaNext = lazyDeltaStep[environment, context, lazyDeltaPair[[1]], lazyDeltaPair[[2]]]
	];
	Which[
		lazyDeltaNext =!= None,
			True,
		lazyDeltaPair === {a, b},
			normalFormsEqualQ[environment, context, a, b],
		True,
			definitionallyEqualQ[environment, context, lazyDeltaPair[[1]], lazyDeltaPair[[2]]]
	]
]

(* The next pair, True for one definition at both heads applied to equal arguments, or None where
   neither side has a definition at its head. As Lean's compare of hints, an abbreviation, as a projection
   function is, unfolds before a regular definition, and two abbreviations unfold together without their
   arguments compared: x.toRingHom against a long composition reads the field before the composition
   unfolds. Of two regular definitions the higher unfolds first, or both at one height. *)
lazyDeltaStep[environment_, context_, a_, b_] := lazyDeltaStepOf[environment, context, a, b, headDefinition[environment, a], headDefinition[environment, b]]

lazyDeltaStepOf[environment_, context_, a_, b_, definitionA_, definitionB_] := (
	Which[
		definitionA === None && definitionB === None,
			None,
		definitionB === None,
			{unfoldedHead[environment, context, a], b},
		definitionA === None,
			{a, unfoldedHead[environment, context, b]},
		Last[definitionA] && Last[definitionB],
			{unfoldedHead[environment, context, a], unfoldedHead[environment, context, b]},
		Last[definitionA],
			{unfoldedHead[environment, context, a], b},
		Last[definitionB],
			{a, unfoldedHead[environment, context, b]},
		First[definitionA] > First[definitionB],
			{unfoldedHead[environment, context, a], b},
		First[definitionA] < First[definitionB],
			{a, unfoldedHead[environment, context, b]},
		sameHeadArgumentsEqualQ[environment, context, a, b],
			True,
		True,
			{unfoldedHead[environment, context, a], unfoldedHead[environment, context, b]}
	]
)

(* {height, abbreviation} of the definition at the head of term, or None if no definition that unfolds is at its head *)
headDefinition[environment_, term_] := Replace[First[applicationSpine[term]], {
	constantReference[name_, _] :> With[{record = constantRecord[environment, name]},
		If[record["Kind"] === "Definition", {Lookup[record, "Height", 0], Lookup[record, "Hint", None] === "Abbreviation"}, None]
	],
	_ -> None
}]

(* a projection function: a value that takes arguments and projects a field out of the last, as Lean's structure
   projections do, which Lean gives abbreviation hints *)
projectionFunctionQ[value_] := MatchQ[value, _lambdaAbstraction] &&
	MatchQ[NestWhile[Function[term, term[[3]]], value, MatchQ[#, _lambdaAbstraction]&], projection[_, _, boundVariable[0]]]

(* the definition at the head of term unfolded, and reduced as far as it reduces without unfolding another *)
unfoldedHead[environment_, context_, term_] := Replace[applicationSpine[term], {
	{constantReference[name_, levels_], arguments_List} :>
		reducedHeadWithoutUnfolding[environment, context, unfoldDefinition[constantRecord[environment, name], levels, arguments]]
}]

normalFormsEqualQ[environment_, context_, a_, b_] := Which[
	MatchQ[a, _lambdaAbstraction],
		etaEqualQ[environment, context, a, b],
	MatchQ[b, _lambdaAbstraction],
		etaEqualQ[environment, context, b, a],
	MatchQ[a, _naturalLiteral] || MatchQ[b, _naturalLiteral],
		literalEqualQ[environment, context, a, b],
	True,
		spinesEqualQ[environment, context, a, b] || structureEtaQ[environment, context, a, b] || structureEtaQ[environment, context, b, a] || unitEqualQ[environment, context, a, b]
]

(* eta for structures: S.mk[params, fields] equals t of the same type when each field equals that projection of t *)
structureEtaQ[environment_, context_, constructorApplication_, other_] := structureEtaSpineQ[environment, context, constructorApplication, other, applicationSpine[constructorApplication]]

structureEtaSpineQ[environment_, context_, constructorApplication_, other_, {constantReference[constructor_, _], arguments_}] /; structureConstructorQ[environment, constructor, Length[arguments]] :=
	structureFieldsEqualQ[
		environment,
		context,
		constructorApplication,
		other,
		constantRecord[environment, constructor]["InductiveType"],
		Drop[arguments, constantRecord[environment, constructor]["NumberOfParameters"]]
	]
structureEtaSpineQ[_, _, _, _, _] := False

structureFieldsEqualQ[environment_, context_, constructorApplication_, other_, structure_, fields_] := And[
	definitionallyEqualQ[environment, context, typeQuery[environment, context, constructorApplication], typeQuery[environment, context, other]],
	AllTrue[
		Transpose[{Range[0, Length[fields] - 1], fields}],
		Function[pair, definitionallyEqualQ[environment, context, Last[pair], Construct[projection, structure, First[pair], other]]]
	]
]

structureConstructorQ[environment_, constructor_, numberOfArguments_Integer] := structureConstructorRecordQ[environment, constantRecord[environment, constructor], numberOfArguments]

structureConstructorRecordQ[environment_, record_, numberOfArguments_] := And[
	record["Kind"] === "Constructor",
	structureLikeQ[environment, record["InductiveType"]],
	numberOfArguments == record["NumberOfParameters"] + record["NumberOfFields"]
]

(* any two terms of a structure with no fields are equal, unless it is a proposition, where proof irrelevance
   decides; a type is never one, nor is a path type, whose line inferring its type would open again *)
unitEqualQ[_, _, _universeSort | _dependentFunctionType | _intervalUniverse, _] := False
unitEqualQ[environment_, context_, a_, _] /; cubicalDeclaredQ[environment] && pathTypeArguments[environment, a] =!= None := False
unitEqualQ[environment_, context_, a_, b_] := unitTypeEqualQ[environment, context, b, weakHeadNormalForm[environment, context, typeQuery[environment, context, a]]]

unitTypeEqualQ[environment_, context_, b_, type_] := Replace[First @ applicationSpine[type], {
	constantReference[structure_, _] /; structureLikeQ[environment, structure] && unitStructureQ[environment, structure] :>
		definitionallyEqualQ[environment, context, type, typeQuery[environment, context, b]],
	_ :> False
}]

unitStructureQ[environment_, structure_] := constantRecord[environment, First[constantRecord[environment, structure]["Constructors"]]]["NumberOfFields"] === 0

etaEqualQ[environment_, context_, function : lambdaAbstraction[name_, domain_, body_, binder_], other_] := etaEqualAtQ[environment, context, function, other, freshFreeVariable[]]

etaEqualAtQ[environment_, context_, lambdaAbstraction[name_, domain_, body_, binder_], other_, id_] := definitionallyEqualQ[
	environment,
	extendContext[context, id, name, domain, binder],
	instantiateBoundVariable[body, freeVariable[id]],
	application[other, freeVariable[id]]
]

literalEqualQ[environment_, context_, a_, b_] := constructorFormsEqualQ[environment, context, a, b, toConstructorForm[environment, a], toConstructorForm[environment, b]]

constructorFormsEqualQ[environment_, context_, a_, b_, formA_, formB_] := (formA =!= a || formB =!= b) && definitionallyEqualQ[environment, context, formA, formB]

spinesEqualQ[environment_, context_, a_, b_] := spinePairEqualQ[environment, context, applicationSpine[a], applicationSpine[b]]

spinePairEqualQ[environment_, context_, {headA_, argumentsA_}, {headB_, argumentsB_}] := And[
	Length[argumentsA] == Length[argumentsB],
	headsEqualQ[environment, context, headA, headB],
	argumentsEqualQ[environment, context, argumentsA, argumentsB]
]

argumentsEqualQ[environment_, context_, arguments_List, otherArguments_List] :=
	AllTrue[Transpose[{arguments, otherArguments}], Function[pair, definitionallyEqualQ[environment, context, First[pair], Last[pair]]]]

headsEqualQ[_, _, constantReference[name_, levels_List], constantReference[name_, otherLevels_List]] :=
	Length[levels] == Length[otherLevels] && AllTrue[Transpose[{levels, otherLevels}], Apply[levelEquivalentQ]]
headsEqualQ[_, _, freeVariable[id_], freeVariable[id_]] := True
headsEqualQ[_, _, metavariable[id_], metavariable[id_]] := True
headsEqualQ[environment_, context_, projection[structure_, index_, first_], projection[structure_, index_, second_]] :=
	definitionallyEqualQ[environment, context, first, second]
headsEqualQ[_, _, _, _] := False

(* As Lean's is_def_eq_proof_irrel: True for proofs of one proposition, False for proofs of two, since equal terms
   have equal types, and None where the first term is no proof, as no type and no literal is *)
proofIrrelevance[_, _, _universeSort | _dependentFunctionType | _naturalLiteral, _] := None
proofIrrelevance[environment_, _, _, _] /; ! rulesSetting[environment, "Prop"] := None
proofIrrelevance[environment_, context_, a_, b_] := proofIrrelevanceOf[environment, context, b, typeQuery[environment, context, a]]

proofIrrelevanceOf[environment_, context_, b_, typeA_] := If[ propositionQ[environment, context, typeA],
	definitionallyEqualQ[environment, context, typeA, typeQuery[environment, context, b]],
	None
]

propositionQ[environment_, context_, type_] := MatchQ[weakHeadNormalForm[environment, context, typeQuery[environment, context, type]], universeSort[0]]
