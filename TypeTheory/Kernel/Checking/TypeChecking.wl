(* ::Package:: *)

(*
Type inference, weak head normalization and definitional equality: the trusted kernel.

Every function takes the environment and a local context, an Association

	<|id -> <|"Name" -> HoldComplete[name], "Type" -> type, "Binder" -> binder|>, ...|>

giving the type of each freeVariable[id]. Going under a binder replaces its bound variable with a
fresh free variable, so the kernel never manipulates loose bound variables.

inferType always checks: an application checks its argument against the domain, a binder checks that
its domain is a type. Reduction implements beta, zeta (local definitions), delta (unfolding
definitions; theorems are never unfolded), iota (a recursor applied to a constructor, natural literals
read as constructors, and K-like recursors such as that of Equal), and addition of natural literals
on Wolfram Language integers when the environment registers an addition, and the rewrite rules of an
axiom where the environment's rules allow them. Definitional equality adds eta for functions and proof
irrelevance: two proofs of the same proposition are equal.

Under rules without Prop, every universe level must be at least 1 whatever its universe parameters are,
so no type is a proposition, and proof irrelevance and K-like reduction never apply.

Metavariables only appear while elaborating; their types and assignments are read from
$metavariableTypes and $metavariableAssignments, which the elaborator binds.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[inferType]
PackageScoped[weakHeadNormalForm]
PackageScoped[definitionallyEqualQ]
PackageScoped[sortLevel]
PackageScoped[checkHasType]
PackageScoped[freshFreeVariable]
PackageScoped[extendContext]
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
definitionallyEqualQ::usage = "definitionallyEqualQ[environment, context, a, b] gives True if a and b are equal by computation, eta and proof irrelevance."
sortLevel::usage = "sortLevel[environment, context, type] gives the level of the sort type belongs to, or throws a kernel failure if type is not a type."
checkHasType::usage = "checkHasType[environment, context, term, type] throws a kernel failure unless term has a type definitionally equal to type."
freshFreeVariable::usage = "freshFreeVariable[] gives an identifier no free variable has used."
extendContext::usage = "extendContext[context, id, HoldComplete[name], type, binder] gives context with freeVariable[id] of type type."
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

freshFreeVariable[] := ++$freeVariableCounter

extendContext[context_Association, id_Integer, name_, type_, binder_String] := Append[context, id -> <|"Name" -> name, "Type" -> type, "Binder" -> binder|>]

makeLambda[context_Association, ids_List, body_] := Fold[
	Function[{accumulated, id}, With[{entry = context[id]}, lambdaAbstraction[entry["Name"], entry["Type"], abstractFreeVariable[accumulated, id], entry["Binder"]]]],
	body,
	Reverse[ids]
]

makeDependentFunctionType[context_Association, ids_List, body_] := Fold[
	Function[{accumulated, id}, With[{entry = context[id]}, dependentFunctionType[entry["Name"], entry["Type"], abstractFreeVariable[accumulated, id], entry["Binder"]]]],
	body,
	Reverse[ids]
]


(* ::Subsection:: *)
(*Type inference*)


inferType[environment_, context_, term_] := Replace[term, {
	boundVariable[index_] :> kernelFailure["LooseBoundVariable", "A bound variable with index `1` occurs outside its binder.", {index}],
	freeVariable[id_] :> Lookup[context, id, kernelFailure["UnknownVariable", "The free variable `1` is not in the local context.", {id}]]["Type"],
	metavariable[id_] :> Lookup[$metavariableTypes, id, kernelFailure["Metavariable", "The term contains an unsolved metavariable.", {}]],
	universeSort[level_] :> (
		If[ ! rulesSetting[environment, "Prop"] && FreeQ[level, _levelMetavariable] && ! levelNeverZeroQ[level], noPropFailure[environment, level]];
		universeSort[normalizeLevel[levelSuccessor[level, 1]]]
	),
	constantReference[name_, levels_List] :> constantType[environment, name, levels],
	naturalLiteral[_Integer?NonNegative] :> naturalNumberType[environment],
	application[function_, argument_] :> applicationType[environment, context, function, argument],
	lambdaAbstraction[name_, domain_, body_, binder_] :> lambdaType[environment, context, name, domain, body, binder],
	dependentFunctionType[name_, domain_, codomain_, binder_] :> functionTypeSort[environment, context, name, domain, codomain, binder],
	localDefinition[name_, type_, value_, body_] :> localDefinitionType[environment, context, type, value, body],
	projection[structure_, index_Integer?NonNegative, structureTerm_] :> projectionType[environment, context, structure, index, structureTerm],
	_ :> kernelFailure["IllFormedTerm", "`1` is not a term.", {term}]
}]

constantType[environment_, name_, levels_List] := With[{record = constantRecord[environment, name]},
	Which[
		record["Kind"] === "RewriteRule",
			kernelFailure["RewriteRuleTerm", "`1` is a rewrite rule, not a term.", {HoldForm @@ name}],
		Length[levels] =!= Length[record["UniverseParameters"]],
			kernelFailure["UniverseArity", "`1` takes `2` universe levels, not `3`.", {HoldForm @@ name, Length[record["UniverseParameters"]], Length[levels]}],
		True,
			instantiateUniverseParameters[record["Type"], record["UniverseParameters"], levels]
	]
]

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

applicationType[environment_, context_, function_, argument_] := Replace[
	weakHeadNormalForm[environment, context, inferType[environment, context, function]],
	{
		dependentFunctionType[_, domain_, codomain_, _] :> (
			checkHasType[environment, context, argument, domain];
			instantiateBoundVariable[codomain, argument]
		),
		functionType_ :> kernelFailure[
			"FunctionExpected",
			"`1` is applied to an argument, but its type `2` is not a function type.",
			{displayCoreTerm[environment, context, function], displayCoreTerm[environment, context, functionType]}
		]
	}
]

checkHasType[environment_, context_, term_, expected_] := With[{actual = inferType[environment, context, term]},
	If[ ! definitionallyEqualQ[environment, context, actual, expected],
		kernelFailure[
			"TypeMismatch",
			"`1` has type `2`, but the expected type is `3`.",
			{displayCoreTerm[environment, context, term], displayCoreTerm[environment, context, actual], displayCoreTerm[environment, context, expected]}
		]
	]
]

lambdaType[environment_, context_, name_, domain_, body_, binder_] := With[{id = freshFreeVariable[]},
	sortLevel[environment, context, domain];
	dependentFunctionType[
		name,
		domain,
		abstractFreeVariable[inferType[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[body, freeVariable[id]]], id],
		binder
	]
]

functionTypeSort[environment_, context_, name_, domain_, codomain_, binder_] := With[{id = freshFreeVariable[]},
	universeSort[normalizeLevel[levelImpredicativeMaximum[
		sortLevel[environment, context, domain],
		sortLevel[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[codomain, freeVariable[id]]]
	]]]
]

localDefinitionType[environment_, context_, type_, value_, body_] := (
	sortLevel[environment, context, type];
	checkHasType[environment, context, value, type];
	inferType[environment, context, instantiateBoundVariable[body, value]]
)

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
projectionType[environment_, context_, structure_, index_, structureTerm_] := Module[
	{structureType, head, parameters, record, fieldsType, fieldType, propositionQ},
	structureType = weakHeadNormalForm[environment, context, inferType[environment, context, structureTerm]];
	{head, parameters} = applicationSpine[structureType];
	If[ ! MatchQ[head, constantReference[structure, _]] || ! structureLikeQ[environment, structure],
		kernelFailure["ProjectionType", "The type of `1` is not the structure `2`.", {displayCoreTerm[environment, context, structureTerm], HoldForm @@ structure}]
	];
	record = constantRecord[environment, structure];
	fieldsType = Fold[
		Function[{type, value}, instantiateLeadingBinder[environment, context, type, value]],
		instantiateUniverseParameters[constantRecord[environment, First[record["Constructors"]]]["Type"], record["UniverseParameters"], Last[head]],
		parameters
	];
	propositionQ = levelEquivalentQ[sortLevel[environment, context, structureType], 0];
	fieldType = Fold[
		Function[{type, earlier}, instantiateEarlierField[environment, context, structure, structureTerm, propositionQ, type, earlier]],
		fieldsType,
		Range[0, index - 1]
	];
	Replace[weakHeadNormalForm[environment, context, fieldType], {
		dependentFunctionType[_, domain_, _, _] :> (
			If[ propositionQ && ! levelEquivalentQ[sortLevel[environment, context, domain], 0],
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


weakHeadNormalForm[environment_, context_, term_] := FixedPoint[Function[current, reduceHead[environment, context, current]], term]

reduceHead[environment_, context_, term_] := With[{spine = applicationSpine[term]},
	reduceSpine[environment, context, term, First[spine], Last[spine]]
]

reduceSpine[_, _, _, lambdaAbstraction[_, _, body_, _], {argument_, rest___}] := makeApplication[instantiateBoundVariable[body, argument], {rest}]
reduceSpine[_, _, _, localDefinition[_, _, value_, body_], arguments_List] := makeApplication[instantiateBoundVariable[body, value], arguments]
reduceSpine[_, _, _, metavariable[id_] /; KeyExistsQ[$metavariableAssignments, id], arguments_List] :=
	makeApplication[$metavariableAssignments[id], arguments]
reduceSpine[environment_, context_, term_, constantReference[name_, levels_List], arguments_List] :=
	reduceConstant[environment, context, term, name, levels, arguments]
reduceSpine[environment_, context_, term_, projection[structure_, index_, structureTerm_], arguments_List] :=
	reduceProjection[environment, context, term, structure, index, structureTerm, arguments]
reduceSpine[_, _, term_, _, _] := term

(* a registered operation on natural numbers computes on literals before it unfolds *)
reduceConstant[environment_, context_, term_, name_, levels_, arguments_] := Replace[
	literalOperationResult[environment, context, name, arguments],
	None :> With[{record = constantRecord[environment, name]},
		Which[
			record["Kind"] === "Definition",
				unfoldDefinition[record, levels, arguments],
			record["Kind"] === "Recursor",
				reduceRecursor[environment, context, term, record, levels, arguments],
			record["Kind"] === "Axiom",
				rewriteAxiom[environment, context, term, name, levels, arguments],
			True,
				term
		]
	]
]

(* An axiom applied to arguments that match the left side of one of its rewrite rules gives the right
   side: a variable of the rule takes the argument at its place, a part without variables must equal the
   argument there, and a constant applied to patterns must be the argument's head after reduction. The
   first rule that matches is taken. *)
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
	If[ Length[arguments] < Length[patterns] || levelValues === None,
		Return[None, Module]
	];
	substitution = Fold[
		Function[{accumulated, pair}, If[ accumulated === None,
			None,
			matchPattern[environment, context, numberOfVariables, record["UniverseParameters"], levelValues, First[pair], Last[pair], accumulated]
		]],
		<||>,
		Transpose[{patterns, Take[arguments, Length[patterns]]}]
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
reduceProjection[environment_, context_, term_, structure_, index_, structureTerm_, arguments_List] := With[
	{record = constantRecord[environment, structure]},
	Replace[applicationSpine[weakHeadNormalForm[environment, context, structureTerm]], {
		{constantReference[constructor_, _], constructorArguments_List} /; And[
			record["Constructors"] === {constructor},
			Length[constructorArguments] == record["NumberOfParameters"] + constantRecord[environment, constructor]["NumberOfFields"]
		] :> makeApplication[First @ Drop[constructorArguments, record["NumberOfParameters"] + index], arguments],
		_ :> term
	}]
]

toConstructorForm[environment_, naturalLiteral[n_Integer]] := Replace[naturalNumberSettings[environment], {
	settings_Association /; n == 0 :> constantReference[settings["Zero"], {}],
	settings_Association :> application[constantReference[settings["Successor"], {}], naturalLiteral[n - 1]],
	_ :> naturalLiteral[n]
}]
toConstructorForm[_, term_] := term


(* A recursor applied to all its arguments up to the major premise: parameters, motives, one for each type
   of its block, minor premises, indices, major premise, then any further arguments. *)
reduceRecursor[environment_, context_, term_, record_, levels_, arguments_] := With[
	{
		numberOfParameters = record["NumberOfParameters"],
		numberOfMotives = record["NumberOfMotives"],
		numberOfMinors = record["NumberOfMinors"],
		numberOfIndices = record["NumberOfIndices"]
	},
	If[ Length[arguments] < numberOfParameters + numberOfMotives + numberOfMinors + numberOfIndices + 1,
		term,
		reduceRecursorApplication[
			environment,
			context,
			term,
			record,
			levels,
			TakeList[arguments, {numberOfParameters, numberOfMotives, numberOfMinors, numberOfIndices, 1, All}]
		]
	]
]

(* the constructor's own parameters come before its fields: those of the block, or of the nested type
   whose recursor this is *)
reduceRecursorApplication[environment_, context_, term_, record_, levels_, {parameters_, motives_, minors_, indices_, {major_}, rest_}] := Replace[
	applicationSpine[toConstructorForm[environment, weakHeadNormalForm[environment, context, major]]],
	{
		{constantReference[constructor_, _], constructorArguments_} /; constructorApplicationQ[record, constructor, constructorArguments] :>
			applyRecursorRule[record, levels, parameters, motives, minors, constructor, Drop[constructorArguments, record["Rules"][constructor]["NumberOfParameters"]], rest],
		_ /; TrueQ[record["KLike"]] :>
			reduceKLike[environment, context, term, record, levels, parameters, motives, minors, major, rest],
		_ :> Replace[structureFields[environment, context, record, major], {
			fields_List :> applyRecursorRule[record, levels, parameters, motives, minors, First[Keys[record["Rules"]]], fields, rest],
			None :> term
		}]
	}
]

(* Eta for structures, as Lean's kernel reduces a recursor: a major premise of a structure type that is
   not a constructor application is the constructor applied to its projections, so a match on a pair p
   computes with p.1 and p.2. A proposition is left alone, since data cannot be projected out of a proof. *)
structureFields[environment_, context_, record_, major_] := With[{name = record["InductiveType"]},
	If[ ! structureLikeQ[environment, name],
		None,
		With[{majorType = weakHeadNormalForm[environment, context, inferType[environment, context, major]]},
			If[ ! MatchQ[First[applicationSpine[majorType]], constantReference[name, _]] || propositionTypeQ[environment, context, majorType],
				None,
				Table[projection[name, index, major], {index, 0, record["Rules"][First[Keys[record["Rules"]]]]["NumberOfFields"] - 1}]
			]
		]
	]
]

propositionTypeQ[environment_, context_, type_] := MatchQ[weakHeadNormalForm[environment, context, inferType[environment, context, type]], universeSort[level_] /; levelEquivalentQ[level, 0]]

constructorApplicationQ[record_, constructor_, constructorArguments_] := And[
	KeyExistsQ[record["Rules"], constructor],
	Length[constructorArguments] == record["Rules"][constructor]["NumberOfParameters"] + record["Rules"][constructor]["NumberOfFields"]
]

applyRecursorRule[record_, levels_, parameters_, motives_List, minors_, constructor_, fields_, rest_] := makeApplication[
	instantiateUniverseParameters[record["Rules"][constructor]["RightHandSide"], record["UniverseParameters"], levels],
	Join[parameters, motives, minors, fields, rest]
]

(* K-like: the inductive is a proposition with one constructor and no fields, so its recursor reduces
   on any major premise whose type matches the constructor's, not only on the constructor itself. *)
reduceKLike[environment_, context_, term_, record_, levels_, parameters_, motives_, minors_, major_, rest_] := With[
	{
		constructor = First[Keys[record["Rules"]]],
		inductiveLevels = If[TrueQ[record["EliminationUniverse"]], Rest[levels], levels]
	},
	With[{constructorApplication = makeApplication[constantReference[constructor, inductiveLevels], parameters]},
		If[ definitionallyEqualQ[environment, context, inferType[environment, context, major], inferType[environment, context, constructorApplication]],
			applyRecursorRule[record, levels, parameters, motives, minors, constructor, {}, rest],
			term
		]
	]
]


(* ::Subsection:: *)
(*Definitional equality*)


definitionallyEqualQ[environment_, context_, a_, b_] := a === b || definitionallyEqualCases[environment, context, a, b]

definitionallyEqualCases[_, _, universeSort[first_], universeSort[second_]] := levelEquivalentQ[first, second]
definitionallyEqualCases[environment_, context_, (head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_], head_[_, otherDomain_, otherBody_, _]] :=
	And[
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
definitionallyEqualCases[environment_, context_, a_, b_] := Or[
	sameHeadArgumentsEqualQ[environment, context, a, b],
	reducedEqualQ[environment, context, a, b],
	proofIrrelevantEqualQ[environment, context, a, b]
]

(* the same constant applied to equal arguments, tried before unfolding the constant *)
sameHeadArgumentsEqualQ[environment_, context_, a_, b_] := With[{spineA = applicationSpine[a], spineB = applicationSpine[b]},
	And[
		MatchQ[First[spineA], _constantReference],
		Last[spineA] =!= {},
		Length[Last[spineA]] == Length[Last[spineB]],
		headsEqualQ[environment, context, First[spineA], First[spineB]],
		argumentsEqualQ[environment, context, Last[spineA], Last[spineB]]
	]
]

reducedEqualQ[environment_, context_, a_, b_] := With[
	{reducedA = weakHeadNormalForm[environment, context, a], reducedB = weakHeadNormalForm[environment, context, b]},
	If[ reducedA =!= a || reducedB =!= b,
		definitionallyEqualQ[environment, context, reducedA, reducedB],
		normalFormsEqualQ[environment, context, a, b]
	]
]

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
structureEtaQ[environment_, context_, constructorApplication_, other_] := With[{spine = applicationSpine[constructorApplication]},
	Replace[First[spine], {
		constantReference[constructor_, _] /; structureConstructorQ[environment, constructor, Length[Last[spine]]] :> With[
			{
				structure = constantRecord[environment, constructor]["InductiveType"],
				fields = Drop[Last[spine], constantRecord[environment, constructor]["NumberOfParameters"]]
			},
			And[
				definitionallyEqualQ[environment, context, inferType[environment, context, constructorApplication], inferType[environment, context, other]],
				AllTrue[
					Transpose[{Range[0, Length[fields] - 1], fields}],
					Function[pair, definitionallyEqualQ[environment, context, Last[pair], projection[structure, First[pair], other]]]
				]
			]
		],
		_ :> False
	}]
]

structureConstructorQ[environment_, constructor_, numberOfArguments_Integer] := With[{record = constantRecord[environment, constructor]},
	And[
		record["Kind"] === "Constructor",
		structureLikeQ[environment, record["InductiveType"]],
		numberOfArguments == record["NumberOfParameters"] + record["NumberOfFields"]
	]
]

(* any two terms of a structure with no fields are equal, unless it is a proposition, where proof irrelevance decides *)
unitEqualQ[environment_, context_, a_, b_] := With[{type = weakHeadNormalForm[environment, context, inferType[environment, context, a]]},
	Replace[First @ applicationSpine[type], {
		constantReference[structure_, _] /; structureLikeQ[environment, structure] && unitStructureQ[environment, structure] :>
			definitionallyEqualQ[environment, context, type, inferType[environment, context, b]],
		_ :> False
	}]
]

unitStructureQ[environment_, structure_] := constantRecord[environment, First[constantRecord[environment, structure]["Constructors"]]]["NumberOfFields"] === 0

etaEqualQ[environment_, context_, lambdaAbstraction[name_, domain_, body_, binder_], other_] := With[{id = freshFreeVariable[]},
	definitionallyEqualQ[
		environment,
		extendContext[context, id, name, domain, binder],
		instantiateBoundVariable[body, freeVariable[id]],
		application[other, freeVariable[id]]
	]
]

literalEqualQ[environment_, context_, a_, b_] := With[{formA = toConstructorForm[environment, a], formB = toConstructorForm[environment, b]},
	(formA =!= a || formB =!= b) && definitionallyEqualQ[environment, context, formA, formB]
]

spinesEqualQ[environment_, context_, a_, b_] := With[{spineA = applicationSpine[a], spineB = applicationSpine[b]},
	And[
		Length[Last[spineA]] == Length[Last[spineB]],
		headsEqualQ[environment, context, First[spineA], First[spineB]],
		argumentsEqualQ[environment, context, Last[spineA], Last[spineB]]
	]
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

proofIrrelevantEqualQ[environment_, context_, a_, b_] := With[{typeA = inferType[environment, context, a]},
	And[
		propositionQ[environment, context, typeA],
		definitionallyEqualQ[environment, context, typeA, inferType[environment, context, b]]
	]
]

propositionQ[environment_, context_, type_] := MatchQ[weakHeadNormalForm[environment, context, inferType[environment, context, type]], universeSort[0]]
