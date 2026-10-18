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
on Wolfram Language integers when the environment registers an addition. Definitional equality adds
eta for functions and proof irrelevance: two proofs of the same proposition are equal.

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
	universeSort[level_] :> universeSort[normalizeLevel[levelSuccessor[level, 1]]],
	constantReference[name_, levels_List] :> constantType[environment, name, levels],
	naturalLiteral[_Integer?NonNegative] :> naturalNumberType[environment],
	application[function_, argument_] :> applicationType[environment, context, function, argument],
	lambdaAbstraction[name_, domain_, body_, binder_] :> lambdaType[environment, context, name, domain, body, binder],
	dependentFunctionType[name_, domain_, codomain_, binder_] :> functionTypeSort[environment, context, name, domain, codomain, binder],
	localDefinition[name_, type_, value_, body_] :> localDefinitionType[environment, context, type, value, body],
	_ :> kernelFailure["IllFormedTerm", "`1` is not a term.", {term}]
}]

constantType[environment_, name_, levels_List] := With[{record = constantRecord[environment, name]},
	If[ Length[levels] =!= Length[record["UniverseParameters"]],
		kernelFailure["UniverseArity", "`1` takes `2` universe levels, not `3`.", {HoldForm @@ name, Length[record["UniverseParameters"]], Length[levels]}],
		instantiateUniverseParameters[record["Type"], record["UniverseParameters"], levels]
	]
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
reduceSpine[_, _, term_, _, _] := term

reduceConstant[environment_, context_, term_, name_, levels_, arguments_] := With[{record = constantRecord[environment, name]},
	Which[
		additionQ[environment, name] && Length[arguments] == 2,
			reduceAddition[environment, context, record, levels, arguments],
		record["Kind"] === "Definition",
			unfoldDefinition[record, levels, arguments],
		record["Kind"] === "Recursor",
			reduceRecursor[environment, context, term, record, levels, arguments],
		True,
			term
	]
]

unfoldDefinition[record_, levels_, arguments_] :=
	makeApplication[instantiateUniverseParameters[record["Value"], record["UniverseParameters"], levels], arguments]

additionQ[environment_, name_] := MatchQ[naturalNumberSettings[environment], KeyValuePattern["Addition" -> name]]

(* The trusted literal extension: the sum of two literals is computed, not unfolded. It agrees with
   the registered addition, which the prelude defines by recursion on its second argument. *)
reduceAddition[environment_, context_, record_, levels_, {first_, second_}] := Replace[
	{weakHeadNormalForm[environment, context, first], weakHeadNormalForm[environment, context, second]},
	{
		{naturalLiteral[m_], naturalLiteral[n_]} :> naturalLiteral[m + n],
		_ :> unfoldDefinition[record, levels, {first, second}]
	}
]

toConstructorForm[environment_, naturalLiteral[n_Integer]] := Replace[naturalNumberSettings[environment], {
	settings_Association /; n == 0 :> constantReference[settings["Zero"], {}],
	settings_Association :> application[constantReference[settings["Successor"], {}], naturalLiteral[n - 1]],
	_ :> naturalLiteral[n]
}]
toConstructorForm[_, term_] := term


(* A recursor applied to all its arguments up to the major premise: parameters, motive, minor premises,
   indices, major premise, then any further arguments. *)
reduceRecursor[environment_, context_, term_, record_, levels_, arguments_] := With[
	{
		numberOfParameters = record["NumberOfParameters"],
		numberOfMinors = record["NumberOfMinors"],
		numberOfIndices = record["NumberOfIndices"]
	},
	If[ Length[arguments] < numberOfParameters + numberOfMinors + numberOfIndices + 2,
		term,
		reduceRecursorApplication[
			environment,
			context,
			term,
			record,
			levels,
			TakeList[arguments, {numberOfParameters, 1, numberOfMinors, numberOfIndices, 1, All}]
		]
	]
]

reduceRecursorApplication[environment_, context_, term_, record_, levels_, {parameters_, {motive_}, minors_, indices_, {major_}, rest_}] := Replace[
	applicationSpine[toConstructorForm[environment, weakHeadNormalForm[environment, context, major]]],
	{
		{constantReference[constructor_, _], constructorArguments_} /; constructorApplicationQ[record, constructor, constructorArguments] :>
			applyRecursorRule[record, levels, parameters, motive, minors, constructor, Drop[constructorArguments, record["NumberOfParameters"]], rest],
		_ /; TrueQ[record["KLike"]] :>
			reduceKLike[environment, context, term, record, levels, parameters, motive, minors, major, rest],
		_ :> term
	}
]

constructorApplicationQ[record_, constructor_, constructorArguments_] := And[
	KeyExistsQ[record["Rules"], constructor],
	Length[constructorArguments] == record["NumberOfParameters"] + record["Rules"][constructor]["NumberOfFields"]
]

applyRecursorRule[record_, levels_, parameters_, motive_, minors_, constructor_, fields_, rest_] := makeApplication[
	instantiateUniverseParameters[record["Rules"][constructor]["RightHandSide"], record["UniverseParameters"], levels],
	Join[parameters, {motive}, minors, fields, rest]
]

(* K-like: the inductive is a proposition with one constructor and no fields, so its recursor reduces
   on any major premise whose type matches the constructor's, not only on the constructor itself. *)
reduceKLike[environment_, context_, term_, record_, levels_, parameters_, motive_, minors_, major_, rest_] := With[
	{
		constructor = First[Keys[record["Rules"]]],
		inductiveLevels = If[TrueQ[record["EliminationUniverse"]], Rest[levels], levels]
	},
	With[{constructorApplication = makeApplication[constantReference[constructor, inductiveLevels], parameters]},
		If[ definitionallyEqualQ[environment, context, inferType[environment, context, major], inferType[environment, context, constructorApplication]],
			applyRecursorRule[record, levels, parameters, motive, minors, constructor, {}, rest],
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
		spinesEqualQ[environment, context, a, b]
]

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
headsEqualQ[_, _, _, _] := False

proofIrrelevantEqualQ[environment_, context_, a_, b_] := With[{typeA = inferType[environment, context, a]},
	And[
		propositionQ[environment, context, typeA],
		definitionallyEqualQ[environment, context, typeA, inferType[environment, context, b]]
	]
]

propositionQ[environment_, context_, type_] := MatchQ[weakHeadNormalForm[environment, context, inferType[environment, context, type]], universeSort[0]]
