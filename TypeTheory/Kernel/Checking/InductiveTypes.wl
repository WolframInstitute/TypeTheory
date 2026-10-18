(* ::Package:: *)

(*
Declaring an inductive family: checking it and generating its recursor.

An inductive type I : (parameters) -> (indices) -> Sort level has constructors, each of type
(parameters) -> (fields) -> I parameters indices'. The checks are those of Lean 4's kernel for a single
family without nesting:

	- the type of I, and of each constructor, is a type;
	- each constructor takes exactly I's parameters first and ends in I applied to those parameters;
	- I occurs strictly positively: in a field's type only as the result, I parameters indices, after
	  binders that do not mention I;
	- unless I is a proposition, each field lives in a universe no larger than I's.

The recursor InductiveRecursor[I] eliminates into any Sort u (large elimination) unless I may be a
proposition and has more than one constructor or a field that is neither a proof nor an index of the
constructor's result; then it eliminates only into Prop. Its arguments are the parameters (implicit),
the motive, one minor premise per constructor, the indices (implicit) and the major premise. Each
constructor gets a reduction rule. A proposition with one constructor and no fields, such as Equal, is
K-like: its recursor reduces on any major premise of the right type.

Everything is built with fresh free variables and abstracted at the end, which keeps de Bruijn indices
out of the construction. The generated recursor type and rules are type-checked before they are added.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[declareInductiveType]
PackageScoped[typeTelescope]
PackageScoped[recursorName]


(* ::Section:: *)
(*Usage Messages*)


declareInductiveType::usage = "declareInductiveType[environment, HoldComplete[name], {HoldComplete[u], ...}, numberOfParameters, type, \
{HoldComplete[constructor] -> constructorType, ...}] checks the inductive family name and gives environment with it, its constructors and its \
recursor added; it throws a kernel failure if a check fails."
typeTelescope::usage = "typeTelescope[environment, context, type] opens the leading function types of type with fresh free variables and gives {extendedContext, {id, ...}, remainingType}."
recursorName::usage = "recursorName[HoldComplete[name]] gives HoldComplete[InductiveRecursor[name]]."


(* ::Section:: *)
(*Function Definitions*)


typeTelescope[environment_, context_, type_] := telescopeFrom[environment, context, {}, weakHeadNormalForm[environment, context, type]]

telescopeFrom[environment_, context_, ids_List, dependentFunctionType[name_, domain_, codomain_, binder_]] := With[{id = freshFreeVariable[]},
	With[{extended = extendContext[context, id, name, domain, binder]},
		telescopeFrom[environment, extended, Append[ids, id], weakHeadNormalForm[environment, extended, instantiateBoundVariable[codomain, freeVariable[id]]]]
	]
]
telescopeFrom[_, context_, ids_List, rest_] := {context, ids, rest}


recursorName[HoldComplete[name_]] := HoldComplete[InductiveRecursor[name]]

occursQ[term_, name_] := ! FreeQ[term, constantReference[name, _]]


declareInductiveType[environment_, name_HoldComplete, universeParameters_List, numberOfParameters_Integer, type_, constructors_List] := Module[
	{typeContext, binderIds, resultType, resultLevel, parameterIds, indexIds, inductiveConstant, provisional, checkedConstructors},
	checkUniverseParameters[name, universeParameters, Prepend[Last /@ constructors, type]];
	If[ ! DuplicateFreeQ[Join[{name, recursorName[name]}, First /@ constructors]],
		kernelFailure["DuplicateConstructor", "The constructors of `1` must have distinct names, different from the type and its recursor.", {HoldForm @@ name}]
	];
	sortLevel[environment, <||>, type];
	{typeContext, binderIds, resultType} = typeTelescope[environment, <||>, type];
	resultLevel = Replace[resultType, {
		universeSort[level_] :> level,
		_ :> kernelFailure["InductiveTypeSort", "The type of an inductive type must end in a sort.", {}]
	}];
	If[ Length[binderIds] < numberOfParameters,
		kernelFailure["InductiveParameters", "The type of `1` has fewer than `2` binders for its parameters.", {HoldForm @@ name, numberOfParameters}]
	];
	{parameterIds, indexIds} = TakeDrop[binderIds, numberOfParameters];
	inductiveConstant = constantReference[name, levelParameter /@ universeParameters];
	provisional = addConstantRecords[environment, <|name -> <|
		"Kind" -> "InductiveType",
		"Type" -> type,
		"UniverseParameters" -> universeParameters,
		"NumberOfParameters" -> numberOfParameters,
		"NumberOfIndices" -> Length[indexIds],
		"Constructors" -> {},
		"LargeElimination" -> False,
		"Recursive" -> False
	|>|>];
	checkedConstructors = Function[constructor,
		checkConstructor[provisional, typeContext, name, inductiveConstant, parameterIds, Length[indexIds], resultLevel, constructor]
	] /@ constructors;
	addInductiveRecords[environment, name, universeParameters, type, typeContext, parameterIds, indexIds, resultLevel, inductiveConstant, checkedConstructors]
]


(* ::Subsection:: *)
(*Constructors*)


checkConstructor[environment_, typeContext_, name_, inductiveConstant_, parameterIds_, numberOfIndices_, resultLevel_, constructorName_ -> constructorType_] := Module[
	{afterParameters, fieldContext, fieldIds, conclusion, conclusionHead, conclusionArguments, conclusionIndices, recursiveFields},
	sortLevel[environment, <||>, constructorType];
	afterParameters = Fold[
		Function[{remaining, parameterId}, instantiateConstructorParameter[environment, typeContext, constructorName, remaining, parameterId]],
		constructorType,
		parameterIds
	];
	{fieldContext, fieldIds, conclusion} = typeTelescope[environment, typeContext, afterParameters];
	{conclusionHead, conclusionArguments} = applicationSpine[conclusion];
	If[ conclusionHead =!= inductiveConstant || Length[conclusionArguments] =!= Length[parameterIds] + numberOfIndices,
		kernelFailure["ConstructorResult", "The constructor `1` must end in `2` applied to its parameters and indices.", {HoldForm @@ constructorName, HoldForm @@ name}]
	];
	If[ Take[conclusionArguments, Length[parameterIds]] =!= (freeVariable /@ parameterIds),
		kernelFailure["ConstructorParameters", "The constructor `1` must end in `2` applied to the same parameters.", {HoldForm @@ constructorName, HoldForm @@ name}]
	];
	conclusionIndices = Drop[conclusionArguments, Length[parameterIds]];
	If[ occursQ[conclusionIndices, name],
		kernelFailure["NonPositiveOccurrence", "`1` occurs in an index of the result of the constructor `2`.", {HoldForm @@ name, HoldForm @@ constructorName}]
	];
	recursiveFields = Flatten[
		Function[fieldId, recursiveFieldData[environment, fieldContext, name, inductiveConstant, parameterIds, constructorName, fieldId]] /@ fieldIds
	];
	checkFieldUniverses[environment, fieldContext, fieldIds, resultLevel, constructorName];
	<|
		"Name" -> constructorName,
		"Type" -> constructorType,
		"FieldIds" -> fieldIds,
		"FieldContext" -> fieldContext,
		"ConclusionIndices" -> conclusionIndices,
		"RecursiveFields" -> recursiveFields
	|>
]

(* a constructor's leading binders are the inductive's parameters: their types must agree *)
instantiateConstructorParameter[environment_, typeContext_, constructorName_, remaining_, parameterId_] := Replace[
	weakHeadNormalForm[environment, typeContext, remaining],
	{
		dependentFunctionType[_, domain_, codomain_, _] /; definitionallyEqualQ[environment, typeContext, domain, typeContext[parameterId]["Type"]] :>
			instantiateBoundVariable[codomain, freeVariable[parameterId]],
		_ :> kernelFailure["ConstructorParameters", "The constructor `1` must take the parameters of its type first.", {HoldForm @@ constructorName}]
	}
]

(* A field is recursive when its type is (ys) -> I parameters indices with I absent from the ys and the
   indices; it is non-recursive when I does not occur at all; anything else is not strictly positive. *)
recursiveFieldData[environment_, fieldContext_, name_, inductiveConstant_, parameterIds_, constructorName_, fieldId_] := Module[
	{fieldType = fieldContext[fieldId]["Type"], innerContext, binderIds, result, resultHead, resultArguments},
	If[ ! occursQ[fieldType, name],
		{},
		{innerContext, binderIds, result} = typeTelescope[environment, fieldContext, fieldType];
		{resultHead, resultArguments} = applicationSpine[result];
		If[ Or[
				AnyTrue[binderIds, Function[id, occursQ[innerContext[id]["Type"], name]]],
				resultHead =!= inductiveConstant,
				Take[resultArguments, UpTo[Length[parameterIds]]] =!= (freeVariable /@ parameterIds),
				occursQ[Drop[resultArguments, Length[parameterIds]], name]
			],
			kernelFailure["NonPositiveOccurrence", "`1` does not occur strictly positively in the constructor `2`.", {HoldForm @@ name, HoldForm @@ constructorName}],
			{<|"Id" -> fieldId, "Binders" -> binderIds, "Context" -> innerContext, "Indices" -> Drop[resultArguments, Length[parameterIds]]|>}
		]
	]
]

checkFieldUniverses[environment_, fieldContext_, fieldIds_, resultLevel_, constructorName_] := If[ ! levelEquivalentQ[resultLevel, 0],
	Scan[
		Function[fieldId, With[{fieldLevel = sortLevel[environment, fieldContext, fieldContext[fieldId]["Type"]]},
			If[ ! levelLessEqualQ[fieldLevel, resultLevel],
				kernelFailure["UniverseTooLarge", "A field of the constructor `1` lives in a larger universe than its type.", {HoldForm @@ constructorName}]
			]
		]],
		fieldIds
	]
]


(* ::Subsection:: *)
(*Recursor*)


largeEliminationQ[environment_, resultLevel_, checkedConstructors_List] := Which[
	levelNeverZeroQ[resultLevel],
		True,
	Length[checkedConstructors] == 0,
		True,
	Length[checkedConstructors] == 1,
		With[{constructor = First[checkedConstructors]},
			AllTrue[constructor["FieldIds"], Function[fieldId, Or[
				levelEquivalentQ[sortLevel[environment, constructor["FieldContext"], constructor["FieldContext"][fieldId]["Type"]], 0],
				MemberQ[constructor["ConclusionIndices"], freeVariable[fieldId]]
			]]]
		],
	True,
		False
]

(* the universe the recursor eliminates into is named apart from the type's own universe parameters, so
   the two never show the same name *)
eliminationUniverseName[universeParameters_List] := With[{taken = displayedName /@ universeParameters},
	SelectFirst[{HoldComplete[u], HoldComplete[v], HoldComplete[w], HoldComplete[U]}, Function[candidate, ! MemberQ[taken, displayedName[candidate]]]]
]

addInductiveRecords[environment_, name_, universeParameters_, type_, typeContext_, parameterIds_, indexIds_, resultLevel_, inductiveConstant_, checkedConstructors_] := Module[
	{
		largeElimination, eliminationName, recursorUniverseParameters, eliminationLevel, recursorConstant,
		majorId = freshFreeVariable[], motiveId = freshFreeVariable[], minorIds, inductiveRecord, constructorRecords,
		baseContext, motiveType, minorContext, minorTypes, ihIds, recursorContext, recursorType, rules, recursorRecord, extended
	},
	largeElimination = largeEliminationQ[environment, resultLevel, checkedConstructors];
	eliminationName = eliminationUniverseName[universeParameters];
	recursorUniverseParameters = If[largeElimination, Prepend[universeParameters, eliminationName], universeParameters];
	eliminationLevel = If[largeElimination, levelParameter[eliminationName], 0];
	recursorConstant = constantReference[recursorName[name], levelParameter /@ recursorUniverseParameters];
	baseContext = extendContext[typeContext, majorId, HoldComplete[t], makeApplication[inductiveConstant, freeVariable /@ Join[parameterIds, indexIds]], "Explicit"];
	motiveType = makeDependentFunctionType[baseContext, Append[indexIds, majorId], universeSort[eliminationLevel]];
	minorIds = Table[freshFreeVariable[], Length[checkedConstructors]];
	ihIds = Function[constructor, Table[freshFreeVariable[], Length[constructor["RecursiveFields"]]]] /@ checkedConstructors;
	minorContext = Fold[
		Function[{context, triple}, inductionHypothesisContext[context, motiveId, Sequence @@ triple]],
		extendContext[Join @@ Prepend[Function[constructor, constructor["FieldContext"]] /@ checkedConstructors, baseContext], motiveId, HoldComplete[m], motiveType, "Explicit"],
		Transpose[{checkedConstructors, ihIds}]
	];
	minorTypes = MapThread[
		Function[{constructor, constructorIhIds},
			makeDependentFunctionType[minorContext, Join[constructor["FieldIds"], constructorIhIds], makeApplication[
				freeVariable[motiveId],
				Append[constructor["ConclusionIndices"], makeApplication[constantReference[constructor["Name"], levelParameter /@ universeParameters], freeVariable /@ Join[parameterIds, constructor["FieldIds"]]]]
			]]
		],
		{checkedConstructors, ihIds}
	];
	recursorContext = Fold[
		Function[{context, entry}, extendContext[context, First[entry], Last[entry]["Name"], Last[entry]["Type"], Last[entry]["Binder"]]],
		minorContext,
		Join[
			Function[id, {id, Append[typeContext[id], "Binder" -> "Implicit"]}] /@ Join[parameterIds, indexIds],
			MapThread[Function[{id, constructor, minorType}, {id, <|"Name" -> constructor["Name"], "Type" -> minorType, "Binder" -> "Explicit"|>}], {minorIds, checkedConstructors, minorTypes}]
		]
	];
	recursorType = makeDependentFunctionType[
		recursorContext,
		Join[parameterIds, {motiveId}, minorIds, indexIds, {majorId}],
		makeApplication[freeVariable[motiveId], freeVariable /@ Append[indexIds, majorId]]
	];
	rules = Association @ MapThread[
		Function[{constructor, minorId, constructorIhIds},
			constructor["Name"] -> <|
				"NumberOfFields" -> Length[constructor["FieldIds"]],
				"RightHandSide" -> makeLambda[
					recursorContext,
					Join[parameterIds, {motiveId}, minorIds, constructor["FieldIds"]],
					makeApplication[
						freeVariable[minorId],
						Join[
							freeVariable /@ constructor["FieldIds"],
							Function[recursive, inductionHypothesisValue[recursorConstant, parameterIds, motiveId, minorIds, recursive]] /@ constructor["RecursiveFields"]
						]
					]
				]
			|>
		],
		{checkedConstructors, minorIds, ihIds}
	];
	inductiveRecord = <|
		"Kind" -> "InductiveType",
		"Type" -> type,
		"UniverseParameters" -> universeParameters,
		"NumberOfParameters" -> Length[parameterIds],
		"NumberOfIndices" -> Length[indexIds],
		"Constructors" -> Function[constructor, constructor["Name"]] /@ checkedConstructors,
		"LargeElimination" -> largeElimination,
		"Recursive" -> AnyTrue[checkedConstructors, Function[constructor, constructor["RecursiveFields"] =!= {}]]
	|>;
	constructorRecords = Association @ MapIndexed[
		Function[{constructor, position}, constructor["Name"] -> <|
			"Kind" -> "Constructor",
			"Type" -> constructor["Type"],
			"UniverseParameters" -> universeParameters,
			"InductiveType" -> name,
			"ConstructorIndex" -> First[position],
			"NumberOfParameters" -> Length[parameterIds],
			"NumberOfFields" -> Length[constructor["FieldIds"]]
		|>],
		checkedConstructors
	];
	recursorRecord = <|
		"Kind" -> "Recursor",
		"Type" -> recursorType,
		"UniverseParameters" -> recursorUniverseParameters,
		"InductiveType" -> name,
		"NumberOfParameters" -> Length[parameterIds],
		"NumberOfIndices" -> Length[indexIds],
		"NumberOfMinors" -> Length[checkedConstructors],
		"Rules" -> rules,
		"EliminationUniverse" -> largeElimination,
		"KLike" -> And[levelEquivalentQ[resultLevel, 0], Length[checkedConstructors] == 1, AllTrue[checkedConstructors, Function[constructor, constructor["FieldIds"] === {}]]]
	|>;
	extended = addConstantRecords[environment, Join[<|name -> inductiveRecord|>, constructorRecords, <|recursorName[name] -> recursorRecord|>]];
	(* the generated recursor and rules are checked like any other term *)
	sortLevel[extended, <||>, recursorType];
	Scan[Function[rule, inferType[extended, <||>, rule["RightHandSide"]]], Values[rules]];
	extended
]

(* the induction hypotheses of a constructor, one per recursive field: (ys) -> motive indices (field ys) *)
inductionHypothesisContext[context_, motiveId_, constructor_, constructorIhIds_] := Fold[
	Function[{accumulated, pair}, With[{recursive = First[pair], ihId = Last[pair]},
		extendContext[accumulated, ihId, HoldComplete[h], makeDependentFunctionType[
			Join[accumulated, recursive["Context"]],
			recursive["Binders"],
			makeApplication[freeVariable[motiveId], Append[recursive["Indices"], makeApplication[freeVariable[recursive["Id"]], freeVariable /@ recursive["Binders"]]]]
		], "Explicit"]
	]],
	context,
	Transpose[{constructor["RecursiveFields"], constructorIhIds}]
]

inductionHypothesisValue[recursorConstant_, parameterIds_, motiveId_, minorIds_, recursive_] := makeLambda[
	recursive["Context"],
	recursive["Binders"],
	makeApplication[
		recursorConstant,
		Join[
			freeVariable /@ parameterIds,
			{freeVariable[motiveId]},
			freeVariable /@ minorIds,
			recursive["Indices"],
			{makeApplication[freeVariable[recursive["Id"]], freeVariable /@ recursive["Binders"]]}
		]
	]
]
