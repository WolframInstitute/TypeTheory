(* ::Package:: *)

(*
Declaring inductive types: checking them and generating their recursors.

The types I_1, ..., I_n of a block are declared together, and are mutually inductive when there are
several: each constructor ends in one of them, and its fields may mention any of them. They share their
parameters and their universe: each I_j has type (parameters) -> (indices_j) -> Sort level, and each
constructor has type (parameters) -> (fields) -> I_j parameters indices'. The checks:

	- the type of each I_j, and of each constructor, is a type, and the I_j agree on parameters and level;
	- each constructor takes exactly the parameters first and ends in a type of the block applied to them;
	- the block occurs strictly positively: in a field's type only as the result, I_k parameters indices,
	  after binders that do not mention it, with indices that do not either;
	- unless the block is a proposition, each field lives in a universe no larger than the block's.

A field may also mention the block nested in the parameters of another inductive type J, as a tree whose
children are a list of trees. Each such occurrence J ps becomes an auxiliary type
of the block, whose constructors are J's for the parameters ps, so the block is checked as a mutual one.
Its recursors are generated with the auxiliary types, and then J ps takes each one's place again.

Each I_j gets the recursor InductiveRecursor[I_j], and each auxiliary type the recursor
InductiveRecursor[I_1, k]. A recursor's arguments are the parameters
(implicit), one motive per type of the block, auxiliary ones included, one minor premise per constructor
of all of them, the indices (implicit) and the major premise. It eliminates into any Sort u (large
elimination) unless the block may be a proposition and has more than one type, more than one
constructor, or a field that is neither a proof nor an index of the constructor's result; then it
eliminates only into Prop. Each constructor gets a reduction rule. A single proposition with one
constructor and no fields, such as Equal, is K-like: its recursor reduces on any major premise of the
right type.

Under rules with quantities (Quantities.wl), the parameters of each constructor are erased, and so are
the parameters, motives and indices of each recursor. A recursor takes its minor premises and its major
premise at quantity 1 when no constructor of the block has a recursive field, and at quantity Infinity
otherwise; a minor premise takes each field at the quantity the constructor takes it times that.

Everything is built with fresh free variables and abstracted at the end, which keeps de Bruijn indices
out of the construction. The generated recursor types and rules are type-checked before they are added.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[declareInductiveType]
PackageScoped[declareInductiveTypes]
PackageScoped[typeTelescope]
PackageScoped[recursorName]


(* ::Section:: *)
(*Usage Messages*)


declareInductiveType::usage = "declareInductiveType[environment, HoldComplete[name], {HoldComplete[u], ...}, numberOfParameters, type, \
{HoldComplete[constructor] -> constructorType, ...}] checks the inductive family name and gives environment with it, its constructors and its \
recursor added; it throws a kernel failure if a check fails."
declareInductiveTypes::usage = "declareInductiveTypes[environment, {HoldComplete[u], ...}, numberOfParameters, {HoldComplete[name] -> type, ...}, \
{HoldComplete[constructor] -> constructorType, ...}] checks the block of mutually inductive families, and gives environment with them, their \
constructors and their recursors added; it throws a kernel failure if a check fails."
typeTelescope::usage = "typeTelescope[environment, context, type] opens the leading function types of type with fresh free variables and gives {extendedContext, {id, ...}, remainingType}."
recursorName::usage = "recursorName[HoldComplete[name]] gives HoldComplete[InductiveRecursor[name]]."


(* ::Section:: *)
(*Function Definitions*)


(* The binders type has as it stands are opened at once: each binder's type is instantiated with the variables before it,
   and what follows with all of them, where opening one binder at a time would instantiate what follows each time; then
   what follows is put in weak head normal form, as each binder's would be, and any binders that reveals are opened. *)
typeTelescope[environment_, context_, type_] := Block[{telescopeChain = NestWhileList[#[[3]] &, type, Head[#] === dependentFunctionType &], telescopeIds, telescopeContext},
	If[ Length[telescopeChain] == 1,
		telescopeFrom[environment, context, {}, weakHeadNormalForm[environment, context, type]],
		telescopeIds = Table[freshFreeVariable[], Length[telescopeChain] - 1];
		telescopeContext = Fold[
			Function[{accumulated, k}, extendContext[
				accumulated,
				telescopeIds[[k]],
				telescopeChain[[k, 1]],
				instantiateBoundVariables[telescopeChain[[k, 2]], freeVariable /@ Take[telescopeIds, k - 1]],
				telescopeChain[[k, 4]]
			]],
			context,
			Range[Length[telescopeIds]]
		];
		telescopeFrom[
			environment,
			telescopeContext,
			telescopeIds,
			weakHeadNormalForm[environment, telescopeContext, instantiateBoundVariables[Last[telescopeChain], freeVariable /@ telescopeIds]]
		]
	]
]

telescopeFrom[environment_, context_, ids_List, dependentFunctionType[name_, domain_, codomain_, binder_]] := Block[
	{telescopeId = freshFreeVariable[], telescopeExtended},
	telescopeExtended = extendContext[context, telescopeId, name, domain, binder];
	telescopeFrom[environment, telescopeExtended, Append[ids, telescopeId], weakHeadNormalForm[environment, telescopeExtended, instantiateBoundVariable[codomain, freeVariable[telescopeId]]]]
]
telescopeFrom[_, context_, ids_List, rest_] := {context, ids, rest}


recursorName[HoldComplete[name_]] := HoldComplete[InductiveRecursor[name]]

auxiliaryRecursorName[HoldComplete[name_], index_Integer] := HoldComplete[InductiveRecursor[name, index]]

(* Iterative DAG-memoized occurrence check: shared subterms are visited at most once per call, avoiding
   exponential tree expansion on large shared-DAG structure and constructor types. *)
occursQ[{}, _List] := False
occursQ[_, {}] := False
occursQ[roots_, names_List] := Block[
	{
		seenOccursTerms = <||>,
		targetOccursNames = AssociationThread[names, True],
		occursStack = If[ListQ[roots], Fold[{#2, #1} &, {}, Reverse[roots]], {roots, {}}],
		currentOccursTerm,
		occursFound = False
	},
	While[occursStack =!= {} && ! occursFound,
		currentOccursTerm = First[occursStack];
		occursStack = Last[occursStack];
		If[ ! KeyExistsQ[seenOccursTerms, currentOccursTerm],
			seenOccursTerms[currentOccursTerm] = True;
			occursStack = Replace[currentOccursTerm, {
				constantReference[constant_, _] :> (If[KeyExistsQ[targetOccursNames, constant], occursFound = True]; occursStack),
				application[function_, argument_] :> {function, {argument, occursStack}},
				(lambdaAbstraction | dependentFunctionType)[_, domain_, body_, _] :> {domain, {body, occursStack}},
				localDefinition[_, type_, definedValue_, body_] :> {type, {definedValue, {body, occursStack}}},
				projection[_, _, structureTerm_] :> {structureTerm, occursStack},
				cubicalSystem[branches_List] :> Fold[{#2, #1} &, occursStack, Flatten[branches, 1]],
				_ :> occursStack
			}]
		]
	];
	occursFound
]

looseBoundVariablesQ[terms_List] := If[ AssociationQ[$looseBoundRangeCache],
	AnyTrue[terms, looseBoundVariablesQ],
	Block[{$looseBoundRangeCache = <||>}, AnyTrue[terms, looseBoundVariablesQ]]
]
looseBoundVariablesQ[term_] := If[ AssociationQ[$looseBoundRangeCache],
	looseBoundRange[term] > 0,
	Block[{$looseBoundRangeCache = <||>}, looseBoundRange[term] > 0]
]


declareInductiveType[environment_, name_HoldComplete, universeParameters_List, numberOfParameters_Integer, type_, constructors_List] :=
	declareInductiveTypes[environment, universeParameters, numberOfParameters, {name -> type}, constructors]

declareInductiveTypes[environment_, universeParameters_List, numberOfParameters_Integer, types : {(_HoldComplete -> _) ..}, constructors_List] :=
	withCheckedTerms[declareBlock[environment, universeParameters, numberOfParameters, types, constructors]]

declareBlock[environment_, universeParameters_List, numberOfParameters_Integer, types_List, constructors_List] := Block[
	{
		blockNames = Keys[types], blockLevels = levelParameter /@ universeParameters,
		blockTypeContext, blockParameterIds, blockOriginals, blockProvisional, blockOwnedConstructors,
		blockOriginalConstructors, blockAllConstructors, blockAuxiliaries, blockAllTypes,
		blockResultLevel, blockCheckedProvisional, blockCheckedConstructors
	},
	checkUniverseParameters[First[blockNames], universeParameters, Join[Values[types], Values[constructors]]];
	If[ ! DuplicateFreeQ[Join[blockNames, recursorName /@ blockNames, Keys[constructors]]],
		kernelFailure["DuplicateConstructor", "The constructors of `1` must have distinct names, different from the types and their recursors.", {HoldForm @@ First[blockNames]}]
	];
	(* that the types and the constructors' types are types the compiled kernel checks of their records, when it checks a
	   batch, and so are the universes of the constructors' fields; the levels of the fields large elimination takes are
	   found here either way *)
	If[! $deferKernelChecks, Scan[sortLevel[environment, <||>, #] &, Values[types]]];
	{blockTypeContext, blockParameterIds} = blockParameters[environment, First[types], numberOfParameters];
	blockOriginals = blockType[environment, blockTypeContext, blockParameterIds, First[#], Last[#], constantReference[First[#], blockLevels], None] & /@ types;
	(* the constructor types may mention the types being declared *)
	blockProvisional = addConstantRecords[environment, Association[(#["Name"] -> provisionalRecord[#, universeParameters, numberOfParameters]) & /@ blockOriginals]];
	(* the constructors of the first type come first, then the second's, and so on, each in the order given *)
	blockOwnedConstructors = originalConstructor[blockProvisional, blockTypeContext, blockParameterIds, blockOriginals, #] & /@ constructors;
	blockOriginalConstructors = Catenate[selectConstructorsByOwner[blockOwnedConstructors, #] & /@ blockNames];
	{blockAllConstructors, blockAuxiliaries} = eliminateNested[environment, universeParameters, blockTypeContext, blockParameterIds, blockNames, blockOriginalConstructors];
	blockAllTypes = Join[
		blockOriginals,
		blockType[blockProvisional, blockTypeContext, blockParameterIds, #["Name"], #["Type"], constantReference[#["Name"], blockLevels], #] & /@ blockAuxiliaries
	];
	blockResultLevel = blockLevel[blockNames, blockAllTypes];
	blockCheckedProvisional = addConstantRecords[blockProvisional, Association[(#["Name"] -> provisionalRecord[#, universeParameters, numberOfParameters]) & /@ Drop[blockAllTypes, Length[blockNames]]]];
	blockCheckedConstructors = checkConstructor[blockCheckedProvisional, blockTypeContext, blockParameterIds, blockAllTypes, blockResultLevel, #] & /@ blockAllConstructors;
	(* a recursive field's sort mentions the types themselves, as Acc's does, so they must be declared to find it *)
	addBlockRecords[
		environment, universeParameters, numberOfParameters, blockTypeContext, blockParameterIds, blockNames, blockAllTypes, blockResultLevel, blockCheckedConstructors,
		largeEliminationQ[blockCheckedProvisional, blockResultLevel, blockAllTypes, blockCheckedConstructors]
	]
]

selectConstructorsByOwner[constructors_List, ownerName_] := Select[constructors, #["Owner"] === ownerName &]


(* ::Subsection:: *)
(*Types*)


(* the parameters are the first type's leading binders, which every type of the block shares *)
blockParameters[environment_, name_ -> type_, numberOfParameters_Integer] := Block[{paramTypeContext, paramBinderIds, paramResultType},
	{paramTypeContext, paramBinderIds, paramResultType} = typeTelescope[environment, <||>, type];
	If[ Length[paramBinderIds] < numberOfParameters,
		kernelFailure["InductiveParameters", "The type of `1` has fewer than `2` binders for its parameters.", {HoldForm @@ name, numberOfParameters}]
	];
	{KeyTake[paramTypeContext, Take[paramBinderIds, numberOfParameters]], Take[paramBinderIds, numberOfParameters]}
]

blockType[environment_, typeContext_, parameterIds_, name_, type_, constant_, nested_] := Block[{btAfterParameters, btContext, btIndexIds, btResult},
	btAfterParameters = leadingParametersInstantiated[environment, typeContext, type, parameterIds,
		kernelFailure["InductiveParameters", "The types of a block must take the same parameters first, and `1` does not.", {HoldForm @@ name}] &
	];
	{btContext, btIndexIds, btResult} = typeTelescope[environment, typeContext, btAfterParameters];
	<|
		"Name" -> name,
		"Type" -> type,
		"Constant" -> constant,
		"IndexIds" -> btIndexIds,
		"Context" -> btContext,
		"Level" -> extractSortLevel[btResult],
		"Nested" -> nested
	|>
]

extractSortLevel[universeSort[level_]] := level
extractSortLevel[_] := kernelFailure["InductiveTypeSort", "The type of an inductive type must end in a sort.", {}]

(* The leading binders of type take the parameters' places when their types agree. The binders type has as it stands
   are compared at once, each binder's type instantiated with the parameters before it, and what follows them instantiated
   with all of them; any parameters left take the binders a weak head normal form reveals, one at a time. *)
leadingParametersInstantiated[environment_, typeContext_, type_, parameterIds_List, failure_] := Block[
	{parameterChain = NestWhileList[#[[3]] &, type, Head[#] === dependentFunctionType &, 1, Length[parameterIds]], standingCount},
	standingCount = Length[parameterChain] - 1;
	Do[
		If[ ! definitionallyEqualQ[environment, typeContext, instantiateBoundVariables[parameterChain[[k, 2]], freeVariable /@ Take[parameterIds, k - 1]], typeContext[parameterIds[[k]]]["Type"]],
			failure[]
		],
		{k, standingCount}
	];
	Fold[
		instantiateLeadingParameter[environment, typeContext, #1, #2, failure] &,
		If[standingCount == 0, type, instantiateBoundVariables[Last[parameterChain], freeVariable /@ Take[parameterIds, standingCount]]],
		Drop[parameterIds, standingCount]
	]
]

(* a leading binder takes the parameter's place when their types agree; both are binder types of the block's
   types, checked first in declareBlock, or of the auxiliary types built from them *)
instantiateLeadingParameter[environment_, typeContext_, remaining_, parameterId_, failure_] :=
	matchLeadingParameter[environment, typeContext, weakHeadNormalForm[environment, typeContext, remaining], parameterId, failure]

matchLeadingParameter[environment_, typeContext_, dependentFunctionType[_, domain_, codomain_, _], parameterId_, _] /;
	definitionallyEqualQ[environment, typeContext, domain, typeContext[parameterId]["Type"]] :=
	instantiateBoundVariable[codomain, freeVariable[parameterId]]
matchLeadingParameter[_, _, _, _, failure_] := failure[]

blockLevel[names_, blockTypes_] := Block[{firstBlockLevel = First[blockTypes]["Level"]},
	If[ ! AllTrue[blockTypes, levelEquivalentQ[#["Level"], firstBlockLevel] &],
		kernelFailure["InductiveUniverse", "The types of the block of `1` must live in the same universe.", {HoldForm @@ First[names]}]
	];
	firstBlockLevel
]

provisionalRecord[type_, universeParameters_, numberOfParameters_] := <|
	"Kind" -> "InductiveType",
	"Type" -> type["Type"],
	"UniverseParameters" -> universeParameters,
	"NumberOfParameters" -> numberOfParameters,
	"NumberOfIndices" -> Length[type["IndexIds"]],
	"Constructors" -> {},
	"LargeElimination" -> False,
	"Recursive" -> False,
	"Block" -> {type["Name"]}
|>


(* ::Subsection:: *)
(*Constructors*)


(* a constructor with its parameters instantiated, and the type of the block it ends in *)
originalConstructor[environment_, typeContext_, parameterIds_, originals_, constructorName_ -> constructorType_] := Block[
	{ocAfterParameters, ocConclusion, ocOwner},
	If[! $deferKernelChecks, sortLevel[environment, <||>, constructorType]];
	ocAfterParameters = leadingParametersInstantiated[environment, typeContext, constructorType, parameterIds,
		kernelFailure["ConstructorParameters", "The constructor `1` must take the parameters of its type first.", {HoldForm @@ constructorName}] &
	];
	(* the type it ends in, after the binders it has as it stands, names its owner: a type of the block applied to
	   arguments is in weak head normal form; anything else is put in it, as a telescope does *)
	ocConclusion = Last[NestWhileList[#[[3]] &, ocAfterParameters, Head[#] === dependentFunctionType &]];
	ocOwner = findOwnerType[originals, First[applicationSpine[ocConclusion]]];
	If[ ocOwner === None,
		ocConclusion = Last @ typeTelescope[environment, typeContext, ocAfterParameters];
		ocOwner = findOwnerType[originals, First[applicationSpine[ocConclusion]]]
	];
	If[ ocOwner === None,
		kernelFailure[
			"ConstructorResult",
			"The constructor `1` must end in `2` applied to its parameters and indices.",
			{HoldForm @@ constructorName, If[Length[originals] == 1, HoldForm @@ First[originals]["Name"], (HoldForm @@ #) & /@ Lookup[originals, "Name"]]}
		]
	];
	<|"Name" -> constructorName, "Type" -> constructorType, "Owner" -> ocOwner["Name"], "AfterParameters" -> ocAfterParameters, "Original" -> None|>
]

findOwnerType[originals_List, head_] := SelectFirst[originals, #["Constant"] === head &, None]

checkConstructor[environment_, typeContext_, parameterIds_, blockTypes_, resultLevel_, constructor_] := Block[
	{
		ccNames = Lookup[blockTypes, "Name"], ccOwner,
		ccFieldContext, ccFieldIds, ccConclusion, ccConclusionHead, ccConclusionArguments, ccConclusionIndices, ccRecursiveFields
	},
	ccOwner = SelectFirst[blockTypes, #["Name"] === constructor["Owner"] &];
	If[! $deferKernelChecks, sortLevel[environment, typeContext, constructor["AfterParameters"]]];
	{ccFieldContext, ccFieldIds, ccConclusion} = typeTelescope[environment, typeContext, constructor["AfterParameters"]];
	{ccConclusionHead, ccConclusionArguments} = applicationSpine[ccConclusion];
	If[ ccConclusionHead =!= ccOwner["Constant"] || Length[ccConclusionArguments] =!= Length[parameterIds] + Length[ccOwner["IndexIds"]],
		kernelFailure["ConstructorResult", "The constructor `1` must end in `2` applied to its parameters and indices.", {HoldForm @@ displayedConstructorName[constructor], HoldForm @@ displayedOwner[blockTypes, constructor]}]
	];
	If[ Take[ccConclusionArguments, Length[parameterIds]] =!= (freeVariable /@ parameterIds),
		kernelFailure["ConstructorParameters", "The constructor `1` must end in `2` applied to the same parameters.", {HoldForm @@ displayedConstructorName[constructor], HoldForm @@ displayedOwner[blockTypes, constructor]}]
	];
	ccConclusionIndices = Drop[ccConclusionArguments, Length[parameterIds]];
	If[ occursQ[ccConclusionIndices, ccNames],
		kernelFailure["NonPositiveOccurrence", "`1` occurs in an index of the result of the constructor `2`.", {HoldForm @@ displayedOwner[blockTypes, constructor], HoldForm @@ displayedConstructorName[constructor]}]
	];
	ccRecursiveFields = Flatten[
		recursiveFieldData[environment, ccFieldContext, blockTypes, parameterIds, constructor, #] & /@ ccFieldIds
	];
	(* an auxiliary type's constructor has no record for the compiled kernel to check *)
	If[ ! $deferKernelChecks || constructor["Original"] =!= None,
		checkFieldUniverses[environment, ccFieldContext, ccFieldIds, resultLevel, displayedConstructorName[constructor]]
	];
	<|
		constructor,
		"FieldIds" -> ccFieldIds,
		"FieldContext" -> ccFieldContext,
		"ConclusionIndices" -> ccConclusionIndices,
		"RecursiveFields" -> ccRecursiveFields
	|>
]

(* an auxiliary type's constructor is named by the constructor of the nested type it stands for, and the
   type by the block's first *)
displayedConstructorName[constructor_] := Replace[constructor["Original"], None :> constructor["Name"]]

displayedOwner[blockTypes_, constructor_] := If[constructor["Original"] === None, constructor["Owner"], First[blockTypes]["Name"]]

(* A field is recursive when its type is (ys) -> I_k parameters indices with the block absent from the ys
   and the indices; it is non-recursive when the block does not occur at all; anything else is not
   strictly positive. *)
recursiveFieldData[environment_, fieldContext_, blockTypes_, parameterIds_, constructor_, fieldId_] := Block[
	{rfNames = Lookup[blockTypes, "Name"], rfFieldType = fieldContext[fieldId]["Type"], rfInnerContext, rfBinderIds, rfResult, rfResultHead, rfResultArguments, rfTarget},
	If[ ! occursQ[rfFieldType, rfNames],
		{},
		{rfInnerContext, rfBinderIds, rfResult} = typeTelescope[environment, fieldContext, rfFieldType];
		{rfResultHead, rfResultArguments} = applicationSpine[rfResult];
		rfTarget = FirstPosition[Lookup[blockTypes, "Constant"], Verbatim[rfResultHead], {None}, {1}, Heads -> False];
		If[ Or[
				AnyTrue[rfBinderIds, occursQ[rfInnerContext[#]["Type"], rfNames] &],
				First[rfTarget] === None,
				Take[rfResultArguments, UpTo[Length[parameterIds]]] =!= (freeVariable /@ parameterIds),
				occursQ[Drop[rfResultArguments, Length[parameterIds]], rfNames]
			],
			kernelFailure[
				"NonPositiveOccurrence",
				"`1` does not occur strictly positively in the constructor `2`.",
				{HoldForm @@ displayedOwner[blockTypes, constructor], HoldForm @@ displayedConstructorName[constructor]}
			],
			{<|"Id" -> fieldId, "Binders" -> rfBinderIds, "Context" -> rfInnerContext, "Indices" -> Drop[rfResultArguments, Length[parameterIds]], "Target" -> First[rfTarget]|>}
		]
	]
]

checkFieldUniverses[environment_, fieldContext_, fieldIds_, resultLevel_, constructorName_] := If[ ! levelEquivalentQ[resultLevel, 0],
	Scan[
		checkOneFieldUniverse[environment, fieldContext, #, resultLevel, constructorName] &,
		fieldIds
	]
]

checkOneFieldUniverse[environment_, fieldContext_, fieldId_, resultLevel_, constructorName_] := Block[
	{checkedFieldLevel = sortLevel[environment, fieldContext, fieldContext[fieldId]["Type"]]},
	If[ ! levelLessEqualQ[checkedFieldLevel, resultLevel],
		kernelFailure["UniverseTooLarge", "A field of the constructor `1` lives in a larger universe than its type.", {HoldForm @@ constructorName}]
	]
]


(* ::Subsection:: *)
(*Nested occurrences*)


(* Each occurrence J ps of the block nested in the parameters ps of an inductive type J becomes an
   auxiliary type, the same one for the same J ps. The original constructors are taken first, then the
   constructors of each auxiliary type in turn, which may nest further: the
   auxiliary types are numbered in this order. *)
(* a type of the block nests in another inductive type only through a field or an index that mentions it: a block whose
   constructors mention none of its types there, as a structure's do, has nothing nested, and its constructors go on as
   the replacement below would rebuild them *)
eliminateNested[environment_, universeParameters_, typeContext_, parameterIds_, names_, originalConstructors_] /;
	! occursQ[Catenate[constructorFieldsAndIndices[#["AfterParameters"]] & /@ originalConstructors], names] :=
	{originalConstructors, {}}

constructorFieldsAndIndices[term_] := Block[
	{fieldChain = NestWhileList[dependentBody, term, dependentFunctionTypeQ]},
	Join[dependentDomain /@ Most[fieldChain], Last[applicationSpine[Last[fieldChain]]]]
]

dependentFunctionTypeQ[dependentFunctionType[_, _, _, _]] := True
dependentFunctionTypeQ[_] := False
dependentDomain[dependentFunctionType[_, domain_, _, _]] := domain
dependentBody[dependentFunctionType[_, _, body_, _]] := body

eliminateNested[environment_, universeParameters_, typeContext_, parameterIds_, names_, originalConstructors_] := Block[
	{
		$nestedEnvironment = environment,
		$nestedUniverseParameters = universeParameters,
		$nestedTypeContext = typeContext,
		$nestedParameterIds = parameterIds,
		$nestedNames = names,
		$nestedAuxiliaries = {},
		$nestedReplaceMemo = <||>,
		nestedReplaced,
		nestedIndex = 1
	},
	nestedReplaced = (Append[#, "AfterParameters" -> replaceNestedTerm[#["AfterParameters"]]] &) /@ originalConstructors;
	While[ nestedIndex <= Length[$nestedAuxiliaries],
		$nestedAuxiliaries[[nestedIndex, "Constructors"]] = (Append[#, "AfterParameters" -> replaceNestedTerm[#["AfterParameters"]]] &) /@ $nestedAuxiliaries[[nestedIndex, "Constructors"]];
		nestedIndex++
	];
	{Join[nestedReplaced, Catenate[Lookup[$nestedAuxiliaries, "Constructors", {}]]], $nestedAuxiliaries}
]

replaceNestedTerm[term_] := Lookup[$nestedReplaceMemo, Key[term], $nestedReplaceMemo[term] = replaceNestedSpine[applicationSpine[term]]]

replaceNestedSpine[{constantReference[inductive_, inductiveLevels_], arguments_}] /; nestedOccurrenceQ[$nestedEnvironment, $nestedNames, inductive, arguments] :=
	nestedApplicationTerm[inductive, inductiveLevels, arguments]
replaceNestedSpine[{head_, {}}] := replaceNestedParts[head]
replaceNestedSpine[{head_, arguments_}] := makeApplication[replaceNestedParts[head], replaceNestedTerm /@ arguments]

replaceNestedParts[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_]] :=
	Construct[head, name, replaceNestedTerm[domain], replaceNestedTerm[body], binder]
replaceNestedParts[localDefinition[name_, type_, value_, body_]] :=
	Construct[localDefinition, name, replaceNestedTerm[type], replaceNestedTerm[value], replaceNestedTerm[body]]
replaceNestedParts[projection[structure_, fieldIndex_, structureTerm_]] :=
	Construct[projection, structure, fieldIndex, replaceNestedTerm[structureTerm]]
replaceNestedParts[cubicalSystem[branches_List]] :=
	Construct[cubicalSystem, Map[replaceNestedTerm, branches, {2}]]
replaceNestedParts[other_] := other

nestedApplicationTerm[inductive_, inductiveLevels_, arguments_] := Block[
	{
		nestedParamCount = constantRecord[$nestedEnvironment, inductive]["NumberOfParameters"],
		nestedParams, nestedAux
	},
	nestedParams = Take[arguments, nestedParamCount];
	If[ occursQ[Drop[arguments, nestedParamCount], $nestedNames],
		kernelFailure["NonPositiveOccurrence", "`1` occurs in an index of the nested type `2`.", {HoldForm @@ First[$nestedNames], HoldForm @@ inductive}]
	];
	If[ looseBoundVariablesQ[nestedParams],
		kernelFailure["NestedParameters", "The parameters of the nested type `1` must not depend on the fields of a constructor of `2`.", {HoldForm @@ inductive, HoldForm @@ First[$nestedNames]}]
	];
	nestedAux = SelectFirst[$nestedAuxiliaries, #["Key"] === {inductive, inductiveLevels, nestedParams} &, None];
	If[ nestedAux === None,
		If[ Length[$nestedAuxiliaries] >= $maximumAuxiliaryTypes,
			kernelFailure["NestingTooDeep", "`1` is nested more than `2` times.", {HoldForm @@ First[$nestedNames], $maximumAuxiliaryTypes}]
		];
		nestedAux = auxiliaryType[$nestedEnvironment, $nestedTypeContext, $nestedParameterIds, First[$nestedNames], Length[$nestedAuxiliaries] + 1, inductive, inductiveLevels, nestedParams];
		$nestedAuxiliaries = Append[$nestedAuxiliaries, nestedAux]
	];
	makeApplication[constantReference[nestedAux["Name"], levelParameter /@ $nestedUniverseParameters], Join[freeVariable /@ $nestedParameterIds, Drop[arguments, nestedParamCount]]]
]

$maximumAuxiliaryTypes = 64

nestedOccurrenceQ[environment_, names_, inductive_, arguments_] := And[
	! MemberQ[names, inductive],
	constantDeclaredQ[environment, inductive],
	constantRecord[environment, inductive]["Kind"] === "InductiveType",
	Length[arguments] >= constantRecord[environment, inductive]["NumberOfParameters"],
	occursQ[Take[arguments, constantRecord[environment, inductive]["NumberOfParameters"]], names]
]

(* the auxiliary type for J ps: J's type and constructors for the parameters ps, after the block's own *)
auxiliaryType[environment_, typeContext_, parameterIds_, firstName_, index_, inductive_, inductiveLevels_, parameters_] := Block[
	{auxRecord = constantRecord[environment, inductive], auxName = HoldComplete[nestedAuxiliary[firstName, index]]},
	<|
		"Key" -> {inductive, inductiveLevels, parameters},
		"Name" -> auxName,
		"Inductive" -> inductive,
		"Levels" -> inductiveLevels,
		"Parameters" -> parameters,
		"Type" -> makeDependentFunctionType[typeContext, parameterIds, instantiateParameters[auxRecord, inductiveLevels, auxRecord["Type"], parameters]],
		"Constructors" -> MapIndexed[
			<|
				"Name" -> HoldComplete[nestedAuxiliary[firstName, index, First[#2]]],
				"Type" -> None,
				"Owner" -> auxName,
				"AfterParameters" -> instantiateParameters[auxRecord, inductiveLevels, constantRecord[environment, #1]["Type"], parameters],
				"Original" -> #1
			|> &,
			auxRecord["Constructors"]
		]
	|>
]

(* a type of J's or of its constructors, at J's levels and with J's parameters instantiated *)
instantiateParameters[record_, inductiveLevels_, type_, parameters_] := Fold[
	instantiateOneParameter,
	instantiateUniverseParameters[type, record["UniverseParameters"], inductiveLevels],
	parameters
]

instantiateOneParameter[dependentFunctionType[_, _, codomain_, _], parameter_] := instantiateBoundVariable[codomain, parameter]
instantiateOneParameter[remaining_, _] := remaining

(* once the recursors are generated, the nested type and its constructors take each auxiliary's place *)
restoreNested[blockTypes_, numberOfParameters_][term_] := Block[
	{
		$restoreAuxiliaries = Select[blockTypes, #["Nested"] =!= None &],
		$restoreAuxiliaryNames,
		$restoreNumberOfParameters = numberOfParameters,
		$restoreMemo = <||>
	},
	If[ $restoreAuxiliaries === {},
		term,
		$restoreAuxiliaryNames = AssociationThread[Lookup[$restoreAuxiliaries, "Name"], $restoreAuxiliaries];
		restoreNestedTerm[term]
	]
]

restoreNestedTerm[subterm_] := Lookup[$restoreMemo, Key[subterm], $restoreMemo[subterm] = restoreNestedSpine[applicationSpine[subterm]]]

restoreNestedSpine[{constantReference[name_, _], arguments_}] /; KeyExistsQ[$restoreAuxiliaryNames, name] :=
	restoreAuxiliaryApplication[$restoreAuxiliaryNames[name]["Nested"], arguments]
restoreNestedSpine[{constantReference[HoldComplete[nestedAuxiliary[_, auxiliaryIndex_, constructorIndex_]], _], arguments_}] :=
	restoreAuxiliaryConstructor[$restoreAuxiliaries[[auxiliaryIndex]]["Nested"], constructorIndex, arguments]
restoreNestedSpine[{head_, {}}] := restoreNestedParts[head]
restoreNestedSpine[{head_, arguments_}] := makeApplication[restoreNestedParts[head], restoreNestedTerm /@ arguments]

restoreAuxiliaryApplication[nested_, arguments_] := makeApplication[
	constantReference[nested["Inductive"], nested["Levels"]],
	Join[nested["Parameters"], restoreNestedTerm /@ Drop[arguments, $restoreNumberOfParameters]]
]

restoreAuxiliaryConstructor[nested_, constructorIndex_, arguments_] := makeApplication[
	constantReference[nested["Constructors"][[constructorIndex]]["Original"], nested["Levels"]],
	Join[nested["Parameters"], restoreNestedTerm /@ Drop[arguments, $restoreNumberOfParameters]]
]

restoreNestedParts[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_]] :=
	Construct[head, name, restoreNestedTerm[domain], restoreNestedTerm[body], binder]
restoreNestedParts[localDefinition[name_, type_, value_, body_]] :=
	Construct[localDefinition, name, restoreNestedTerm[type], restoreNestedTerm[value], restoreNestedTerm[body]]
restoreNestedParts[projection[structure_, fieldIndex_, structureTerm_]] :=
	Construct[projection, structure, fieldIndex, restoreNestedTerm[structureTerm]]
restoreNestedParts[cubicalSystem[branches_List]] :=
	Construct[cubicalSystem, Map[restoreNestedTerm, branches, {2}]]
restoreNestedParts[other_] := other

restoredContext[restore_, context_Association] := Map[Append[#, "Type" -> restore[#["Type"]]] &, context]


(* ::Subsection:: *)
(*Recursors*)


(* Large elimination: a block that may be a proposition eliminates into any universe only if it is a single type
   with at most one constructor, whose fields are proofs or indices of its result *)
largeEliminationQ[environment_, resultLevel_, blockTypes_, checkedConstructors_List] := Which[
	levelNeverZeroQ[resultLevel],
		True,
	Length[blockTypes] > 1,
		False,
	Length[checkedConstructors] == 0,
		True,
	Length[checkedConstructors] == 1,
		largeEliminationConstructorQ[environment, First[checkedConstructors]],
	True,
		False
]

largeEliminationConstructorQ[environment_, constructor_] := AllTrue[
	constructor["FieldIds"],
	Or[
		levelEquivalentQ[sortLevel[environment, constructor["FieldContext"], constructor["FieldContext"][#]["Type"]], 0],
		MemberQ[constructor["ConclusionIndices"], freeVariable[#]]
	] &
]

(* the universe the recursor eliminates into is named apart from the type's own universe parameters, so
   the two never show the same name *)
eliminationUniverseName[universeParameters_List] := With[{taken = displayedName /@ universeParameters},
	SelectFirst[{HoldComplete[u], HoldComplete[v], HoldComplete[w], HoldComplete[U]}, Function[candidate, ! MemberQ[taken, displayedName[candidate]]]]
]

(* a single motive is m; the motives of a block are m1, m2, ... *)
motiveNames[1] := {HoldComplete[m]}
motiveNames[count_Integer] := Table[With[{motive = Symbol[Context[m] <> "m" <> ToString[index]]}, HoldComplete[motive]], {index, count}]

addBlockRecords[environment_, universeParameters_, numberOfParameters_, typeContext_, parameterIds_, names_, blockTypes_, resultLevel_, rawConstructors_, largeElimination_] :=
	Block[{$binderAbstractions = <||>}, blockRecords[environment, universeParameters, numberOfParameters, typeContext, parameterIds, names, blockTypes, resultLevel, rawConstructors, largeElimination]]

blockRecords[environment_, universeParameters_, numberOfParameters_, typeContext_, parameterIds_, names_, blockTypes_, resultLevel_, rawConstructors_, largeElimination_] := Block[
	{
		brLevels = levelParameter /@ universeParameters, brRestore, brCheckedConstructors, brEliminationName, brRecursorUniverseParameters, brEliminationLevel,
		brRecursorConstants, brMotiveIds, brMajorIds, brMajorTypes, brMajorContexts, brMotiveContext, brMinorIds, brIhIds, brMinorContext, brMinorTypes,
		brRecursorContexts, brRecursorTypes, brRules, brInductiveRecords, brConstructorRecords, brRecursorRecords, brExtended, brMatchQuantity, brMatchBinder, brPremiseContext
	},
	brRestore = If[AllTrue[blockTypes, #["Nested"] === None &], Identity, restoreNested[blockTypes, numberOfParameters]];
	(* the auxiliary types give way to the nested types before anything is built from the constructors *)
	brCheckedConstructors = restoreConstructorData[brRestore, brLevels, parameterIds, #] & /@ rawConstructors;
	brEliminationName = eliminationUniverseName[universeParameters];
	brRecursorUniverseParameters = If[largeElimination, Prepend[universeParameters, brEliminationName], universeParameters];
	(* without Prop, the motive's universe is Type u, which is never Prop *)
	brEliminationLevel = Which[
		! largeElimination, 0,
		rulesSetting[environment, "Prop"], levelParameter[brEliminationName],
		True, normalizeLevel[levelSuccessor[levelParameter[brEliminationName], 1]]
	];
	brRecursorConstants = MapIndexed[
		constantReference[
			If[First[#2] <= Length[names], recursorName[#1["Name"]], auxiliaryRecursorName[First[names], First[#2] - Length[names]]],
			levelParameter /@ brRecursorUniverseParameters
		] &,
		blockTypes
	];
	brMotiveIds = Table[freshFreeVariable[], Length[blockTypes]];
	brMajorIds = Table[freshFreeVariable[], Length[blockTypes]];
	brMajorTypes = (brRestore[makeApplication[#["Constant"], freeVariable /@ Join[parameterIds, #["IndexIds"]]]] &) /@ blockTypes;
	brMajorContexts = MapThread[
		extendContext[restoredContext[brRestore, #1["Context"]], #2, HoldComplete[t], #3, "Explicit"] &,
		{blockTypes, brMajorIds, brMajorTypes}
	];
	brMotiveContext = Fold[
		extendContext[#1, Sequence @@ #2, "Explicit"] &,
		Join @@ Prepend[brMajorContexts, typeContext],
		MapThread[
			{#2, #5, makeDependentFunctionType[#4, Append[#1["IndexIds"], #3], universeSort[brEliminationLevel]]} &,
			{blockTypes, brMotiveIds, brMajorIds, brMajorContexts, motiveNames[Length[blockTypes]]}
		]
	];
	brMinorIds = Table[freshFreeVariable[], Length[brCheckedConstructors]];
	brIhIds = (Table[freshFreeVariable[], Length[#["RecursiveFields"]]] &) /@ brCheckedConstructors;
	brMinorContext = Fold[
		inductionHypothesisContext[#1, brMotiveIds, Sequence @@ #2] &,
		Join @@ Append[(#["FieldContext"] &) /@ brCheckedConstructors, brMotiveContext],
		Transpose[{brCheckedConstructors, brIhIds}]
	];
	(* with quantities, a match uses its argument once, unless it recurses; without them every quantity is Infinity *)
	brMatchQuantity = If[AnyTrue[brCheckedConstructors, #["RecursiveFields"] =!= {} &], Infinity, 1];
	brMatchBinder = If[rulesSetting[environment, "Quantities"], quantifiedBinder["Explicit", brMatchQuantity], "Explicit"];
	brPremiseContext = Fold[
		scaleFieldBinderQuantity[brMatchQuantity, #1, #2] &,
		brMinorContext,
		Catenate[Lookup[brCheckedConstructors, "FieldIds"]]
	];
	brMinorTypes = MapThread[
		makeDependentFunctionType[brPremiseContext, Join[#1["FieldIds"], #2], makeApplication[
			freeVariable[brMotiveIds[[ownerPosition[blockTypes, #1]]]],
			Append[#1["ConclusionIndices"], #1["Application"]]
		]] &,
		{brCheckedConstructors, brIhIds}
	];
	brRecursorContexts = MapThread[
		buildRecursorContext[environment, brMinorContext, parameterIds, brMotiveIds, brMinorIds, brCheckedConstructors, brMinorTypes, brMatchBinder, #1, #2] &,
		{blockTypes, brMajorIds}
	];
	brRecursorTypes = MapThread[
		makeDependentFunctionType[
			#4,
			Join[parameterIds, brMotiveIds, brMinorIds, #1["IndexIds"], {#3}],
			makeApplication[freeVariable[#2], freeVariable /@ Append[#1["IndexIds"], #3]]
		] &,
		{blockTypes, brMotiveIds, brMajorIds, brRecursorContexts}
	];
	brRules = MapIndexed[
		buildTypeRecursorRules[blockTypes, brCheckedConstructors, brRecursorConstants, First[brRecursorContexts], parameterIds, brMotiveIds, brMinorIds, numberOfParameters, #1, First[#2]] &,
		blockTypes
	];
	brInductiveRecords = Association[
		buildInductiveRecord[brCheckedConstructors, universeParameters, numberOfParameters, largeElimination, names, #] & /@ Take[blockTypes, Length[names]]
	];
	brConstructorRecords = Association[Catenate[
		buildConstructorRecords[environment, brCheckedConstructors, universeParameters, numberOfParameters, #] & /@ Take[blockTypes, Length[names]]
	]];
	brRecursorRecords = Association @ MapThread[
		buildRecursorRecord[blockTypes, brCheckedConstructors, brRecursorUniverseParameters, numberOfParameters, largeElimination, resultLevel, #1, #2, #3, #4] &,
		{blockTypes, brRecursorConstants, brRecursorTypes, brRules}
	];
	brExtended = addConstantRecords[environment, Join[brInductiveRecords, brConstructorRecords, brRecursorRecords]];
	(* the generated recursors and rules are checked like any other term, by the compiled kernel when it checks a batch *)
	If[ ! $deferKernelChecks,
		Scan[sortLevel[brExtended, <||>, #] &, brRecursorTypes];
		Scan[inferType[brExtended, <||>, #["RightHandSide"]] &, Catenate[Values /@ brRules]]
	];
	brExtended
]

restoreConstructorData[restore_, levels_, parameterIds_, constructor_] := Join[constructor, <|
	"FieldContext" -> restoredContext[restore, constructor["FieldContext"]],
	"RecursiveFields" -> (Append[#, "Context" -> restoredContext[restore, #["Context"]]] &) /@ constructor["RecursiveFields"],
	"Application" -> restore[makeApplication[constantReference[constructor["Name"], levels], freeVariable /@ Join[parameterIds, constructor["FieldIds"]]]]
|>]

scaleFieldBinderQuantity[matchQuantity_, context_, fieldId_] := Block[{scaledBinder = context[fieldId]["Binder"]},
	Append[context, fieldId -> Append[context[fieldId], "Binder" -> quantifiedBinder[binderKind[scaledBinder], multiplyQuantities[matchQuantity, binderQuantity[scaledBinder]]]]]
]

buildRecursorContext[environment_, minorContext_, parameterIds_, motiveIds_, minorIds_, checkedConstructors_, minorTypes_, matchBinder_, type_, majorId_] := Fold[
	extendContext[#1, First[#2], Last[#2]["Name"], Last[#2]["Type"], Last[#2]["Binder"]] &,
	minorContext,
	Join[
		({#, Append[minorContext[#], "Binder" -> erasedBinder[environment, "Implicit"]]} &) /@ Join[parameterIds, type["IndexIds"]],
		({#, Append[minorContext[#], "Binder" -> erasedBinder[environment, "Explicit"]]} &) /@ motiveIds,
		MapThread[
			{#1, <|"Name" -> displayedConstructorName[#2], "Type" -> #3, "Binder" -> matchBinder|>} &,
			{minorIds, checkedConstructors, minorTypes}
		],
		{{majorId, Append[minorContext[majorId], "Binder" -> matchBinder]}}
	]
]

buildTypeRecursorRules[blockTypes_, checkedConstructors_, recursorConstants_, firstRecursorContext_, parameterIds_, motiveIds_, minorIds_, numberOfParameters_, type_, typePosition_] :=
	Association @ Map[
		buildOneRecursorRule[type, checkedConstructors[[#]], #, recursorConstants, firstRecursorContext, parameterIds, motiveIds, minorIds, numberOfParameters] &,
		Select[Range[Length[checkedConstructors]], ownerPosition[blockTypes, checkedConstructors[[#]]] == typePosition &]
	]

buildOneRecursorRule[type_, constructor_, constructorIndex_, recursorConstants_, firstRecursorContext_, parameterIds_, motiveIds_, minorIds_, numberOfParameters_] :=
	displayedConstructorName[constructor] -> <|
		"NumberOfParameters" -> If[type["Nested"] === None, numberOfParameters, Length[type["Nested"]["Parameters"]]],
		"NumberOfFields" -> Length[constructor["FieldIds"]],
		"RightHandSide" -> makeLambda[
			firstRecursorContext,
			Join[parameterIds, motiveIds, minorIds, constructor["FieldIds"]],
			makeApplication[
				freeVariable[minorIds[[constructorIndex]]],
				Join[
					freeVariable /@ constructor["FieldIds"],
					inductionHypothesisValue[recursorConstants[[#["Target"]]], parameterIds, motiveIds, minorIds, #] & /@ constructor["RecursiveFields"]
				]
			]
		]
	|>

buildInductiveRecord[checkedConstructors_, universeParameters_, numberOfParameters_, largeElimination_, names_, type_] := Block[
	{ownedInductiveConstructors = Select[checkedConstructors, #["Owner"] === type["Name"] &]},
	type["Name"] -> <|
		"Kind" -> "InductiveType",
		"Type" -> type["Type"],
		"UniverseParameters" -> universeParameters,
		"NumberOfParameters" -> numberOfParameters,
		"NumberOfIndices" -> Length[type["IndexIds"]],
		"Constructors" -> Lookup[ownedInductiveConstructors, "Name", {}],
		"LargeElimination" -> largeElimination,
		"Recursive" -> AnyTrue[ownedInductiveConstructors, #["RecursiveFields"] =!= {} &],
		"Block" -> names
	|>
]

buildConstructorRecords[environment_, checkedConstructors_, universeParameters_, numberOfParameters_, type_] := MapIndexed[
	#1["Name"] -> <|
		"Kind" -> "Constructor",
		"Type" -> If[rulesSetting[environment, "Quantities"], erasedParameters[#1["Type"], numberOfParameters], #1["Type"]],
		"UniverseParameters" -> universeParameters,
		"InductiveType" -> type["Name"],
		"ConstructorIndex" -> First[#2],
		"NumberOfParameters" -> numberOfParameters,
		"NumberOfFields" -> Length[#1["FieldIds"]]
	|> &,
	Select[checkedConstructors, #["Owner"] === type["Name"] &]
]

buildRecursorRecord[blockTypes_, checkedConstructors_, recursorUniverseParameters_, numberOfParameters_, largeElimination_, resultLevel_, type_, recursorConstant_, recursorType_, typeRules_] :=
	First[recursorConstant] -> <|
		"Kind" -> "Recursor",
		"Type" -> recursorType,
		"UniverseParameters" -> recursorUniverseParameters,
		"InductiveType" -> If[type["Nested"] === None, type["Name"], type["Nested"]["Inductive"]],
		"NumberOfParameters" -> numberOfParameters,
		"NumberOfMotives" -> Length[blockTypes],
		"NumberOfIndices" -> Length[type["IndexIds"]],
		"NumberOfMinors" -> Length[checkedConstructors],
		"Rules" -> typeRules,
		"EliminationUniverse" -> largeElimination,
		"KLike" -> And[
			Length[blockTypes] == 1,
			levelEquivalentQ[resultLevel, 0],
			Length[checkedConstructors] == 1,
			AllTrue[checkedConstructors, #["FieldIds"] === {} &]
		]
	|>

(* with quantities, a constructor's parameters are erased: the value it builds does not hold them *)
erasedParameters[dependentFunctionType[name_, domain_, codomain_, binder_], count_Integer?Positive] :=
	Construct[dependentFunctionType, name, domain, erasedParameters[codomain, count - 1], quantifiedBinder[binderKind[binder], 0]]
erasedParameters[type_, _] := type

ownerPosition[blockTypes_, constructor_] := First[FirstPosition[Lookup[blockTypes, "Name"], Verbatim[constructor["Owner"]], {0}, {1}, Heads -> False]]

(* the induction hypotheses of a constructor, one per recursive field: (ys) -> motive_k indices (field ys),
   with the motive of the type the field ends in *)
inductionHypothesisContext[context_, motiveIds_, constructor_, constructorIhIds_] := Fold[
	addInductionHypothesis[motiveIds, #1, First[#2], Last[#2]] &,
	context,
	Transpose[{constructor["RecursiveFields"], constructorIhIds}]
]

addInductionHypothesis[motiveIds_, accumulated_, recursive_, ihId_] := extendContext[
	accumulated,
	ihId,
	HoldComplete[h],
	makeDependentFunctionType[
		Join[accumulated, recursive["Context"]],
		recursive["Binders"],
		makeApplication[freeVariable[motiveIds[[recursive["Target"]]]], Append[recursive["Indices"], makeApplication[freeVariable[recursive["Id"]], freeVariable /@ recursive["Binders"]]]]
	],
	"Explicit"
]

inductionHypothesisValue[recursorConstant_, parameterIds_, motiveIds_, minorIds_, recursive_] := makeLambda[
	recursive["Context"],
	recursive["Binders"],
	makeApplication[
		recursorConstant,
		Join[
			freeVariable /@ parameterIds,
			freeVariable /@ motiveIds,
			freeVariable /@ minorIds,
			recursive["Indices"],
			{makeApplication[freeVariable[recursive["Id"]], freeVariable /@ recursive["Binders"]]}
		]
	]
]
