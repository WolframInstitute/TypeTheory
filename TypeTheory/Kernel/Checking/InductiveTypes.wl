(* ::Package:: *)

(*
Declaring inductive types: checking them and generating their recursors.

The types I_1, ..., I_n of a block are declared together, and are mutually inductive when there are
several: each constructor ends in one of them, and its fields may mention any of them. They share their
parameters and their universe: each I_j has type (parameters) -> (indices_j) -> Sort level, and each
constructor has type (parameters) -> (fields) -> I_j parameters indices'. The checks are those of Lean 4's
kernel:

	- the type of each I_j, and of each constructor, is a type, and the I_j agree on parameters and level;
	- each constructor takes exactly the parameters first and ends in a type of the block applied to them;
	- the block occurs strictly positively: in a field's type only as the result, I_k parameters indices,
	  after binders that do not mention it, with indices that do not either;
	- unless the block is a proposition, each field lives in a universe no larger than the block's.

A field may also mention the block nested in the parameters of another inductive type J, as a tree whose
children are a list of trees. As Lean's kernel does, each such occurrence J ps becomes an auxiliary type
of the block, whose constructors are J's for the parameters ps, so the block is checked as a mutual one.
Its recursors are generated with the auxiliary types, and then J ps takes each one's place again.

Each I_j gets the recursor InductiveRecursor[I_j], and each auxiliary type the recursor
InductiveRecursor[I_1, k], as Lean names it I_1.rec_k. A recursor's arguments are the parameters
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


typeTelescope[environment_, context_, type_] := telescopeFrom[environment, context, {}, weakHeadNormalForm[environment, context, type]]

telescopeFrom[environment_, context_, ids_List, dependentFunctionType[name_, domain_, codomain_, binder_]] := With[{id = freshFreeVariable[]},
	With[{extended = extendContext[context, id, name, domain, binder]},
		telescopeFrom[environment, extended, Append[ids, id], weakHeadNormalForm[environment, extended, instantiateBoundVariable[codomain, freeVariable[id]]]]
	]
]
telescopeFrom[_, context_, ids_List, rest_] := {context, ids, rest}


recursorName[HoldComplete[name_]] := HoldComplete[InductiveRecursor[name]]

auxiliaryRecursorName[HoldComplete[name_], index_Integer] := HoldComplete[InductiveRecursor[name, index]]

occursQ[term_, names_List] := ! FreeQ[term, constantReference[Alternatives @@ names, _]]

looseBoundVariablesQ[term_] := liftBoundVariables[term, 1, 0] =!= term


declareInductiveType[environment_, name_HoldComplete, universeParameters_List, numberOfParameters_Integer, type_, constructors_List] :=
	declareInductiveTypes[environment, universeParameters, numberOfParameters, {name -> type}, constructors]

declareInductiveTypes[environment_, universeParameters_List, numberOfParameters_Integer, types : {(_HoldComplete -> _) ..}, constructors_List] :=
	withCheckedTerms[declareBlock[environment, universeParameters, numberOfParameters, types, constructors]]

declareBlock[environment_, universeParameters_List, numberOfParameters_Integer, types_List, constructors_List] := Module[
	{
		names = Keys[types], levels = levelParameter /@ universeParameters, typeContext, parameterIds, originals, provisional,
		originalConstructors, blockConstructors, auxiliaries, blockTypes, resultLevel, checkedProvisional, checkedConstructors
	},
	checkUniverseParameters[First[names], universeParameters, Join[Values[types], Values[constructors]]];
	If[ ! DuplicateFreeQ[Join[names, recursorName /@ names, Keys[constructors]]],
		kernelFailure["DuplicateConstructor", "The constructors of `1` must have distinct names, different from the types and their recursors.", {HoldForm @@ First[names]}]
	];
	Scan[Function[type, sortLevel[environment, <||>, type]], Values[types]];
	{typeContext, parameterIds} = blockParameters[environment, First[types], numberOfParameters];
	originals = Function[entry, blockType[environment, typeContext, parameterIds, First[entry], Last[entry], constantReference[First[entry], levels], None]] /@ types;
	(* the constructor types may mention the types being declared *)
	provisional = addConstantRecords[environment, Association[Function[type, type["Name"] -> provisionalRecord[type, universeParameters, numberOfParameters]] /@ originals]];
	(* the constructors of the first type come first, then the second's, and so on, each in the order given *)
	originalConstructors = With[{owned = Function[constructor, originalConstructor[provisional, typeContext, parameterIds, originals, constructor]] /@ constructors},
		Catenate[Function[name, Select[owned, Function[constructor, constructor["Owner"] === name]]] /@ names]
	];
	{blockConstructors, auxiliaries} = eliminateNested[environment, universeParameters, typeContext, parameterIds, names, originalConstructors];
	blockTypes = Join[
		originals,
		Function[auxiliary, blockType[provisional, typeContext, parameterIds, auxiliary["Name"], auxiliary["Type"], constantReference[auxiliary["Name"], levels], auxiliary]] /@ auxiliaries
	];
	resultLevel = blockLevel[names, blockTypes];
	checkedProvisional = addConstantRecords[provisional, Association[Function[type, type["Name"] -> provisionalRecord[type, universeParameters, numberOfParameters]] /@ Drop[blockTypes, Length[names]]]];
	checkedConstructors = Function[constructor,
		checkConstructor[checkedProvisional, typeContext, parameterIds, blockTypes, resultLevel, constructor]
	] /@ blockConstructors;
	(* a recursive field's sort mentions the types themselves, as Acc's does, so they must be declared to find it *)
	addBlockRecords[
		environment, universeParameters, numberOfParameters, typeContext, parameterIds, names, blockTypes, resultLevel, checkedConstructors,
		largeEliminationQ[checkedProvisional, resultLevel, blockTypes, checkedConstructors]
	]
]


(* ::Subsection:: *)
(*Types*)


(* the parameters are the first type's leading binders, which every type of the block shares *)
blockParameters[environment_, name_ -> type_, numberOfParameters_Integer] := Module[{typeContext, binderIds, resultType},
	{typeContext, binderIds, resultType} = typeTelescope[environment, <||>, type];
	If[ Length[binderIds] < numberOfParameters,
		kernelFailure["InductiveParameters", "The type of `1` has fewer than `2` binders for its parameters.", {HoldForm @@ name, numberOfParameters}]
	];
	{KeyTake[typeContext, Take[binderIds, numberOfParameters]], Take[binderIds, numberOfParameters]}
]

blockType[environment_, typeContext_, parameterIds_, name_, type_, constant_, nested_] := Module[{afterParameters, context, indexIds, result},
	afterParameters = Fold[
		Function[{remaining, parameterId}, instantiateLeadingParameter[environment, typeContext, remaining, parameterId, Function[
			kernelFailure["InductiveParameters", "The types of a block must take the same parameters first, and `1` does not.", {HoldForm @@ name}]
		]]],
		type,
		parameterIds
	];
	{context, indexIds, result} = typeTelescope[environment, typeContext, afterParameters];
	<|
		"Name" -> name,
		"Type" -> type,
		"Constant" -> constant,
		"IndexIds" -> indexIds,
		"Context" -> context,
		"Level" -> Replace[result, {
			universeSort[level_] :> level,
			_ :> kernelFailure["InductiveTypeSort", "The type of an inductive type must end in a sort.", {}]
		}],
		"Nested" -> nested
	|>
]

(* a leading binder takes the parameter's place when their types agree; both are binder types of the block's
   types, checked first in declareBlock, or of the auxiliary types built from them *)
instantiateLeadingParameter[environment_, typeContext_, remaining_, parameterId_, failure_] := Replace[
	weakHeadNormalForm[environment, typeContext, remaining],
	{
		dependentFunctionType[_, domain_, codomain_, _] /; definitionallyEqualQ[environment, typeContext, domain, typeContext[parameterId]["Type"]] :>
			instantiateBoundVariable[codomain, freeVariable[parameterId]],
		_ :> failure[]
	}
]

blockLevel[names_, blockTypes_] := With[{level = First[blockTypes]["Level"]},
	If[ ! AllTrue[blockTypes, Function[type, levelEquivalentQ[type["Level"], level]]],
		kernelFailure["InductiveUniverse", "The types of the block of `1` must live in the same universe.", {HoldForm @@ First[names]}]
	];
	level
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
originalConstructor[environment_, typeContext_, parameterIds_, originals_, constructorName_ -> constructorType_] := Module[
	{afterParameters, conclusion, owner},
	sortLevel[environment, <||>, constructorType];
	afterParameters = Fold[
		Function[{remaining, parameterId}, instantiateLeadingParameter[environment, typeContext, remaining, parameterId, Function[
			kernelFailure["ConstructorParameters", "The constructor `1` must take the parameters of its type first.", {HoldForm @@ constructorName}]
		]]],
		constructorType,
		parameterIds
	];
	conclusion = Last @ typeTelescope[environment, typeContext, afterParameters];
	owner = SelectFirst[originals, Function[type, First[applicationSpine[conclusion]] === type["Constant"]], None];
	If[ owner === None,
		kernelFailure[
			"ConstructorResult",
			"The constructor `1` must end in `2` applied to its parameters and indices.",
			{HoldForm @@ constructorName, If[Length[originals] == 1, HoldForm @@ First[originals]["Name"], Function[name, HoldForm @@ name] /@ Lookup[originals, "Name"]]}
		]
	];
	<|"Name" -> constructorName, "Type" -> constructorType, "Owner" -> owner["Name"], "AfterParameters" -> afterParameters, "Original" -> None|>
]

checkConstructor[environment_, typeContext_, parameterIds_, blockTypes_, resultLevel_, constructor_] := Module[
	{
		names = Lookup[blockTypes, "Name"], owner = SelectFirst[blockTypes, Function[type, type["Name"] === constructor["Owner"]]],
		fieldContext, fieldIds, conclusion, conclusionHead, conclusionArguments, conclusionIndices, recursiveFields
	},
	sortLevel[environment, typeContext, constructor["AfterParameters"]];
	{fieldContext, fieldIds, conclusion} = typeTelescope[environment, typeContext, constructor["AfterParameters"]];
	{conclusionHead, conclusionArguments} = applicationSpine[conclusion];
	If[ conclusionHead =!= owner["Constant"] || Length[conclusionArguments] =!= Length[parameterIds] + Length[owner["IndexIds"]],
		kernelFailure["ConstructorResult", "The constructor `1` must end in `2` applied to its parameters and indices.", {HoldForm @@ displayedConstructorName[constructor], HoldForm @@ displayedOwner[blockTypes, constructor]}]
	];
	If[ Take[conclusionArguments, Length[parameterIds]] =!= (freeVariable /@ parameterIds),
		kernelFailure["ConstructorParameters", "The constructor `1` must end in `2` applied to the same parameters.", {HoldForm @@ displayedConstructorName[constructor], HoldForm @@ displayedOwner[blockTypes, constructor]}]
	];
	conclusionIndices = Drop[conclusionArguments, Length[parameterIds]];
	If[ occursQ[conclusionIndices, names],
		kernelFailure["NonPositiveOccurrence", "`1` occurs in an index of the result of the constructor `2`.", {HoldForm @@ displayedOwner[blockTypes, constructor], HoldForm @@ displayedConstructorName[constructor]}]
	];
	recursiveFields = Flatten[
		Function[fieldId, recursiveFieldData[environment, fieldContext, blockTypes, parameterIds, constructor, fieldId]] /@ fieldIds
	];
	checkFieldUniverses[environment, fieldContext, fieldIds, resultLevel, displayedConstructorName[constructor]];
	<|
		constructor,
		"FieldIds" -> fieldIds,
		"FieldContext" -> fieldContext,
		"ConclusionIndices" -> conclusionIndices,
		"RecursiveFields" -> recursiveFields
	|>
]

(* an auxiliary type's constructor is named by the constructor of the nested type it stands for, and the
   type by the block's first *)
displayedConstructorName[constructor_] := Replace[constructor["Original"], None :> constructor["Name"]]

displayedOwner[blockTypes_, constructor_] := If[constructor["Original"] === None, constructor["Owner"], First[blockTypes]["Name"]]

(* A field is recursive when its type is (ys) -> I_k parameters indices with the block absent from the ys
   and the indices; it is non-recursive when the block does not occur at all; anything else is not
   strictly positive. *)
recursiveFieldData[environment_, fieldContext_, blockTypes_, parameterIds_, constructor_, fieldId_] := Module[
	{names = Lookup[blockTypes, "Name"], fieldType = fieldContext[fieldId]["Type"], innerContext, binderIds, result, resultHead, resultArguments, target},
	If[ ! occursQ[fieldType, names],
		{},
		{innerContext, binderIds, result} = typeTelescope[environment, fieldContext, fieldType];
		{resultHead, resultArguments} = applicationSpine[result];
		target = FirstPosition[Lookup[blockTypes, "Constant"], Verbatim[resultHead], {None}, {1}, Heads -> False];
		If[ Or[
				AnyTrue[binderIds, Function[id, occursQ[innerContext[id]["Type"], names]]],
				First[target] === None,
				Take[resultArguments, UpTo[Length[parameterIds]]] =!= (freeVariable /@ parameterIds),
				occursQ[Drop[resultArguments, Length[parameterIds]], names]
			],
			kernelFailure[
				"NonPositiveOccurrence",
				"`1` does not occur strictly positively in the constructor `2`.",
				{HoldForm @@ displayedOwner[blockTypes, constructor], HoldForm @@ displayedConstructorName[constructor]}
			],
			{<|"Id" -> fieldId, "Binders" -> binderIds, "Context" -> innerContext, "Indices" -> Drop[resultArguments, Length[parameterIds]], "Target" -> First[target]|>}
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
(*Nested occurrences*)


(* Each occurrence J ps of the block nested in the parameters ps of an inductive type J becomes an
   auxiliary type, the same one for the same J ps. The original constructors are taken first, then the
   constructors of each auxiliary type in turn, which may nest further: Lean's kernel numbers the
   auxiliary types in this order. *)
eliminateNested[environment_, universeParameters_, typeContext_, parameterIds_, names_, originalConstructors_] := Module[
	{auxiliaries = {}, replaceNested, replaceParts, nestedApplication, replaced, index = 1},
	replaceNested[term_] := Replace[applicationSpine[term], {
		{constantReference[inductive_, inductiveLevels_], arguments_} /; nestedOccurrenceQ[environment, names, inductive, arguments] :>
			nestedApplication[inductive, inductiveLevels, arguments],
		{head_, {}} :> replaceParts[head],
		{head_, arguments_} :> makeApplication[replaceParts[head], replaceNested /@ arguments]
	}];
	replaceParts[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_]] := Construct[head, name, replaceNested[domain], replaceNested[body], binder];
	replaceParts[localDefinition[name_, type_, value_, body_]] := Construct[localDefinition, name, replaceNested[type], replaceNested[value], replaceNested[body]];
	replaceParts[projection[structure_, fieldIndex_, structureTerm_]] := Construct[projection, structure, fieldIndex, replaceNested[structureTerm]];
	replaceParts[other_] := other;
	nestedApplication[inductive_, inductiveLevels_, arguments_] := Module[
		{numberOfNestedParameters = constantRecord[environment, inductive]["NumberOfParameters"], parameters, auxiliary},
		parameters = Take[arguments, numberOfNestedParameters];
		If[ occursQ[Drop[arguments, numberOfNestedParameters], names],
			kernelFailure["NonPositiveOccurrence", "`1` occurs in an index of the nested type `2`.", {HoldForm @@ First[names], HoldForm @@ inductive}]
		];
		If[ looseBoundVariablesQ[parameters],
			kernelFailure["NestedParameters", "The parameters of the nested type `1` must not depend on the fields of a constructor of `2`.", {HoldForm @@ inductive, HoldForm @@ First[names]}]
		];
		auxiliary = SelectFirst[auxiliaries, Function[candidate, candidate["Key"] === {inductive, inductiveLevels, parameters}], None];
		If[ auxiliary === None,
			If[ Length[auxiliaries] >= $maximumAuxiliaryTypes,
				kernelFailure["NestingTooDeep", "`1` is nested more than `2` times.", {HoldForm @@ First[names], $maximumAuxiliaryTypes}]
			];
			auxiliary = auxiliaryType[environment, typeContext, parameterIds, First[names], Length[auxiliaries] + 1, inductive, inductiveLevels, parameters];
			auxiliaries = Append[auxiliaries, auxiliary]
		];
		makeApplication[constantReference[auxiliary["Name"], levelParameter /@ universeParameters], Join[freeVariable /@ parameterIds, Drop[arguments, numberOfNestedParameters]]]
	];
	replaced = Function[constructor, Append[constructor, "AfterParameters" -> replaceNested[constructor["AfterParameters"]]]] /@ originalConstructors;
	While[ index <= Length[auxiliaries],
		auxiliaries[[index, "Constructors"]] = Function[constructor, Append[constructor, "AfterParameters" -> replaceNested[constructor["AfterParameters"]]]] /@ auxiliaries[[index, "Constructors"]];
		index++
	];
	{Join[replaced, Catenate[Lookup[auxiliaries, "Constructors", {}]]], auxiliaries}
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
auxiliaryType[environment_, typeContext_, parameterIds_, firstName_, index_, inductive_, inductiveLevels_, parameters_] := With[
	{record = constantRecord[environment, inductive], name = HoldComplete[nestedAuxiliary[firstName, index]]},
	<|
		"Key" -> {inductive, inductiveLevels, parameters},
		"Name" -> name,
		"Inductive" -> inductive,
		"Levels" -> inductiveLevels,
		"Parameters" -> parameters,
		"Type" -> makeDependentFunctionType[typeContext, parameterIds, instantiateParameters[record, inductiveLevels, record["Type"], parameters]],
		"Constructors" -> MapIndexed[
			Function[{constructor, position}, <|
				"Name" -> HoldComplete[nestedAuxiliary[firstName, index, First[position]]],
				"Type" -> None,
				"Owner" -> name,
				"AfterParameters" -> instantiateParameters[record, inductiveLevels, constantRecord[environment, constructor]["Type"], parameters],
				"Original" -> constructor
			|>],
			record["Constructors"]
		]
	|>
]

(* a type of J's or of its constructors, at J's levels and with J's parameters instantiated *)
instantiateParameters[record_, inductiveLevels_, type_, parameters_] := Fold[
	Function[{remaining, parameter}, Replace[remaining, dependentFunctionType[_, _, codomain_, _] :> instantiateBoundVariable[codomain, parameter]]],
	instantiateUniverseParameters[type, record["UniverseParameters"], inductiveLevels],
	parameters
]

(* once the recursors are generated, the nested type and its constructors take each auxiliary's place *)
restoreNested[blockTypes_, numberOfParameters_][term_] := Module[
	{auxiliaries = Select[blockTypes, Function[type, type["Nested"] =!= None]], restore, restoreParts},
	restore[subterm_] := Replace[applicationSpine[subterm], {
		{constantReference[name_, _], arguments_} /; MemberQ[Lookup[auxiliaries, "Name"], name] :> With[
			{nested = SelectFirst[auxiliaries, Function[type, type["Name"] === name]]["Nested"]},
			makeApplication[constantReference[nested["Inductive"], nested["Levels"]], Join[nested["Parameters"], restore /@ Drop[arguments, numberOfParameters]]]
		],
		{constantReference[HoldComplete[nestedAuxiliary[_, auxiliaryIndex_, constructorIndex_]], _], arguments_} :> With[
			{nested = auxiliaries[[auxiliaryIndex]]["Nested"]},
			makeApplication[
				constantReference[nested["Constructors"][[constructorIndex]]["Original"], nested["Levels"]],
				Join[nested["Parameters"], restore /@ Drop[arguments, numberOfParameters]]
			]
		],
		{head_, {}} :> restoreParts[head],
		{head_, arguments_} :> makeApplication[restoreParts[head], restore /@ arguments]
	}];
	restoreParts[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_]] := Construct[head, name, restore[domain], restore[body], binder];
	restoreParts[localDefinition[name_, type_, value_, body_]] := Construct[localDefinition, name, restore[type], restore[value], restore[body]];
	restoreParts[projection[structure_, fieldIndex_, structureTerm_]] := Construct[projection, structure, fieldIndex, restore[structureTerm]];
	restoreParts[other_] := other;
	restore[term]
]

restoredContext[restore_, context_Association] := Map[Function[entry, Append[entry, "Type" -> restore[entry["Type"]]]], context]


(* ::Subsection:: *)
(*Recursors*)


(* Lean's rule: a block that may be a proposition eliminates into any universe only if it is a single type
   with at most one constructor, whose fields are proofs or indices of its result *)
largeEliminationQ[environment_, resultLevel_, blockTypes_, checkedConstructors_List] := Which[
	levelNeverZeroQ[resultLevel],
		True,
	Length[blockTypes] > 1,
		False,
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

(* a single motive is m; the motives of a block are m1, m2, ... *)
motiveNames[1] := {HoldComplete[m]}
motiveNames[count_Integer] := Table[With[{motive = Symbol[Context[m] <> "m" <> ToString[index]]}, HoldComplete[motive]], {index, count}]

addBlockRecords[environment_, universeParameters_, numberOfParameters_, typeContext_, parameterIds_, names_, blockTypes_, resultLevel_, rawConstructors_, largeElimination_] := Module[
	{
		levels = levelParameter /@ universeParameters, restore, checkedConstructors, eliminationName, recursorUniverseParameters, eliminationLevel,
		recursorConstants, motiveIds, majorIds, majorTypes, majorContexts, motiveContext, minorIds, ihIds, minorContext, minorTypes,
		recursorContexts, recursorTypes, rules, inductiveRecords, constructorRecords, recursorRecords, extended, matchQuantity, matchBinder, premiseContext
	},
	restore = If[AllTrue[blockTypes, Function[type, type["Nested"] === None]], Identity, restoreNested[blockTypes, numberOfParameters]];
	(* the auxiliary types give way to the nested types before anything is built from the constructors *)
	checkedConstructors = Function[constructor, Join[constructor, <|
		"FieldContext" -> restoredContext[restore, constructor["FieldContext"]],
		"RecursiveFields" -> Function[recursive, Append[recursive, "Context" -> restoredContext[restore, recursive["Context"]]]] /@ constructor["RecursiveFields"],
		"Application" -> restore[makeApplication[constantReference[constructor["Name"], levels], freeVariable /@ Join[parameterIds, constructor["FieldIds"]]]]
	|>]] /@ rawConstructors;
	eliminationName = eliminationUniverseName[universeParameters];
	recursorUniverseParameters = If[largeElimination, Prepend[universeParameters, eliminationName], universeParameters];
	(* without Prop, the motive's universe is Type u, which is never Prop *)
	eliminationLevel = Which[
		! largeElimination, 0,
		rulesSetting[environment, "Prop"], levelParameter[eliminationName],
		True, normalizeLevel[levelSuccessor[levelParameter[eliminationName], 1]]
	];
	recursorConstants = MapIndexed[
		Function[{type, position}, constantReference[
			If[First[position] <= Length[names], recursorName[type["Name"]], auxiliaryRecursorName[First[names], First[position] - Length[names]]],
			levelParameter /@ recursorUniverseParameters
		]],
		blockTypes
	];
	motiveIds = Table[freshFreeVariable[], Length[blockTypes]];
	majorIds = Table[freshFreeVariable[], Length[blockTypes]];
	majorTypes = Function[type, restore[makeApplication[type["Constant"], freeVariable /@ Join[parameterIds, type["IndexIds"]]]]] /@ blockTypes;
	majorContexts = MapThread[
		Function[{type, majorId, majorType}, extendContext[restoredContext[restore, type["Context"]], majorId, HoldComplete[t], majorType, "Explicit"]],
		{blockTypes, majorIds, majorTypes}
	];
	motiveContext = Fold[
		Function[{context, entry}, extendContext[context, Sequence @@ entry, "Explicit"]],
		Join @@ Prepend[majorContexts, typeContext],
		MapThread[
			Function[{type, motiveId, majorId, majorContext, motiveName}, {
				motiveId,
				motiveName,
				makeDependentFunctionType[majorContext, Append[type["IndexIds"], majorId], universeSort[eliminationLevel]]
			}],
			{blockTypes, motiveIds, majorIds, majorContexts, motiveNames[Length[blockTypes]]}
		]
	];
	minorIds = Table[freshFreeVariable[], Length[checkedConstructors]];
	ihIds = Function[constructor, Table[freshFreeVariable[], Length[constructor["RecursiveFields"]]]] /@ checkedConstructors;
	minorContext = Fold[
		Function[{context, pair}, inductionHypothesisContext[context, motiveIds, Sequence @@ pair]],
		Join @@ Append[Function[constructor, constructor["FieldContext"]] /@ checkedConstructors, motiveContext],
		Transpose[{checkedConstructors, ihIds}]
	];
	(* with quantities, a match uses its argument once, unless it recurses; without them every quantity is Infinity *)
	matchQuantity = If[AnyTrue[checkedConstructors, Function[constructor, constructor["RecursiveFields"] =!= {}]], Infinity, 1];
	matchBinder = If[rulesSetting[environment, "Quantities"], quantifiedBinder["Explicit", matchQuantity], "Explicit"];
	premiseContext = Fold[
		Function[{context, fieldId}, With[{binder = context[fieldId]["Binder"]},
			Append[context, fieldId -> Append[context[fieldId], "Binder" -> quantifiedBinder[binderKind[binder], multiplyQuantities[matchQuantity, binderQuantity[binder]]]]]
		]],
		minorContext,
		Catenate[Lookup[checkedConstructors, "FieldIds"]]
	];
	minorTypes = MapThread[
		Function[{constructor, constructorIhIds},
			makeDependentFunctionType[premiseContext, Join[constructor["FieldIds"], constructorIhIds], makeApplication[
				freeVariable[motiveIds[[ownerPosition[blockTypes, constructor]]]],
				Append[constructor["ConclusionIndices"], constructor["Application"]]
			]]
		],
		{checkedConstructors, ihIds}
	];
	recursorContexts = MapThread[
		Function[{type, majorId},
			Fold[
				Function[{context, entry}, extendContext[context, First[entry], Last[entry]["Name"], Last[entry]["Type"], Last[entry]["Binder"]]],
				minorContext,
				Join[
					Function[id, {id, Append[minorContext[id], "Binder" -> erasedBinder[environment, "Implicit"]]}] /@ Join[parameterIds, type["IndexIds"]],
					Function[id, {id, Append[minorContext[id], "Binder" -> erasedBinder[environment, "Explicit"]]}] /@ motiveIds,
					MapThread[
						Function[{id, constructor, minorType}, {id, <|"Name" -> displayedConstructorName[constructor], "Type" -> minorType, "Binder" -> matchBinder|>}],
						{minorIds, checkedConstructors, minorTypes}
					],
					{{majorId, Append[minorContext[majorId], "Binder" -> matchBinder]}}
				]
			]
		],
		{blockTypes, majorIds}
	];
	recursorTypes = MapThread[
		Function[{type, motiveId, majorId, recursorContext},
			makeDependentFunctionType[
				recursorContext,
				Join[parameterIds, motiveIds, minorIds, type["IndexIds"], {majorId}],
				makeApplication[freeVariable[motiveId], freeVariable /@ Append[type["IndexIds"], majorId]]
			]
		],
		{blockTypes, motiveIds, majorIds, recursorContexts}
	];
	rules = MapIndexed[
		Function[{type, position}, Association @ Map[
			Function[constructorIndex, With[{constructor = checkedConstructors[[constructorIndex]]},
				displayedConstructorName[constructor] -> <|
					"NumberOfParameters" -> Replace[type["Nested"], {None -> numberOfParameters, nested_ :> Length[nested["Parameters"]]}],
					"NumberOfFields" -> Length[constructor["FieldIds"]],
					"RightHandSide" -> makeLambda[
						First[recursorContexts],
						Join[parameterIds, motiveIds, minorIds, constructor["FieldIds"]],
						makeApplication[
							freeVariable[minorIds[[constructorIndex]]],
							Join[
								freeVariable /@ constructor["FieldIds"],
								Function[recursive, inductionHypothesisValue[recursorConstants[[recursive["Target"]]], parameterIds, motiveIds, minorIds, recursive]] /@ constructor["RecursiveFields"]
							]
						]
					]
				|>
			]],
			Select[Range[Length[checkedConstructors]], Function[constructorIndex, ownerPosition[blockTypes, checkedConstructors[[constructorIndex]]] == First[position]]]
		]],
		blockTypes
	];
	inductiveRecords = Association[Function[type, With[{owned = Select[checkedConstructors, Function[constructor, constructor["Owner"] === type["Name"]]]},
		type["Name"] -> <|
			"Kind" -> "InductiveType",
			"Type" -> type["Type"],
			"UniverseParameters" -> universeParameters,
			"NumberOfParameters" -> numberOfParameters,
			"NumberOfIndices" -> Length[type["IndexIds"]],
			"Constructors" -> Lookup[owned, "Name", {}],
			"LargeElimination" -> largeElimination,
			"Recursive" -> AnyTrue[owned, Function[constructor, constructor["RecursiveFields"] =!= {}]],
			"Block" -> names
		|>
	]] /@ Take[blockTypes, Length[names]]];
	constructorRecords = Association[Catenate[Function[type, MapIndexed[
		Function[{constructor, position}, constructor["Name"] -> <|
			"Kind" -> "Constructor",
			"Type" -> If[rulesSetting[environment, "Quantities"], erasedParameters[constructor["Type"], numberOfParameters], constructor["Type"]],
			"UniverseParameters" -> universeParameters,
			"InductiveType" -> type["Name"],
			"ConstructorIndex" -> First[position],
			"NumberOfParameters" -> numberOfParameters,
			"NumberOfFields" -> Length[constructor["FieldIds"]]
		|>],
		Select[checkedConstructors, Function[constructor, constructor["Owner"] === type["Name"]]]
	]] /@ Take[blockTypes, Length[names]]]];
	recursorRecords = Association @ MapThread[
		Function[{type, recursorConstant, recursorType, typeRules}, First[recursorConstant] -> <|
			"Kind" -> "Recursor",
			"Type" -> recursorType,
			"UniverseParameters" -> recursorUniverseParameters,
			"InductiveType" -> Replace[type["Nested"], {None -> type["Name"], nested_ :> nested["Inductive"]}],
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
				AllTrue[checkedConstructors, Function[constructor, constructor["FieldIds"] === {}]]
			]
		|>],
		{blockTypes, recursorConstants, recursorTypes, rules}
	];
	extended = addConstantRecords[environment, Join[inductiveRecords, constructorRecords, recursorRecords]];
	(* the generated recursors and rules are checked like any other term, by the compiled kernel when it checks a batch *)
	If[ ! $deferKernelChecks,
		Scan[Function[recursorType, sortLevel[extended, <||>, recursorType]], recursorTypes];
		Scan[Function[rule, inferType[extended, <||>, rule["RightHandSide"]]], Catenate[Values /@ rules]]
	];
	extended
]

(* with quantities, a constructor's parameters are erased: the value it builds does not hold them *)
erasedParameters[dependentFunctionType[name_, domain_, codomain_, binder_], count_Integer?Positive] :=
	Construct[dependentFunctionType, name, domain, erasedParameters[codomain, count - 1], quantifiedBinder[binderKind[binder], 0]]
erasedParameters[type_, _] := type

ownerPosition[blockTypes_, constructor_] := First[FirstPosition[Lookup[blockTypes, "Name"], Verbatim[constructor["Owner"]], {0}, {1}, Heads -> False]]

(* the induction hypotheses of a constructor, one per recursive field: (ys) -> motive_k indices (field ys),
   with the motive of the type the field ends in *)
inductionHypothesisContext[context_, motiveIds_, constructor_, constructorIhIds_] := Fold[
	Function[{accumulated, pair}, With[{recursive = First[pair], ihId = Last[pair]},
		extendContext[accumulated, ihId, HoldComplete[h], makeDependentFunctionType[
			Join[accumulated, recursive["Context"]],
			recursive["Binders"],
			makeApplication[freeVariable[motiveIds[[recursive["Target"]]]], Append[recursive["Indices"], makeApplication[freeVariable[recursive["Id"]], freeVariable /@ recursive["Binders"]]]]
		], "Explicit"]
	]],
	context,
	Transpose[{constructor["RecursiveFields"], constructorIhIds}]
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
