(* ::Package:: *)

(*
Cubical type theory, after Cohen, Coquand, Huber and Mörtberg: a path is a function from an interval, and
univalence is a theorem that computes. TypeTheoryCubical[sum] declares its primitives where the rules have
"Cubical", which excludes Prop:

	Interval                                    the interval, a pretype: it is no type of a universe, and only a
	                                            function or a path type may take an element of it
	IntervalZero, IntervalOne                   its endpoints
	IntervalMeet[r, s], IntervalJoin[r, s], IntervalReverse[r]
	                                            r ∧ s, r ∨ s and ~r: the interval is a De Morgan algebra
	Path[A, a, b]                               the paths over a line of types A, a function from Interval into a
	                                            universe, from a : A[0] to b : A[1]
	CubicalTransport[A, φ, a]                   a : A[0] carried along the line A to A[1]; A must be constant where
	                                            the face φ holds, and there the transport is a
	CubicalComposition[A, Function[{i}, system], a]
	                                            the lid of an open box in the type A: its base is a, and the system
	                                            gives its sides, each a line in A over a face

A path is a function of an element of Interval, whose values at IntervalZero and IntervalOne are its
endpoints: the kernel checks a function of the interval against a path type by its values there, and a
path that is no function, applied to an endpoint, computes to that endpoint of its type. An element of the
interval is a variable, an endpoint or an operation on them, and two are equal when their normal forms,
irredundant disjunctions of conjunctions of variables and reversed variables, are.

A face is an element of the interval read as the condition that it is 1: the variable i is the face where i
is 1, IntervalReverse[i] the face where i is 0, a meet both, a join either. A conjunction that asks a
variable to be both 0 and 1 is empty. A system, the core term cubicalSystem[{{face, term}, ...}], is a
partial element: each term is checked with each conjunction of its face substituted into it, its type and
its context, and any two terms agree where both faces hold. A system has no type of its own; it is only
the side of a composition.

Transport and composition compute by the type they are in, as in cubical type theory: transport is the
identity where its face holds, and in a universe or an inductive type with no parameters and no indices;
in a function type and a path type, and composition in a function type and a path type, it is built from
transport and composition in the parts. Composition is the side its system gives at IntervalOne where a
face holds. Where no rule applies the term does not compute, which costs canonicity and never consistency:
every rule is one of cubical type theory.

declareCubical, the typing of the primitives and their reductions are part of the trusted kernel.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryCubical]
PackageExported[IntervalZero]
PackageExported[IntervalOne]
PackageExported[IntervalMeet]
PackageExported[IntervalJoin]
PackageExported[IntervalReverse]
PackageExported[CubicalTransport]
PackageExported[CubicalComposition]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[declareCubical]
PackageScoped[cubicalDeclaredQ]
PackageScoped[cubicalRole]
PackageScoped[intervalTypeQ]
PackageScoped[intervalEqualQ]
PackageScoped[intervalForm]
PackageScoped[faceConjunctions]
PackageScoped[cubicalApplicationType]
PackageScoped[cubicalConstantType]
PackageScoped[pathApplicationType]
PackageScoped[cubicalFitQ]
PackageScoped[reduceCubical]
PackageScoped[reducePathEndpoint]
PackageScoped[systemsEqualQ]
PackageScoped[checkIntervalDomain]
PackageScoped[pathTypeArguments]
PackageScoped[intervalLambdaType]
PackageScoped[restrictedTerm]
PackageScoped[$cubicalNames]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryCubical::usage = "TypeTheoryCubical[sum] declares the primitives of cubical type theory, when added to a TypeTheoryEnvironment whose rules \
are cubical: Interval, its endpoints IntervalZero and IntervalOne, IntervalMeet, IntervalJoin and IntervalReverse, the type Path[A, a, b] of paths over \
a line of types A, CubicalTransport and CubicalComposition. sum is the dependent sum type the environment declares, which Glue types use."
IntervalZero::usage = "IntervalZero is the endpoint 0 of the Interval of cubical type theory; 0 stands for it where an element of the interval is expected."
IntervalOne::usage = "IntervalOne is the endpoint 1 of the Interval of cubical type theory; 1 stands for it where an element of the interval is expected."
IntervalMeet::usage = "IntervalMeet[r, s] is r ∧ s, the meet of two elements of the Interval of cubical type theory; Min[r, s] stands for it."
IntervalJoin::usage = "IntervalJoin[r, s] is r ∨ s, the join of two elements of the Interval of cubical type theory; Max[r, s] stands for it."
IntervalReverse::usage = "IntervalReverse[r] is ~r, the reversal of an element of the Interval of cubical type theory, which takes 0 to 1; 1 - r stands for it."
CubicalTransport::usage = "CubicalTransport[A, φ, a] carries a, an element of A[0], along the line of types A, a function from the Interval into a universe, \
to an element of A[1]. A must be constant where the face φ holds, and there the transport is a."
CubicalComposition::usage = "CubicalComposition[A, Function[{i}, {face -> u, ...}], a] composes in the type A: it gives the lid of the open box whose base \
is a and whose sides are the lines u, over the faces, which must be a at i = 0. Where a face holds, it is that side at i = 1."

declareCubical::usage = "declareCubical[environment, HoldComplete[sum]] checks that the rules of environment are cubical and gives environment with the \
primitives of cubical type theory declared; it throws a kernel failure otherwise."
cubicalDeclaredQ::usage = "cubicalDeclaredQ[environment] gives True if environment has the primitives of cubical type theory."
cubicalRole::usage = "cubicalRole[environment, HoldComplete[name]] gives the role of name among the primitives of cubical type theory, such as \"Path\", or None."
intervalTypeQ::usage = "intervalTypeQ[environment, term] gives True if term is the Interval of cubical type theory."
intervalEqualQ::usage = "intervalEqualQ[environment, context, a, b] gives True if a and b are elements of the interval with the same normal form."
intervalForm::usage = "intervalForm[environment, context, term] gives the normal form of an element of the interval: a list of conjunctions, each a sorted \
list of literals {id, True} for a variable and {id, False} for its reversal; {} is 0 and {{}} is 1. It gives None for a term that is no element of the interval."
faceConjunctions::usage = "faceConjunctions[environment, context, face] gives the conjunctions of the face as substitutions <|id -> endpoint, ...|>, \
leaving out those that ask a variable to be both 0 and 1; it throws a kernel failure if face is no element of the interval."
cubicalApplicationType::usage = "cubicalApplicationType[environment, context, record, arguments] gives the type of a primitive of cubical type theory applied \
to the arguments, checking them by its own rules, or None if the primitive takes its arguments as its type says."
cubicalConstantType::usage = "cubicalConstantType[environment, record, type] gives the type of a primitive of cubical type theory on its own, or throws a \
kernel failure for one that must be applied to all its arguments."
pathApplicationType::usage = "pathApplicationType[environment, context, type, argument] gives the type of a path of type type applied to an element of the \
interval, or None if type is no path type."
cubicalFitQ::usage = "cubicalFitQ[environment, context, term, actual, expected] gives True if term, of the type actual, has the type expected by the rules of \
paths: a function of the interval is a path with its values at the endpoints, and a path is a function of the interval."
reduceCubical::usage = "reduceCubical[environment, context, term, record, levels, arguments] gives term, a primitive of cubical type theory applied to \
arguments, reduced one step where it computes, and term otherwise."
reducePathEndpoint::usage = "reducePathEndpoint[environment, context, term, head, arguments] gives term, head applied to arguments, with a path that is no \
function applied to an endpoint replaced by that endpoint of its type, or term if there is none."
systemsEqualQ::usage = "systemsEqualQ[environment, context, first, second] gives True if the two systems have the same faces, in order, and terms equal \
where their faces hold."
checkIntervalDomain::usage = "checkIntervalDomain[environment, context, domain] checks that domain, the domain of a function, is a type or the interval."
pathTypeArguments::usage = "pathTypeArguments[environment, type] gives {line, left, right} for a path type Path[line, left, right], or None."
intervalLambdaType::usage = "intervalLambdaType[environment, bodyContext, id, name, domain, body, bodyType] gives the path type of a function of the interval, \
Path[Function[{i}, bodyType], body at 0, body at 1], where bodyType, the type of the body at the variable id, is a type of a universe; None otherwise."
restrictedTerm::usage = "restrictedTerm[term, substitution] gives term restricted to a conjunction of a face: each interval variable of the substitution \
<|id -> endpoint, ...|> replaced by its endpoint."
$cubicalNames::usage = "$cubicalNames gives the name of each primitive of cubical type theory by its role."


(* ::Section:: *)
(*Function Definitions*)


(* ::Subsection:: *)
(*Declaration*)


$cubicalNames = <|
	"Interval" -> HoldComplete[Interval],
	"Zero" -> HoldComplete[IntervalZero],
	"One" -> HoldComplete[IntervalOne],
	"Meet" -> HoldComplete[IntervalMeet],
	"Join" -> HoldComplete[IntervalJoin],
	"Reverse" -> HoldComplete[IntervalReverse],
	"Path" -> HoldComplete[Path],
	"Transport" -> HoldComplete[CubicalTransport],
	"Composition" -> HoldComplete[CubicalComposition]
|>

(* the arguments a primitive must have before it is a term: those with rules of their own *)
$saturatedArity = <|"Transport" -> 3, "Composition" -> 3|>

declareCubical[environment_, sum_HoldComplete] := withKernelCaches[
	If[ ! TrueQ[rulesSetting[environment, "Cubical"]] || TrueQ[rulesSetting[environment, "Prop"]],
		kernelFailure["CubicalNotAllowed", "The rules of the environment are not cubical: they need \"Cubical\" -> True and no Prop.", {}]
	];
	If[ ! constantDeclaredQ[environment, sum] || ! structureLikeQ[environment, sum],
		kernelFailure["SumExpected", "TypeTheoryCubical needs `1` declared as a dependent sum, a structure of a type and a family over it.", {HoldForm @@ sum}]
	];
	Scan[
		Function[name, If[constantDeclaredQ[environment, name], kernelFailure["AlreadyDeclared", "`1` is already declared.", {HoldForm @@ name}]]],
		Values[$cubicalNames]
	];
	addConstantRecords[environment, Association @ KeyValueMap[
		Function[{role, name}, name -> <|
			"Kind" -> "Cubical",
			"CubicalRole" -> role,
			"Type" -> cubicalType[role],
			"UniverseParameters" -> If[MemberQ[{"Path", "Transport", "Composition"}, role], {HoldComplete[u]}, {}],
			"Sum" -> sum
		|>],
		$cubicalNames
	]]
]

cubicalDeclaredQ[environment_] := TrueQ[rulesSetting[environment, "Cubical"]] && cubicalRole[environment, HoldComplete[Interval]] === "Interval"

cubicalRole[environment_, name_HoldComplete] := If[ constantDeclaredQ[environment, name],
	Replace[constantRecord[environment, name], {record : KeyValuePattern["Kind" -> "Cubical"] :> record["CubicalRole"], _ -> None}],
	None
]

intervalTypeQ[environment_, constantReference[name_, {}]] := cubicalRole[environment, name] === "Interval"
intervalTypeQ[_, _] := False

cubicalConstant[role_String] := constantReference[$cubicalNames[role], {}]
cubicalConstant[role_String, level_] := constantReference[$cubicalNames[role], {level}]

$interval := cubicalConstant["Interval"]
$intervalZero := cubicalConstant["Zero"]
$intervalOne := cubicalConstant["One"]

intervalMeet[r_, s_] := makeApplication[cubicalConstant["Meet"], {r, s}]
intervalJoin[r_, s_] := makeApplication[cubicalConstant["Join"], {r, s}]
intervalReverse[r_] := application[cubicalConstant["Reverse"], r]

(* the types of the primitives, written with bound variables counted from the innermost binder; each comment
   gives the type as a term would write it, the universe parameter u a sort level *)
cubicalType["Interval"] := intervalUniverse[]
cubicalType["Zero" | "One"] := $interval
cubicalType["Meet" | "Join"] := dependentFunctionType[HoldComplete[r], $interval, dependentFunctionType[HoldComplete[s], $interval, $interval, "Explicit"], "Explicit"]
cubicalType["Reverse"] := dependentFunctionType[HoldComplete[r], $interval, $interval, "Explicit"]
(* ForAll[{Typed[A, ForAll[{Typed[i, Interval]}, Sort u]], Typed[a, A[0]], Typed[b, A[1]]}, Sort u] *)
cubicalType["Path"] := dependentFunctionType[HoldComplete[A], lineType[],
	dependentFunctionType[HoldComplete[a], application[boundVariable[0], $intervalZero],
		dependentFunctionType[HoldComplete[b], application[boundVariable[1], $intervalOne], universeSort[levelParameter[HoldComplete[u]]], "Explicit"],
		"Explicit"
	],
	"Explicit"
]
(* ForAll[{Typed[A, ForAll[{Typed[i, Interval]}, Sort u]], Typed[φ, Interval], Typed[a, A[0]]}, A[1]] *)
cubicalType["Transport"] := dependentFunctionType[HoldComplete[A], lineType[],
	dependentFunctionType[HoldComplete[\[Phi]], $interval,
		dependentFunctionType[HoldComplete[a], application[boundVariable[1], $intervalZero], application[boundVariable[2], $intervalOne], "Explicit"],
		"Explicit"
	],
	"Explicit"
]
(* ForAll[{Typed[A, Sort u], Typed[tube, ForAll[{Typed[i, Interval]}, A]], Typed[a, A]}, A]: the sides are a system, which the kernel checks itself *)
cubicalType["Composition"] := dependentFunctionType[HoldComplete[A], universeSort[levelParameter[HoldComplete[u]]],
	dependentFunctionType[HoldComplete[tube], dependentFunctionType[HoldComplete[i], $interval, boundVariable[1], "Explicit"],
		dependentFunctionType[HoldComplete[a], boundVariable[1], boundVariable[2], "Explicit"],
		"Explicit"
	],
	"Explicit"
]

lineType[] := dependentFunctionType[HoldComplete[i], $interval, universeSort[levelParameter[HoldComplete[u]]], "Explicit"]


(* ::Subsection:: *)
(*The interval*)


(* a domain is a type, or the interval, which only a function or a path may take *)
checkIntervalDomain[environment_, context_, domain_] := If[ intervalTypeQ[environment, domain] && cubicalDeclaredQ[environment],
	Null,
	sortLevel[environment, context, domain]
]

intervalVariableQ[environment_, context_, id_] := KeyExistsQ[context, id] && intervalTypeQ[environment, context[id]["Type"]]

intervalForm[environment_, context_, term_] := Replace[term, {
	freeVariable[id_] /; intervalVariableQ[environment, context, id] :> {{{id, True}}},
	_freeVariable -> None,
	_ :> Replace[applicationSpine[term], {
		{constantReference[name_, {}], arguments_List} :> Replace[cubicalRole[environment, name], {
			role : "Zero" | "One" | "Meet" | "Join" | "Reverse" :> operationForm[environment, context, role, arguments],
			_ -> None
		}],
		{_lambdaAbstraction | _localDefinition, _} :> With[{reduced = reducedHeadWithoutUnfolding[environment, context, term]},
			If[reduced === term, None, intervalForm[environment, context, reduced]]
		],
		_ -> None
	}]
}]

operationForm[_, _, "Zero", {}] := {}
operationForm[_, _, "One", {}] := {{}}
operationForm[environment_, context_, "Meet", {r_, s_}] := combinedForms[meetForms, intervalForm[environment, context, r], intervalForm[environment, context, s]]
operationForm[environment_, context_, "Join", {r_, s_}] := combinedForms[joinForms, intervalForm[environment, context, r], intervalForm[environment, context, s]]
operationForm[environment_, context_, "Reverse", {r_}] := Replace[intervalForm[environment, context, r], {None -> None, form_ :> reverseForm[form]}]
operationForm[_, _, _, _] := None

combinedForms[combine_, first_, second_] := If[first === None || second === None, None, combine[first, second]]

(* no conjunction contains another, so the form of an element is unique *)
irredundant[conjunctions_List] := With[{distinct = Union[Union /@ conjunctions]},
	Select[distinct, Function[conjunction, NoneTrue[distinct, Function[other, other =!= conjunction && SubsetQ[conjunction, other]]]]]
]

joinForms[first_, second_] := irredundant[Join[first, second]]
meetForms[first_, second_] := irredundant[Flatten[Outer[Union, first, second, 1], 1]]

(* ~(c1 ∨ c2 ∨ ...) is ~c1 ∧ ~c2 ∧ ..., and ~(l1 ∧ l2 ∧ ...) is ~l1 ∨ ~l2 ∨ ... *)
reverseForm[form_] := Fold[
	meetForms,
	{{}},
	Function[conjunction, Function[literal, {{First[literal], ! Last[literal]}}] /@ conjunction] /@ form
]

intervalEqualQ[environment_, context_, a_, b_] := With[{form = intervalForm[environment, context, a]},
	form =!= None && form === intervalForm[environment, context, b]
]

(* the canonical term of a form: a join of meets, each literal a variable or its reversal *)
intervalTerm[{}] := $intervalZero
intervalTerm[{{}}] := $intervalOne
intervalTerm[form_List] := Fold[intervalJoin, conjunctionTerm /@ form]
conjunctionTerm[conjunction_List] := Fold[intervalMeet, literalTerm /@ conjunction]
literalTerm[{id_, True}] := freeVariable[id]
literalTerm[{id_, False}] := intervalReverse[freeVariable[id]]


(* ::Subsection:: *)
(*Faces*)


faceConjunctions[environment_, context_, face_] := Replace[intervalForm[environment, context, face], {
	None :> kernelFailure["FaceExpected", "`1` is not a face, an element of the interval.", {displayCoreTerm[environment, context, face]}],
	form_ :> Association /@ Map[Function[literal, First[literal] -> If[Last[literal], $intervalOne, $intervalZero]], Select[form, consistentConjunctionQ], {2}]
}]

consistentConjunctionQ[conjunction_List] := DuplicateFreeQ[First /@ conjunction]

(* a face holds everywhere when one of its conjunctions asks nothing *)
faceTrueQ[environment_, context_, face_] := MemberQ[faceConjunctions[environment, context, face], <||>]

(* the restriction of a term, or a context, to a conjunction: its variables replaced by endpoints *)
restricted[term_, substitution_Association] := If[substitution === <||>, term, ReplaceAll[term, freeVariable[id_] /; KeyExistsQ[substitution, id] :> substitution[id]]]

restrictedTerm[term_, substitution_Association] := restricted[term, substitution]

restrictedContext[context_Association, substitution_Association] := If[ substitution === <||>,
	context,
	Map[Function[entry, Association @ KeyValueMap[Function[{key, value}, key -> If[MemberQ[{"Type", "Value"}, key], restricted[value, substitution], value]], entry]], context]
]

(* term and other are equal wherever face holds *)
equalUnderFaceQ[environment_, context_, face_, term_, other_] := AllTrue[
	faceConjunctions[environment, context, face],
	Function[substitution, definitionallyEqualQ[environment, restrictedContext[context, substitution], restricted[term, substitution], restricted[other, substitution]]]
]

checkUnderFace[environment_, context_, face_, term_, type_] := Scan[
	Function[substitution, checkHasType[environment, restrictedContext[context, substitution], restricted[term, substitution], restricted[type, substitution]]],
	faceConjunctions[environment, context, face]
]


(* ::Subsection:: *)
(*Systems*)


(* the branches of a tube, Function[{i}, system], opened with a fresh variable of the interval *)
openedTube[environment_, context_, lambdaAbstraction[name_, domain_, cubicalSystem[branches_List], _]] /; intervalTypeQ[environment, domain] := With[
	{id = freshFreeVariable[]},
	If[ AnyTrue[branches, Function[branch, boundVariableOccursQ[First[branch], 0]]],
		kernelFailure["FaceOfTube", "A face of a composition may not mention the variable of its sides.", {}]
	];
	<|
		"Id" -> id,
		"Context" -> extendContext[context, id, name, domain, "Explicit"],
		"Faces" -> Function[branch, instantiateBoundVariable[First[branch], $intervalZero]] /@ branches,
		"Sides" -> Function[branch, instantiateBoundVariable[Last[branch], freeVariable[id]]] /@ branches
	|>
]
openedTube[environment_, context_, tube_] :=
	kernelFailure["TubeExpected", "The sides of a composition must be a function of the interval whose body is a system, Function[{i}, {face -> u, ...}].", {}]

(* each side is a term of type where its face holds, and any two agree where both hold *)
checkSystem[environment_, context_, faces_List, sides_List, type_] := (
	Scan[Function[face, faceConjunctions[environment, context, face]], faces];
	MapThread[Function[{face, side}, checkUnderFace[environment, context, face, side, type]], {faces, sides}];
	Do[
		If[ ! equalUnderFaceQ[environment, context, intervalMeet[faces[[k]], faces[[l]]], sides[[k]], sides[[l]]],
			kernelFailure["SystemDisagreement", "Two sides of a system disagree where both their faces hold.", {}]
		],
		{k, Length[faces]},
		{l, k + 1, Length[faces]}
	]
)

systemsEqualQ[environment_, context_, cubicalSystem[first_List], cubicalSystem[second_List]] := And[
	Length[first] == Length[second],
	AllTrue[
		Transpose[{first, second}],
		Function[pair, And[
			intervalEqualQ[environment, context, First[First[pair]], First[Last[pair]]],
			equalUnderFaceQ[environment, context, First[First[pair]], Last[First[pair]], Last[Last[pair]]]
		]]
	]
]
systemsEqualQ[_, _, _, _] := False


(* ::Subsection:: *)
(*Typing*)


(* transport and composition must be applied to all the arguments their rules check *)
cubicalConstantType[environment_, record_, type_] := If[ KeyExistsQ[$saturatedArity, record["CubicalRole"]],
	kernelFailure["CubicalUnsaturated", "`1` must be applied to `2` arguments.", {HoldForm @@ $cubicalNames[record["CubicalRole"]], $saturatedArity[record["CubicalRole"]]}],
	type
]

cubicalApplicationType[environment_, context_, record_, levels_List, arguments_List] := With[{role = record["CubicalRole"]},
	If[ ! KeyExistsQ[$saturatedArity, role],
		None,
		If[ Length[arguments] < $saturatedArity[role],
			kernelFailure["CubicalUnsaturated", "`1` must be applied to `2` arguments.", {HoldForm @@ $cubicalNames[role], $saturatedArity[role]}]
		];
		Fold[
			Function[{type, argument}, applicationTypeOf[environment, context, type, argument]],
			saturatedType[environment, context, role, levels, Take[arguments, $saturatedArity[role]]],
			Drop[arguments, $saturatedArity[role]]
		]
	]
]

(* the type of a further argument's application, as for any function *)
applicationTypeOf[environment_, context_, type_, argument_] := Replace[weakHeadNormalForm[environment, context, type], {
	dependentFunctionType[_, domain_, codomain_, _] :> (checkHasType[environment, context, argument, domain]; instantiateBoundVariable[codomain, argument]),
	other_ :> Replace[pathApplicationType[environment, context, other, argument], None :> kernelFailure["FunctionExpected", "`1` is not a function type.", {displayCoreTerm[environment, context, other]}]]
}]

(* CubicalTransport[A, φ, a]: a line of types in a universe, a face where it is constant, and an element of A[0] *)
saturatedType[environment_, context_, "Transport", {level_}, {line_, face_, value_}] := (
	checkHasType[environment, context, line, lineOf[level]];
	checkHasType[environment, context, face, $interval];
	checkHasType[environment, context, value, application[line, $intervalZero]];
	Scan[
		Function[substitution, With[{id = freshFreeVariable[], restrictedLine = restricted[line, substitution]},
			If[ ! definitionallyEqualQ[
					environment,
					extendContext[restrictedContext[context, substitution], id, HoldComplete[i], $interval, "Explicit"],
					application[restrictedLine, freeVariable[id]],
					application[restrictedLine, $intervalZero]
				],
				kernelFailure["TransportNotConstant", "The line of a transport must be constant where its face holds.", {}]
			]
		]],
		faceConjunctions[environment, context, face]
	];
	application[line, $intervalOne]
)

(* CubicalComposition[A, Function[{i}, system], a]: the sides are lines in A over their faces, and are a at 0 *)
saturatedType[environment_, context_, "Composition", {level_}, {type_, tube_, cap_}] := With[{opened = openedTube[environment, context, tube]},
	checkHasType[environment, context, type, universeSort[level]];
	checkSystem[environment, opened["Context"], opened["Faces"], opened["Sides"], type];
	checkHasType[environment, context, cap, type];
	MapThread[
		Function[{face, side}, If[ ! equalUnderFaceQ[environment, context, face, restricted[side, <|opened["Id"] -> $intervalZero|>], cap],
			kernelFailure["CapMismatch", "A side of a composition must be its base at 0, where its face holds.", {}]
		]],
		{opened["Faces"], opened["Sides"]}
	];
	type
]

saturatedType[_, _, role_, _, _] := kernelFailure["CubicalUniverse", "`1` takes one universe level.", {HoldForm @@ $cubicalNames[role]}]

lineOf[level_] := dependentFunctionType[HoldComplete[i], $interval, universeSort[level], "Explicit"]

(* the endpoints are normalized, without unfolding definitions, so that a path between two variables reads as
   one: the value of a path at 0 is the start of its type, and a function that applies another to its
   argument is that function *)
intervalLambdaType[environment_, bodyContext_, id_, name_, domain_, body_, bodyType_] := If[ ! intervalTypeQ[environment, domain] || ! cubicalDeclaredQ[environment],
	None,
	Replace[weakHeadNormalForm[environment, bodyContext, inferType[environment, bodyContext, bodyType]], {
		universeSort[level_] :> With[{outerContext = KeyDrop[bodyContext, id]},
			makeApplication[cubicalConstant["Path", level], {
				lambdaAbstraction[name, $interval, abstractFreeVariable[bodyType, id], "Explicit"],
				normalizedTerm[environment, outerContext, instantiateBoundVariable[body, $intervalZero]],
				normalizedTerm[environment, outerContext, instantiateBoundVariable[body, $intervalOne]]
			}]
		],
		_ -> None
	}]
]

normalizedTerm[environment_, context_, term_] := With[{reduced = reducedHeadWithoutUnfolding[environment, context, term]},
	Replace[reduced, {
		lambdaAbstraction[name_, domain_, body_, binder_] :> With[{id = freshFreeVariable[]},
			etaContracted[lambdaAbstraction[
				name,
				normalizedTerm[environment, context, domain],
				abstractFreeVariable[normalizedTerm[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[body, freeVariable[id]]], id],
				binder
			]]
		],
		dependentFunctionType[name_, domain_, codomain_, binder_] :> With[{id = freshFreeVariable[]},
			dependentFunctionType[
				name,
				normalizedTerm[environment, context, domain],
				abstractFreeVariable[normalizedTerm[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[codomain, freeVariable[id]]], id],
				binder
			]
		],
		_application :> With[{spine = applicationSpine[reduced]},
			With[{rebuilt = makeApplication[First[spine], Function[argument, normalizedTerm[environment, context, argument]] /@ Last[spine]]},
				If[rebuilt === reduced, reduced, With[{again = reducedHeadWithoutUnfolding[environment, context, rebuilt]}, If[again === rebuilt, rebuilt, normalizedTerm[environment, context, again]]]]
			]
		],
		_ :> reduced
	}]
]

etaContracted[lambdaAbstraction[_, _, application[function_, boundVariable[0]], _]] /; ! boundVariableOccursQ[function, 0] := instantiateBoundVariable[function, $intervalZero]
etaContracted[term_] := term

pathTypeArguments[environment_, type_] := Replace[applicationSpine[type], {
	{constantReference[name_, {_}], {line_, left_, right_}} /; cubicalRole[environment, name] === "Path" :> {line, left, right},
	_ -> None
}]

(* a path applied to an element of the interval has the type of its line there *)
pathApplicationType[environment_, context_, type_, argument_] := If[ ! cubicalDeclaredQ[environment],
	None,
	Replace[pathTypeArguments[environment, type], {
		{line_, _, _} :> (checkHasType[environment, context, argument, $interval]; application[line, argument]),
		None -> None
	}]
]

(* a function of the interval with the right values at the endpoints is a path, and a path is a function of the interval *)
cubicalFitQ[environment_, context_, term_, actual_, expected_] := cubicalDeclaredQ[environment] && With[
	{actualForm = weakHeadNormalForm[environment, context, actual], expectedForm = weakHeadNormalForm[environment, context, expected]},
	Replace[{actualForm, pathTypeArguments[environment, expectedForm], expectedForm, pathTypeArguments[environment, actualForm]}, {
		{dependentFunctionType[name_, domain_, codomain_, _], {line_, left_, right_}, _, _} /; intervalTypeQ[environment, domain] :> With[{id = freshFreeVariable[]},
			And[
				definitionallyEqualQ[
					environment,
					extendContext[context, id, name, domain, "Explicit"],
					instantiateBoundVariable[codomain, freeVariable[id]],
					application[line, freeVariable[id]]
				],
				definitionallyEqualQ[environment, context, application[term, $intervalZero], left],
				definitionallyEqualQ[environment, context, application[term, $intervalOne], right]
			]
		],
		{_, _, dependentFunctionType[name_, domain_, codomain_, _], {line_, _, _}} /; intervalTypeQ[environment, domain] :> With[{id = freshFreeVariable[]},
			definitionallyEqualQ[
				environment,
				extendContext[context, id, name, domain, "Explicit"],
				application[line, freeVariable[id]],
				instantiateBoundVariable[codomain, freeVariable[id]]
			]
		],
		_ -> False
	}]
]


(* ::Subsection:: *)
(*Reduction*)


reduceCubical[environment_, context_, term_, record_, levels_, arguments_] := Replace[{record["CubicalRole"], arguments}, {
	{role : "Meet" | "Join" | "Reverse", {__}} :> canonicalInterval[environment, context, term],
	{"Transport", {line_, face_, value_, rest___}} :> Replace[
		transportReduction[environment, context, First[levels], line, face, value],
		{None :> term, reduced_ :> makeApplication[reduced, {rest}]}
	],
	{"Composition", {type_, tube_, cap_, rest___}} :> Replace[
		compositionReduction[environment, context, First[levels], type, tube, cap],
		{None :> term, reduced_ :> makeApplication[reduced, {rest}]}
	],
	_ :> term
}]

(* an operation on the interval is its canonical term *)
canonicalInterval[environment_, context_, term_] := Replace[intervalForm[environment, context, term], {None :> term, form_ :> intervalTerm[form]}]

(* a path that is no function, applied to an endpoint, is that endpoint of its type *)
reducePathEndpoint[environment_, context_, term_, head_, arguments_List] := With[
	{position = FirstPosition[arguments, argument_ /; MatchQ[intervalForm[environment, context, argument], {} | {{}}], None, {1}, Heads -> False]},
	If[ position === None,
		term,
		With[{index = First[position]},
			Replace[
				pathTypeArguments[environment, weakHeadNormalForm[environment, context, inferType[environment, context, makeApplication[head, Take[arguments, index - 1]]]]],
				{
					{_, left_, right_} :> makeApplication[If[intervalForm[environment, context, arguments[[index]]] === {}, left, right], Drop[arguments, index]],
					None :> term
				}
			]
		]
	]
]

(* the line A at a fresh variable of the interval, reduced: {id, context, body} *)
openedLine[environment_, context_, line_] := With[{id = freshFreeVariable[]},
	With[{lineContext = extendContext[context, id, HoldComplete[i], $interval, "Explicit"]},
		{id, lineContext, weakHeadNormalForm[environment, lineContext, application[line, freeVariable[id]]]}
	]
]

(* a function of the interval variable id, from a term in which it is free *)
intervalLambda[name_, id_, body_] := lambdaAbstraction[name, $interval, abstractFreeVariable[body, id], "Explicit"]

(* the term with the variable id replaced *)
substitutedVariable[term_, id_, value_] := instantiateBoundVariable[abstractFreeVariable[term, id], value]

closedInductiveTypeQ[environment_, constantReference[name_, _]] := And[
	constantDeclaredQ[environment, name],
	MatchQ[constantRecord[environment, name], KeyValuePattern[{"Kind" -> "InductiveType", "NumberOfParameters" -> 0, "NumberOfIndices" -> 0}]]
]
closedInductiveTypeQ[_, _] := False

transportReduction[environment_, context_, level_, line_, face_, value_] := If[ faceTrueQ[environment, context, face],
	value,
	Replace[openedLine[environment, context, line], {
		{_, _, _universeSort} :> value,
		{_, _, type_} /; closedInductiveTypeQ[environment, type] :> value,
		{id_, lineContext_, dependentFunctionType[name_, domain_, codomain_, binder_]} /; ! intervalTypeQ[environment, domain] :>
			functionTransport[environment, context, lineContext, id, face, value, name, domain, codomain, binder],
		{id_, lineContext_, type_} /; pathTypeArguments[environment, type] =!= None :>
			pathTransport[environment, context, lineContext, id, level, face, value, pathTypeArguments[environment, type]],
		_ -> None
	}]
]

(* In (x : B[i]) -> C[i, x], a function f goes to the function of v : B[1] that transports f applied to v
   transported back, w(0), along C[i, w(i)], where w(i) carries v from B[1] to B[i] and is v where the face
   holds or i is 1. *)
functionTransport[environment_, context_, lineContext_, id_, face_, value_, name_, domain_, codomain_, binder_] := Module[
	{argumentId = freshFreeVariable[], domainLevel, codomainLevel, back, outerContext},
	domainLevel = sortLevel[environment, lineContext, domain];
	codomainLevel = With[{fieldId = freshFreeVariable[]},
		sortLevel[environment, extendContext[lineContext, fieldId, name, domain, binder], instantiateBoundVariable[codomain, freeVariable[fieldId]]]
	];
	outerContext = extendContext[context, argumentId, name, substitutedVariable[domain, id, $intervalOne], binder];
	back = Function[r, With[{jd = freshFreeVariable[]},
		makeApplication[cubicalConstant["Transport", domainLevel], {
			intervalLambda[HoldComplete[j], jd, substitutedVariable[domain, id, intervalJoin[r, intervalReverse[freeVariable[jd]]]]],
			intervalJoin[face, r],
			freeVariable[argumentId]
		}]
	]];
	makeLambda[outerContext, {argumentId}, makeApplication[cubicalConstant["Transport", codomainLevel], {
		intervalLambda[HoldComplete[i], id, instantiateBoundVariable[codomain, back[freeVariable[id]]]],
		face,
		application[value, back[$intervalZero]]
	}]]
]

(* in Path[A[i], u[i], v[i]], a path p goes to the path of j that composes along A[i][j] from p[j], with the
   sides p[j] where the face holds, u[i] at j = 0 and v[i] at j = 1 *)
pathTransport[environment_, context_, lineContext_, id_, level_, face_, value_, {innerLine_, left_, right_}] := With[{jd = freshFreeVariable[]},
	With[{pathContext = extendContext[context, jd, HoldComplete[j], $interval, "Explicit"]},
		makeLambda[pathContext, {jd}, heterogeneousComposition[
			environment,
			pathContext,
			level,
			intervalLambda[HoldComplete[i], id, application[innerLine, freeVariable[jd]]],
			{
				{face, intervalLambda[HoldComplete[i], id, application[value, freeVariable[jd]]]},
				{intervalReverse[freeVariable[jd]], intervalLambda[HoldComplete[i], id, left]},
				{freeVariable[jd], intervalLambda[HoldComplete[i], id, right]}
			},
			application[value, freeVariable[jd]]
		]]
	]
]

(* Composition along a line A, comp A [φ ↦ u] a: composition in A[1] of the sides transported to 1 from
   where they are, and of the base transported along all of A. The sides are lines, functions of the interval. *)
heterogeneousComposition[environment_, context_, level_, line_, branches_List, cap_] := With[{id = freshFreeVariable[]},
	makeApplication[cubicalConstant["Composition", level], {
		application[line, $intervalOne],
		lambdaAbstraction[HoldComplete[i], $interval, abstractFreeVariable[cubicalSystem[Function[branch, {
			First[branch],
			With[{kd = freshFreeVariable[]},
				makeApplication[cubicalConstant["Transport", level], {
					intervalLambda[HoldComplete[k], kd, application[line, intervalJoin[freeVariable[id], freeVariable[kd]]]],
					freeVariable[id],
					application[Last[branch], freeVariable[id]]
				}]
			]
		}] /@ branches], id], "Explicit"],
		makeApplication[cubicalConstant["Transport", level], {line, $intervalZero, cap}]
	}]
]

(* Composition is the side at 1 where a face holds; in a function type it composes the values, and in a path
   type the points, with the path's endpoints as two more sides. *)
compositionReduction[environment_, context_, level_, type_, tube_, cap_] := With[{opened = openedTube[environment, context, tube]},
	Replace[SelectFirst[Transpose[{opened["Faces"], opened["Sides"]}], Function[branch, faceTrueQ[environment, context, First[branch]]], None], {
		{_, side_} :> restricted[side, <|opened["Id"] -> $intervalOne|>],
		None :> Replace[weakHeadNormalForm[environment, context, type], {
			dependentFunctionType[name_, domain_, codomain_, binder_] /; ! intervalTypeQ[environment, domain] :>
				functionComposition[environment, context, opened, name, domain, codomain, binder, cap],
			pathType_ /; pathTypeArguments[environment, pathType] =!= None :>
				pathComposition[environment, context, level, opened, pathTypeArguments[environment, pathType], cap],
			_ -> None
		}]
	}]
]

functionComposition[environment_, context_, opened_, name_, domain_, codomain_, binder_, cap_] := With[{argumentId = freshFreeVariable[]},
	With[
		{
			argumentContext = extendContext[context, argumentId, name, domain, binder],
			valueType = instantiateBoundVariable[codomain, freeVariable[argumentId]]
		},
		makeLambda[argumentContext, {argumentId}, makeApplication[cubicalConstant["Composition", sortLevel[environment, argumentContext, valueType]], {
			valueType,
			systemTube[opened, Function[side, application[side, freeVariable[argumentId]]], {}],
			application[cap, freeVariable[argumentId]]
		}]]
	]
]

pathComposition[environment_, context_, level_, opened_, {innerLine_, left_, right_}, cap_] := With[{jd = freshFreeVariable[]},
	With[{pathContext = extendContext[context, jd, HoldComplete[j], $interval, "Explicit"]},
		makeLambda[pathContext, {jd}, makeApplication[cubicalConstant["Composition", level], {
			application[innerLine, freeVariable[jd]],
			systemTube[opened, Function[side, application[side, freeVariable[jd]]], {{intervalReverse[freeVariable[jd]], left}, {freeVariable[jd], right}}],
			application[cap, freeVariable[jd]]
		}]]
	]
]

(* the tube of a composition with each side changed, and further branches constant in the tube's variable *)
systemTube[opened_, change_, extra_List] := lambdaAbstraction[HoldComplete[i], $interval, abstractFreeVariable[
	cubicalSystem[Join[Transpose[{opened["Faces"], change /@ opened["Sides"]}], extra]],
	opened["Id"]
], "Explicit"]
