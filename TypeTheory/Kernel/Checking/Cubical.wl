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
	GlueType[A, system]                         the type A with, where each face of the system holds, a type T glued
	                                            to it along an equivalence e : T ≃ A; the system gives the pairs
	                                            {T, e}, elements of the sum, and where a face holds it is T
	GlueIntroduction[A, system, terms, a]       the element of the Glue type that is t where a face holds, t a term
	                                            of the system terms that e takes to a, an element of A
	GlueElimination[A, system, b]               the element of A under the element b of the Glue type; where a face
	                                            holds it is e applied to b

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

An equivalence T ≃ A is a function with contractible fibers, the type the kernel writes with the sum, the
dependent sum type TypeTheoryCubical names, and Path:

	Fiber[f, y]          Σ x : T, Path[A, f[x], y]
	IsContractible[X]    Σ c : X, ∀ z : X, Path[X, c, z]
	T ≃ A                Σ f : T -> A, ∀ y : A, IsContractible[Fiber[f, y]]

Transport and composition compute by the type they are in, as in cubical type theory: transport is the
identity where its face holds, and in a universe or an inductive type with no parameters and no indices;
in a function type and a path type, and composition in a function type and a path type, it is built from
transport and composition in the parts. Composition is the side its system gives at IntervalOne where a
face holds. Transport in a Glue type, where its own face is 0 and no face of the Glue type holds for every
point of the line, transports the element under it in A, and takes the center of the fiber of each
equivalence at the end of the line over it, which a composition then joins: transport along the path that
univalence gives an equivalence e applies e. Where no rule applies the term does not compute, which costs
canonicity and never consistency: every rule is one of cubical type theory.

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
PackageExported[GlueType]
PackageExported[GlueIntroduction]
PackageExported[GlueElimination]


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
PackageScoped[glueTypeArguments]
PackageScoped[gluePairType]
PackageScoped[pairType]
PackageScoped[cubicalSum]
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
GlueType::usage = "GlueType[A, {face -> pair, ...}] is the type A glued, where each face holds, to the type T of the pair, an element {T, e} of the sum with \
e an equivalence from T to A; where a face holds it is T. Univalence turns an equivalence into a path of Glue types."
GlueIntroduction::usage = "GlueIntroduction[{face -> t, ...}, a] is the element of the Glue type expected that is t where a face holds and lies over a, \
an element of A that the equivalence takes t to. GlueIntroduction[A, system, {face -> t, ...}, a] gives the Glue type GlueType[A, system] in full."
GlueElimination::usage = "GlueElimination[b] is the element of A under b, an element of GlueType[A, system]; where a face of the system holds it is the \
equivalence there applied to b. GlueElimination[A, system, b] gives the Glue type in full."

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
glueTypeArguments::usage = "glueTypeArguments[environment, type] gives {level, base, system} for a Glue type GlueType[base, system] at the universe level level, or None."
gluePairType::usage = "gluePairType[sum, level, base] gives the type of the pairs of a Glue type over base in Type level: Σ T : Type level, T ≃ base."
pairType::usage = "pairType[sum, pair] gives the glued type T of a pair {T, e} of a Glue type."
cubicalSum::usage = "cubicalSum[environment] gives the dependent sum type that TypeTheoryCubical names in environment."
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
	"Composition" -> HoldComplete[CubicalComposition],
	"GlueType" -> HoldComplete[GlueType],
	"GlueIntroduction" -> HoldComplete[GlueIntroduction],
	"GlueElimination" -> HoldComplete[GlueElimination]
|>

(* the arguments a primitive must have before it is a term: those with rules of their own *)
$saturatedArity = <|"Transport" -> 3, "Composition" -> 3, "GlueType" -> 2, "GlueIntroduction" -> 4, "GlueElimination" -> 3|>

declareCubical[environment_, sum_HoldComplete] := withKernelCaches[
	(* the live check of quantities does not count the uses in a system, so the two do not go together *)
	If[ ! TrueQ[rulesSetting[environment, "Cubical"]] || TrueQ[rulesSetting[environment, "Prop"]] || TrueQ[rulesSetting[environment, "Quantities"]],
		kernelFailure["CubicalNotAllowed", "The rules of the environment are not cubical: they need \"Cubical\" -> True, no Prop and no quantities.", {}]
	];
	If[ ! sumQ[environment, sum],
		kernelFailure[
			"SumExpected",
			"TypeTheoryCubical needs `1` declared as the dependent sum, of the type ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, A -> TypeUniverse[v + 1]]}, TypeUniverse[Max[u + 1, v + 1]]] with one constructor of the type ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, A -> TypeUniverse[v + 1]], Typed[a, A], Typed[b, B[a]]}, `1`[A, B]].",
			{HoldForm @@ sum}
		]
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
			"UniverseParameters" -> If[MemberQ[{"Path", "Transport", "Composition", "GlueType", "GlueIntroduction", "GlueElimination"}, role], {HoldComplete[u]}, {}],
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

(* the Glue primitives' types only name their arguments: the systems, which no type describes, are checked by
   the kernel itself. ForAll[{TypedImplicit[A, Type u], TypedImplicit[system, Type u]}, Type u] and so on *)
cubicalType["GlueType"] := dependentFunctionType[HoldComplete[A], glueSort[],
	dependentFunctionType[HoldComplete[system], glueSort[], glueSort[], "Explicit"],
	"Explicit"
]
cubicalType["GlueIntroduction"] := dependentFunctionType[HoldComplete[A], glueSort[],
	dependentFunctionType[HoldComplete[system], glueSort[],
		dependentFunctionType[HoldComplete[terms], glueSort[],
			dependentFunctionType[HoldComplete[a], boundVariable[2], glueSort[], "Explicit"],
			"Explicit"
		],
		"Implicit"
	],
	"Implicit"
]
cubicalType["GlueElimination"] := dependentFunctionType[HoldComplete[A], glueSort[],
	dependentFunctionType[HoldComplete[system], glueSort[],
		dependentFunctionType[HoldComplete[b], glueSort[], boundVariable[2], "Explicit"],
		"Implicit"
	],
	"Implicit"
]

glueSort[] := universeSort[levelSuccessor[levelParameter[HoldComplete[u]], 1]]


(* ::Subsection:: *)
(*Equivalences*)


(* the dependent sum: a structure of a type A in Type u and a family B over it in Type v, with the pair of an
   a and a b : B[a] *)
sumQ[environment_, sum_HoldComplete] := And[
	constantDeclaredQ[environment, sum],
	structureLikeQ[environment, sum],
	MatchQ[constantRecord[environment, sum], KeyValuePattern[{"UniverseParameters" -> {_, _}, "NumberOfParameters" -> 2}]],
	With[
		{
			record = constantRecord[environment, sum],
			levels = levelParameter /@ constantRecord[environment, sum]["UniverseParameters"]
		},
		And[
			definitionallyEqualQ[environment, <||>, record["Type"], expectedSumType[levels]],
			definitionallyEqualQ[environment, <||>, constantRecord[environment, First[record["Constructors"]]]["Type"], expectedPairType[sum, levels]]
		]
	]
]

(* ForAll[{Typed[A, Type u], Typed[B, A -> Type v]}, Type (max u v)] *)
expectedSumType[{u_, v_}] := dependentFunctionType[HoldComplete[A], typeAt[u],
	dependentFunctionType[HoldComplete[B], dependentFunctionType[HoldComplete[x], boundVariable[0], typeAt[v], "Explicit"],
		universeSort[normalizeLevel[levelMaximum[levelSuccessor[u, 1], levelSuccessor[v, 1]]]],
		"Explicit"
	],
	"Explicit"
]

(* ForAll[{TypedImplicit[A, Type u], TypedImplicit[B, A -> Type v], Typed[a, A], Typed[b, B[a]]}, sum[A, B]] *)
expectedPairType[sum_, {u_, v_}] := dependentFunctionType[HoldComplete[A], typeAt[u],
	dependentFunctionType[HoldComplete[B], dependentFunctionType[HoldComplete[x], boundVariable[0], typeAt[v], "Explicit"],
		dependentFunctionType[HoldComplete[a], boundVariable[1],
			dependentFunctionType[HoldComplete[b], application[boundVariable[1], boundVariable[0]],
				makeApplication[constantReference[sum, {u, v}], {boundVariable[3], boundVariable[2]}],
				"Explicit"
			],
			"Explicit"
		],
		"Implicit"
	],
	"Implicit"
]

typeAt[level_] := universeSort[normalizeLevel[levelSuccessor[level, 1]]]

(* terms built with fresh variables, abstracted at the end *)
binding[head_, name_, domain_, body_] := With[{id = freshFreeVariable[]},
	head[HoldComplete[name], domain, abstractFreeVariable[body[freeVariable[id]], id], "Explicit"]
]

sumOf[sum_, {u_, v_}, domain_, family_] := makeApplication[constantReference[sum, {u, v}], {domain, family}]

constantPath[level_, type_, left_, right_] := makeApplication[cubicalConstant["Path", normalizeLevel[levelSuccessor[level, 1]]], {
	lambdaAbstraction[HoldComplete[i], $interval, liftBoundVariables[type, 1, 0], "Explicit"],
	left,
	right
}]

(* for T and A in Type u: the fiber of f over y, contractibility, and the equivalences from T to A *)
fiberType[sum_, u_, domain_, codomain_, function_, point_] :=
	sumOf[sum, {u, u}, domain, binding[lambdaAbstraction, x, domain, Function[element, constantPath[u, codomain, application[function, element], point]]]]

contractibleType[sum_, u_, type_] := sumOf[sum, {u, u}, type, binding[lambdaAbstraction, c, type, Function[center,
	binding[dependentFunctionType, z, type, Function[other, constantPath[u, type, center, other]]]
]]]

equivalenceType[sum_, u_, domain_, codomain_] := With[{functionType = binding[dependentFunctionType, x, domain, Function[element, codomain]]},
	sumOf[sum, {u, u}, functionType, binding[lambdaAbstraction, f, functionType, Function[function,
		binding[dependentFunctionType, y, codomain, Function[point, contractibleType[sum, u, fiberType[sum, u, domain, codomain, function, point]]]]
	]]]
]

(* the type of a pair {T, e} of a Glue type over A in Type u: Σ T : Type u, T ≃ A *)
gluePairType[sum_, u_, base_] := sumOf[sum, {normalizeLevel[levelSuccessor[u, 1]], u}, typeAt[u], binding[lambdaAbstraction, T, typeAt[u], Function[glued,
	equivalenceType[sum, u, glued, base]
]]]

pairType[sum_, pair_] := projection[sum, 0, pair]
pairFunction[sum_, pair_] := projection[sum, 0, projection[sum, 1, pair]]

(* the center of contraction of the fiber over y of the equivalence of a pair: {x, Path[A, f[x], y]} *)
fiberCenter[sum_, pair_, point_] := projection[sum, 0, application[projection[sum, 1, projection[sum, 1, pair]], point]]


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

(* GlueType[A, system]: A in Type u, and each pair of the system an element of Σ T : Type u, T ≃ A where its face holds *)
saturatedType[environment_, context_, "GlueType", {level_}, {base_, system_}] := (
	checkGlueSystem[environment, context, level, base, system];
	typeAt[level]
)

(* GlueIntroduction[A, system, terms, a]: the terms are elements of the glued types, which the equivalences take to a *)
saturatedType[environment_, context_, "GlueIntroduction", {level_}, {base_, system_, terms_, value_}] := With[{sum = cubicalSum[environment]},
	checkGlueSystem[environment, context, level, base, system];
	checkHasType[environment, context, value, base];
	Replace[{system, terms}, {
		{cubicalSystem[pairs_List], cubicalSystem[elements_List]} /; Length[pairs] == Length[elements] && AllTrue[
				Transpose[{pairs, elements}],
				Function[branch, intervalEqualQ[environment, context, First[First[branch]], First[Last[branch]]]]
			] :> (
			MapThread[
				Function[{pair, element}, (
					checkUnderFace[environment, context, First[pair], Last[element], pairType[sum, Last[pair]]];
					If[ ! equalUnderFaceQ[environment, context, First[pair], application[pairFunction[sum, Last[pair]], Last[element]], value],
						kernelFailure["GlueMismatch", "The equivalence of a Glue type must take each term of the element to the element of the base under it.", {}]
					]
				)],
				{pairs, elements}
			];
			Do[
				If[ ! equalUnderFaceQ[environment, context, intervalMeet[First[elements[[k]]], First[elements[[l]]]], Last[elements[[k]]], Last[elements[[l]]]],
					kernelFailure["SystemDisagreement", "Two sides of a system disagree where both their faces hold.", {}]
				],
				{k, Length[elements]},
				{l, k + 1, Length[elements]}
			]
		),
		_ :> kernelFailure["GlueTermsExpected", "The terms of an element of a Glue type must be a system with the faces of the Glue type, in order.", {}]
	}];
	makeApplication[cubicalConstant["GlueType", level], {base, system}]
]

(* GlueElimination[A, system, b]: b an element of GlueType[A, system] *)
saturatedType[environment_, context_, "GlueElimination", {level_}, {base_, system_, glued_}] := (
	checkGlueSystem[environment, context, level, base, system];
	checkHasType[environment, context, glued, makeApplication[cubicalConstant["GlueType", level], {base, system}]];
	base
)

saturatedType[_, _, role_, _, _] := kernelFailure["CubicalUniverse", "`1` takes one universe level.", {HoldForm @@ $cubicalNames[role]}]

cubicalSum[environment_] := constantRecord[environment, $cubicalNames["Interval"]]["Sum"]

checkGlueSystem[environment_, context_, level_, base_, cubicalSystem[branches_List]] := (
	checkHasType[environment, context, base, typeAt[level]];
	checkSystem[environment, context, First /@ branches, Last /@ branches, gluePairType[cubicalSum[environment], level, base]]
)
checkGlueSystem[_, _, _, _, _] := kernelFailure["GlueSystemExpected", "A Glue type takes a system of pairs, {face -> pair, ...}.", {}]

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
	(* where a face holds, a Glue type is its glued type, an element of it its term there, and the element
	   under one the equivalence applied to it *)
	{"GlueType", {_, cubicalSystem[branches_List], rest___}} :> Replace[
		trueBranch[environment, context, branches],
		{None :> term, {_, pair_} :> makeApplication[pairType[record["Sum"], pair], {rest}]}
	],
	{"GlueIntroduction", {_, _, cubicalSystem[elements_List], _, rest___}} :> Replace[
		trueBranch[environment, context, elements],
		{None :> term, {_, element_} :> makeApplication[element, {rest}]}
	],
	{"GlueElimination", {_, cubicalSystem[branches_List], glued_, rest___}} :> Replace[trueBranch[environment, context, branches], {
		{_, pair_} :> makeApplication[application[pairFunction[record["Sum"], pair], glued], {rest}],
		None :> Replace[applicationSpine[weakHeadNormalForm[environment, context, glued]], {
			{constantReference[name_, _], {_, _, _, value_}} /; cubicalRole[environment, name] === "GlueIntroduction" :> makeApplication[value, {rest}],
			_ :> term
		}]
	}],
	_ :> term
}]

trueBranch[environment_, context_, branches_List] := SelectFirst[branches, Function[branch, faceTrueQ[environment, context, First[branch]]], None]

(* an operation on the interval is its canonical term *)
canonicalInterval[environment_, context_, term_] := Replace[intervalForm[environment, context, term], {None :> term, form_ :> intervalTerm[form]}]

(* a path that is no function, applied to an endpoint, is that endpoint of its type *)
reducePathEndpoint[environment_, context_, term_, head_, arguments_List] := With[
	{
		position = FirstPosition[
			Drop[arguments, saturatedPrefix[environment, head]],
			argument_ /; MatchQ[intervalForm[environment, context, argument], {} | {{}}],
			None,
			{1},
			Heads -> False
		]
	},
	If[ position === None,
		term,
		With[{index = First[position] + saturatedPrefix[environment, head]},
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

(* the arguments of a primitive that its own rules check, which are no path applied to an endpoint *)
saturatedPrefix[environment_, constantReference[name_, _]] := Lookup[$saturatedArity, cubicalRole[environment, name], 0]
saturatedPrefix[_, _] := 0

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
		{id_, lineContext_, type_} /; glueTypeArguments[environment, type] =!= None :>
			glueTransport[environment, context, lineContext, id, level, face, value, glueTypeArguments[environment, type]],
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

glueTypeArguments[environment_, type_] := Replace[applicationSpine[type], {
	{constantReference[name_, {glueLevel_}], {base_, system_cubicalSystem}} /; cubicalRole[environment, name] === "GlueType" :> {glueLevel, base, system},
	_ -> None
}]

(* Transport in GlueType[A[i], {ψ[i] -> {T[i], e[i]}, ...}] with its own face 0, where no face ψ holds all
   along the line: the element under b, carried along A, is a1; at the end of the line, the center of the
   fiber over a1 of each equivalence e[1] gives a term t and a path from e[1][t] to a1, and a composition in
   A[1] along those paths reversed gives the element under the result, which is t where ψ[1] holds. *)
glueTransport[environment_, context_, lineContext_, id_, level_, face_, value_, {glueLevel_, base_, cubicalSystem[branches_List]}] := If[
	intervalForm[environment, context, face] =!= {} || ! independentFaceEmptyQ[environment, lineContext, id, First /@ branches],
	None,
	glueTransportReduct[environment, id, level, value, glueLevel, base, branches]
]

glueTransportReduct[environment_, id_, level_, value_, glueLevel_, base_, branches_List] := Module[
	{sum = cubicalSum[environment], startSystem, endSystem, endBase, under, centers},
	startSystem = cubicalSystem[Map[Function[part, substitutedVariable[part, id, $intervalZero]], branches, {2}]];
	endSystem = cubicalSystem[Map[Function[part, substitutedVariable[part, id, $intervalOne]], branches, {2}]];
	endBase = substitutedVariable[base, id, $intervalOne];
	under = makeApplication[cubicalConstant["Transport", level], {
		intervalLambda[HoldComplete[i], id, base],
		$intervalZero,
		makeApplication[cubicalConstant["GlueElimination", glueLevel], {substitutedVariable[base, id, $intervalZero], startSystem, value}]
	}];
	centers = Function[branch, fiberCenter[sum, Last[branch], under]] /@ First[endSystem];
	makeApplication[cubicalConstant["GlueIntroduction", glueLevel], {
		endBase,
		endSystem,
		cubicalSystem[Transpose[{First /@ First[endSystem], Function[center, projection[sum, 0, center]] /@ centers}]],
		With[{jd = freshFreeVariable[]},
			makeApplication[cubicalConstant["Composition", level], {
				endBase,
				lambdaAbstraction[HoldComplete[j], $interval, abstractFreeVariable[
					cubicalSystem[Transpose[{First /@ First[endSystem], Function[center, application[projection[sum, 1, center], intervalReverse[freeVariable[jd]]]] /@ centers}]],
					jd
				], "Explicit"],
				under
			}]
		]
	}]
]

(* no conjunction of the faces, all joined, leaves the variable of the line out *)
independentFaceEmptyQ[environment_, context_, id_, faces_List] := With[
	{form = intervalForm[environment, context, Fold[intervalJoin, $intervalZero, faces]]},
	form =!= None && NoneTrue[Select[form, consistentConjunctionQ], Function[conjunction, FreeQ[conjunction, {id, _}]]]
]
