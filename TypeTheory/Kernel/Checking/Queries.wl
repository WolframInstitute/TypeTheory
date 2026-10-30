(* ::Package:: *)

(*
Questions about terms and environments.

TypeTheoryTerm[term, environment] carries the environment its constants come from; TypeTheoryTerm[term]
without one is read in the default environment, $TypeTheoryEnvironment, or, beside a term that has one, in that term's. A term's universe parameters are the symbols and strings
in its universe levels. Answers are TypeTheoryTerm expressions in the same environment, read back from
core terms.

An environment behaves like an Association of its constants: environment[name] gives the declaration
that introduced name, Keys gives the names in the order they were declared, and Length, KeyExistsQ and
Normal work as for an Association, Normal giving the declarations themselves, in order. Information
gives "Constants", "Kinds", "Axioms", "RewriteRules", "NaturalNumbers", "Rules" and "Provenance", which says whether
the environment was read from a file without checking it (SavedEnvironments.wl).

An environment's store can be changed by hand. TypeTheoryCheck[environment] is how to trust it anyway:
it replays every declaration in order on the empty environment of the same rules with the core
declaration functions, and compares each record with the one the replay produces. Axioms and rewrite
rules are taken on trust, as their name says.

TypeTheoryTranslate[environment, rules] replays the declarations the same way on the empty environment
of other rules, whose kernel checks each of them again: a translation is trusted no more than the
declarations it gives. Where the rules lose Prop, Prop becomes the lowest universe of types, Type, and the
other universes stay: a level l becomes max(l, 1), which commutes with instantiating universe parameters.
A recursor's motive goes into Sort u with Prop and into Sort (u + 1) without it, so the universe level a
recursor is applied at moves down by one where the rules lose Prop, and up by one where they gain it,
and a recursor that eliminates into Prop alone gets the level 0; a declaration whose motives go into
Prop itself, as a proof that 0 is no successor does, is tried again with the levels kept. An inductive
proposition lives in the universe of its largest field, as Exists does. What needs Prop's impredicativity
or proof irrelevance, or a recursor at a universe parameter that may be 0, then fails to check, and is
left out with every declaration that mentions it. A theorem of rules without Prop states a type, so where
the rules gain Prop it becomes a definition. Where the rules lose quantities, every binder loses its
quantity; where they gain them, the kernel gives the constructors and recursors theirs.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryCheck]
PackageExported[TypeTheoryAxiomClosure]
PackageExported[TypeTheoryTranslate]
PackageExported[DefinitionallyEqualQ]
PackageExported[WeakHeadNormalForm]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[termEnvironment]
PackageScoped[heldTerm]
PackageScoped[termSyntax]
PackageScoped[declarationOf]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryAxiomClosure::usage = "TypeTheoryAxiomClosure[term] gives the axioms the TypeTheoryTerm term rests on, through the types and values of the constants \
it mentions and of the constants those mention, as <|axiom -> kind, ...|>: \"Proposition\" for an axiom that is a proposition, \"Signature\" for one whose \
type is a type, a parameter as a variable is, and \"RewriteRule\" for a rewrite rule of a constant reached, which the kernel computes with."
TypeTheoryCheck::usage = "TypeTheoryCheck[term] gives the type of the TypeTheoryTerm term in its environment, or a Failure if it does not type-check.\n\
TypeTheoryCheck[term, type] gives a Success if term has the given type, and a Failure otherwise.\n\
TypeTheoryCheck[environment] checks every declaration of the TypeTheoryEnvironment environment again from scratch and gives a Success, \
or a Failure for the first declaration that does not check. With Method -> \"Symbolic\" it replays every declaration with the kernel written in \
Wolfram Language; by default it checks with the compiled kernel where one is available."
TypeTheoryTranslate::usage = "TypeTheoryTranslate[environment, rules] translates the declarations of the TypeTheoryEnvironment environment to the \
TypeTheoryRules rules, whose kernel checks them again, and gives a Success whose \"Environment\" is the environment of rules with each declaration that \
checks there, and whose \"Failures\" gives the failure of each declaration left out, those that mention one included.\n\
Where rules have no Prop, Prop becomes the lowest universe of types, Type. Axioms are left out, since one that holds of propositions need not hold of \
types, as propositional extensionality does not; the option \"Axioms\" -> True keeps them."
DefinitionallyEqualQ::usage = "DefinitionallyEqualQ[term1, term2] gives True if the TypeTheoryTerm expressions term1 and term2 are equal by computation \
in their environment, and False otherwise."
WeakHeadNormalForm::usage = "WeakHeadNormalForm[term] reduces the TypeTheoryTerm term until its head can no longer reduce."

termEnvironment::usage = "termEnvironment[term] gives the environment of the TypeTheoryTerm term, or the default environment if it has none."
heldTerm::usage = "heldTerm[term] gives HoldComplete[expr] for the TypeTheoryTerm term holding expr."
termSyntax::usage = "termSyntax[term] gives the syntax tree of the TypeTheoryTerm term."
declarationOf::usage = "declarationOf[environment, HoldComplete[name], mode] gives the declaration that introduced the constant name, \
its terms read back for display (mode \"Display\") or exactly (mode \"Exact\")."


(* ::Section:: *)
(*Function Definitions*)


(* a term without an environment is in the default environment *)
termEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
termEnvironment[TypeTheoryTerm[_]] := defaultEnvironment[]

heldTerm[TypeTheoryTerm[term_, ___]] := HoldComplete[term]

termSyntax[TypeTheoryTerm[term_, ___]] := toSyntax[term]

(* the environment two terms share: a term without one takes the other's, and two without one are in
   the default environment *)
sharedEnvironment[first_TypeTheoryTerm, second_TypeTheoryTerm] := Replace[{givenEnvironment[first], givenEnvironment[second]}, {
	{None, None} :> defaultEnvironment[],
	{environment_, None} | {None, environment_} :> environment,
	{environment_, environment_} :> environment,
	_ :> kernelFailure["DifferentEnvironments", "The terms carry different environments.", {}]
}]

givenEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
givenEnvironment[TypeTheoryTerm[_]] := None

elaborateQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] :=
	elaborateClosedTerm[environment, heldTerm[term], expected, universeParameters]

(* a term checks under rules with quantities only if its functions use their variables as their quantities allow *)
checkedQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] := With[
	{elaborated = elaborateQueryTerm[environment, term, expected, universeParameters]},
	If[rulesSetting[environment, "Quantities"], withKernelCaches[checkLiveUses[environment, First[elaborated]]]];
	elaborated
]


TypeTheoryTerm /: TypeOf[term : TypeTheoryTerm[_, ___]] := TypeTheoryCheck[term]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "AxiomClosure"] := TypeTheoryAxiomClosure[term]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Constants"] := catchKernelFailure[ReleaseHold /@ typeAndValueConstants[termEnvironment[term], term]]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Holes"] := catchKernelFailure[termHoles[termEnvironment[term], term]]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Annotation"] := catchKernelFailure[termAnnotation[termEnvironment[term], term]]
TypeTheoryTerm /: Information[TypeTheoryTerm[_, ___], "Properties"] := {"AxiomClosure", "Holes", "Constants", "Annotation"}
TypeTheoryTerm /: TypeOf[TypeTheoryTerm[term_], environment_?environmentQ] := TypeTheoryCheck[TypeTheoryTerm[term, environment]]


(* a constant on its own has its declared type, with its implicit arguments and universe parameters *)
TypeTheoryCheck[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	coreToTypeTheoryTerm[environment, <||>, betaNormalize @ Replace[aliasResolvedName[environment, heldFromSyntax[termSyntax[term]]], {
		name_ /; And[constantDeclaredQ[environment, name], ! overloadedNameQ[environment, name], constantRecord[environment, name]["Kind"] =!= "RewriteRule"] :>
			constantRecord[environment, name]["Type"],
		_ :> Last @ checkedQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]
	}]]
]

TypeTheoryCheck[term_TypeTheoryTerm, type_TypeTheoryTerm] := catchKernelFailure @ With[
	{environment = sharedEnvironment[term, type], universeParameters = universeParameterNames[{termSyntax[term], termSyntax[type]}]},
	{expected = elaborateClosedType[environment, heldTerm[type], universeParameters]},
	checkedQueryTerm[environment, term, expected, universeParameters];
	Success["TypeChecked", <|"MessageTemplate" -> "`1` has type `2`.", "MessageParameters" -> {term, type}, "Term" -> term, "Type" -> type|>]
]


(* the kernel checks each term as elaboration finishes, so the two compared are checked *)
DefinitionallyEqualQ[first_TypeTheoryTerm, second_TypeTheoryTerm] := TrueQ @ catchKernelFailure @ With[
	{environment = sharedEnvironment[first, second], universeParameters = universeParameterNames[{termSyntax[first], termSyntax[second]}]},
	{
		terms = {
			First @ elaborateQueryTerm[environment, first, None, universeParameters],
			First @ elaborateQueryTerm[environment, second, None, universeParameters]
		}
	},
	withCheckedTerms[definitionallyEqualQ[environment, <||>, First[terms], Last[terms]]]
]


WeakHeadNormalForm[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	coreToTypeTheoryTerm[
		environment,
		<||>,
		weakHeadNormalForm[environment, <||>, First @ elaborateQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]]
	]
]


(* ::Subsection:: *)
(*Environments as associations*)


(environment : TypeTheoryEnvironment[_Symbol])[name_] /; environmentQ[environment] := declarationOf[environment, HoldComplete[name], "Display"]

TypeTheoryEnvironment /: Keys[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := ReleaseHold /@ environmentNames[environment]
TypeTheoryEnvironment /: Length[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := Length[environmentNames[environment]]
TypeTheoryEnvironment /: KeyExistsQ[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, name_] := constantDeclaredQ[environment, HoldComplete[name]]

(* the declarations, in order; constructors and recursors come with their inductive type *)
TypeTheoryEnvironment /: Normal[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := catchKernelFailure @ With[
	{primary = primaryNames[environment]},
	Replace[naturalNumberSettings[environment], {
		settings_Association :> withRegistrations[Function[name, declarationOf[environment, name, "Exact"]] /@ primary, primary, settings],
		None :> Function[name, declarationOf[environment, name, "Exact"]] /@ primary
	}]
]

(* constructors and recursors come with their type, the types of a block with its first, and the holes of a theorem
   with the theorem, whose proof reads back with them *)
primaryNames[environment_] := Select[
	environmentNames[environment],
	Function[name, With[{record = constantRecord[environment, name]}, ! generatedQ[record, name] && record["Kind"] =!= "Hole"]]
]

generatedQ[record_, name_] := Or[
	MatchQ[record["Kind"], "Constructor" | "Recursor"],
	record["Kind"] === "InductiveType" && First[record["Block"]] =!= name,
	record["Kind"] === "Quotient" && record["QuotientType"] =!= name,
	record["Kind"] === "Cubical" && record["CubicalRole"] =!= "Interval"
]

(* each registration of the natural numbers, or of operations on them, comes right after the last constant
   it names, and after the registration before it *)
withRegistrations[declarations_List, primary_List, settings_Association] := With[
	{positions = Rest @ FoldList[Max, 0, MapIndexed[
		Function[{roles, index}, Max[Flatten[Position[primary, Alternatives @@ registrationNames[settings, First[index]], {1}]]]],
		settings["Registrations"]
	]]},
	Catenate @ MapIndexed[
		Function[{declaration, index}, Prepend[
			Function[registration, registrationDeclaration[settings, registration]] /@ Flatten[Position[positions, First[index]]],
			declaration
		]],
		declarations
	]
]

(* the constants a registration names: the first also names the natural numbers themselves *)
registrationNames[settings_Association, 1] := Join[Lookup[settings, {"Type", "Zero", "Successor"}], Lookup[settings["Operations"], First[settings["Registrations"]]]]
registrationNames[settings_Association, index_Integer] := Lookup[settings["Operations"], settings["Registrations"][[index]]]

registrationOf[settings_Association, index_Integer] := <|
	KeyTake[settings, {"Type", "Zero", "Successor"}],
	"Operations" -> KeyTake[settings["Operations"], settings["Registrations"][[index]]]
|>

registrationDeclaration[settings_Association, index_Integer] := ReleaseHold @ heldFromSyntax @ syntaxHead[
	TypeTheoryNaturalNumbers,
	Join[
		toSyntax @@@ Lookup[settings, {"Type", "Zero", "Successor"}],
		Replace[KeyTake[settings["Operations"], settings["Registrations"][[index]]], {
			<||> -> {},
			operations_ :> {syntaxHead[Association, KeyValueMap[Function[{role, name}, syntaxHead[Rule, {syntaxString[role], toSyntax @@ name}]], operations]]}
		}]
	]
]

TypeTheoryEnvironment /: Information[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, property_String] := environmentInformation[environment, property]

environmentInformation[_, "Properties"] := {"Constants", "Kinds", "Axioms", "RewriteRules", "NaturalNumbers", "Rules", "Provenance"}
environmentInformation[environment_, "Constants"] := Keys[environment]
environmentInformation[environment_, "Kinds"] := Counts[Function[name, constantRecord[environment, name]["Kind"]] /@ environmentNames[environment]]
environmentInformation[environment_, "Axioms"] :=
	ReleaseHold /@ Select[environmentNames[environment], Function[name, constantRecord[environment, name]["Kind"] === "Axiom"]]
environmentInformation[environment_, "RewriteRules"] :=
	ReleaseHold /@ Select[environmentNames[environment], Function[name, constantRecord[environment, name]["Kind"] === "RewriteRule"]]
environmentInformation[environment_, "NaturalNumbers"] := Replace[
	naturalNumberSettings[environment],
	settings_Association :> <|Map[ReleaseHold, KeyTake[settings, {"Type", "Zero", "Successor"}]], "Operations" -> Map[ReleaseHold, settings["Operations"]]|>
]
environmentInformation[environment_, "Rules"] := environmentRules[environment]
environmentInformation[environment_, "Provenance"] := environmentProvenance[environment]


(* ::Subsection:: *)
(*Declarations read back*)


(* the quotient constants come from one declaration, written short with the prelude's names *)
quotientDeclaration[record_] := Replace[{record["Equality"], record["QuotientNames"]}, {
	{HoldComplete[Equal], HoldComplete /@ Unevaluated[{QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction}]} :> TypeTheoryQuotients[],
	{HoldComplete[equality_], names_List} :> (TypeTheoryQuotients[equality, names] /. HoldComplete[name_] :> name)
}]

declarationOf[environment_, name_HoldComplete, mode_String] := If[ ! constantDeclaredQ[environment, name],
	Missing["KeyAbsent", ReleaseHold[name]],
	Replace[constantRecord[environment, name], {
		record : KeyValuePattern["Kind" -> "Constructor" | "Recursor"] :> declarationOf[environment, record["InductiveType"], mode],
		record : KeyValuePattern["Kind" -> "Hole"] :> declarationOf[environment, record["Theorem"], mode],
		record : KeyValuePattern["Kind" -> "Quotient"] :> quotientDeclaration[record],
		record : KeyValuePattern["Kind" -> "Cubical"] :> Replace[record["Sum"], HoldComplete[sum_] :> TypeTheoryCubical[sum]],
		record_ :> ReleaseHold @ heldFromSyntax @ declarationSyntax[environment, name, record, mode]
	}]
]

(* a rewrite rule reads back as ForAll[binders, lhs -> rhs], with the binders its two sides share *)
declarationSyntax[environment_, name_, record : KeyValuePattern["Kind" -> "RewriteRule"], mode_] := syntaxHead[TypeTheoryRewriteRule, Join[
	{
		toSyntax @@ name,
		ruleSyntax[readBack[environment, record["LeftHandSide"], mode], readBack[environment, record["RightHandSide"], mode], record["NumberOfVariables"]]
	},
	universeOptionSyntax[record]
]]

declarationSyntax[environment_, name_, record_, mode_] := With[
	{
		nameSyntax = toSyntax @@ name,
		typeSyntax = readBack[environment, record["Type"], mode],
		universeOption = universeOptionSyntax[record]
	},
	Replace[record["Kind"], {
		"InductiveType" /; Length[record["Block"]] > 1 :> syntaxHead[TypeTheoryInductiveType, Join[
			{
				syntaxHead[List, Function[member,
					syntaxHead[Rule, {toSyntax @@ member, readBack[environment, constantRecord[environment, member]["Type"], mode]}]
				] /@ record["Block"]],
				syntaxHead[List, Function[constructor,
					syntaxHead[Rule, {toSyntax @@ constructor, readBack[environment, constantRecord[environment, constructor]["Type"], mode]}]
				] /@ Catenate[Function[member, constantRecord[environment, member]["Constructors"]] /@ record["Block"]]],
				syntaxHead[Rule, {syntaxString["Parameters"], syntaxInteger[record["NumberOfParameters"]]}]
			},
			universeOption
		]],
		"Axiom" :> syntaxHead[TypeTheoryAxiom, Join[{nameSyntax, typeSyntax}, universeOption, annotationOptionSyntax[record], overloadsOptionSyntax[record]]],
		"Definition" | "Opaque" :> syntaxHead[TypeTheoryDefinition, Join[
			{nameSyntax, syntaxHead[Typed, {readBack[environment, record["Value"], mode], typeSyntax}]},
			universeOption,
			Function[role, syntaxHead[Rule, {syntaxString[role], syntaxSymbol[HoldComplete[True]]}]] /@ Keys[Select[recordRoles[record], TrueQ]],
			overloadsOptionSyntax[record]
		]],
		"Theorem" :> syntaxHead[TypeTheoryTheorem, Join[{nameSyntax, typeSyntax, readBack[environment, record["Value"], mode]}, universeOption, annotationOptionSyntax[record]]],
		"InductiveType" :> syntaxHead[TypeTheoryInductiveType, Join[
			{
				nameSyntax,
				typeSyntax,
				syntaxHead[List, Function[constructor,
					syntaxHead[Rule, {toSyntax @@ constructor, readBack[environment, constantRecord[environment, constructor]["Type"], mode]}]
				] /@ record["Constructors"]],
				syntaxHead[Rule, {syntaxString["Parameters"], syntaxInteger[record["NumberOfParameters"]]}]
			},
			universeOption
		]]
	}]
]

(* the roles of a definition's record, as declareDefinition takes them *)
recordRoles[record_] := Join[Append[KeyTake[record, {"Instance", "Coercion"}], "Opaque" -> record["Kind"] === "Opaque"], KeyTake[record, {"Overloads"}]]

overloadsOptionSyntax[record_] := Replace[Lookup[record, "Overloads", None], {None -> {}, operation_HoldComplete :> {syntaxHead[Rule, {syntaxString["Overloads"], toSyntax @@ operation}]}}]

annotationOptionSyntax[record_] := Replace[Lookup[record, "Annotation", None], {None -> {}, annotation_ :> {syntaxOther[HoldComplete["Annotation" -> annotation]]}}]

universeOptionSyntax[record_] := Replace[record["UniverseParameters"], {
	{} -> {},
	parameters_List :> {syntaxHead[Rule, {syntaxString["UniverseParameters"], syntaxHead[List, toSyntax @@@ parameters]}]}
}]

ruleSyntax[left_, right_, 0] := syntaxHead[Rule, {left, right}]
ruleSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Function]], {binders_, leftBody_}], syntaxApplication[syntaxSymbol[HoldComplete[Function]], {_, rightBody_}], _] :=
	syntaxHead[ForAll, {binders, syntaxHead[Rule, {leftBody, rightBody}]}]

readBack[environment_, term_, "Display"] := delaborate[environment, <||>, term]
readBack[environment_, term_, "Exact"] := Block[{$exactReadBack = True}, delaborate[environment, <||>, term]]


(* ::Subsection:: *)
(*The axioms a term rests on*)


(* Lean's #print axioms: the constants a term mentions, then those in the type and value of each, until an axiom,
   which is collected and its type followed, so that a signature's own parameters show; a constructor or recursor
   leads to its inductive type, and an inductive type to its constructors. A rewrite rule of a constant reached is
   trusted as an axiom is. An axiom is a proposition when its type is a proposition, and a signature otherwise:
   a type, or a function into types, which a theorem holds for in every model, as for a variable. *)
TypeTheoryAxiomClosure[term_TypeTheoryTerm] := catchKernelFailure @ Block[{closureEnvironment = termEnvironment[term]},
	First[closureOf[closureEnvironment, queryCoreTerm[closureEnvironment, term]]]
]

(* the core term of a query; a declared constant on its own is that constant, an overloaded name such as True included *)
queryCoreTerm[environment_, term_] := Replace[aliasResolvedName[environment, heldFromSyntax[termSyntax[term]]], {
	name_ /; constantDeclaredQ[environment, name] :> constantReference[name, {}],
	_ :> First @ checkedQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]
}]

(* {axioms, holes} a term rests on: the axioms as <|name -> kind|>, the holes as <|HoldComplete[hole] -> record|>; the
   subterms seen are shared by the whole closure, so a term the declarations share is walked once *)
closureOf[environment_, term_] := Block[{$closureVisited = <||>, $closureAxioms = <||>, $closureHoles = <||>, $constantsSeen = <||>},
	withKernelCaches[visitTerm[environment, term]];
	{KeyMap[ReleaseHold, $closureAxioms], $closureHoles}
]

termHoles[environment_, term_] := holeGroups[environment, Last[closureOf[environment, queryCoreTerm[environment, term]]]]

(* the annotation of a constant's record: a hole's, or None *)
termAnnotation[environment_, term_] := Replace[queryCoreTerm[environment, term], {
	constantReference[name_, _] :> Lookup[constantRecord[environment, name], "Annotation", None],
	_ :> None
}]

(* the holes by the theorem they are holes of, each with its statement and its annotation *)
holeGroups[environment_, holes_Association] := GroupBy[
	KeyValueMap[
		Function[{name, record}, <|
			"Theorem" -> ReleaseHold[record["Theorem"]],
			"Hole" -> ReleaseHold[name],
			"Statement" -> coreToTypeTheoryTerm[environment, <||>, record["Type"]],
			"Annotation" -> record["Annotation"]
		|>],
		holes
	],
	Function[hole, hole["Theorem"]],
	Map[Function[hole, KeyDrop[hole, "Theorem"]]]
]

visitConstant[environment_, name_] := If[ ! KeyExistsQ[$closureVisited, name],
	$closureVisited[name] = True;
	visitRecord[environment, name, constantRecord[environment, name]];
	Scan[Function[rule, $closureAxioms[rule] = "RewriteRule"], rewriteRuleNames[environment, name]]
]

visitRecord[environment_, name_, record_] := Switch[record["Kind"],
	"Axiom",
		$closureAxioms[name] = If[propositionTypeQ[environment, record["Type"]], "Proposition", "Signature"];
		visitTerm[environment, record["Type"]],
	"Definition" | "Opaque" | "Theorem",
		visitTerm[environment, record["Type"]];
		visitTerm[environment, record["Value"]],
	"InductiveType",
		visitTerm[environment, record["Type"]];
		Scan[Function[constructor, visitConstant[environment, constructor]], record["Constructors"]],
	"Constructor" | "Recursor",
		visitTerm[environment, record["Type"]];
		visitConstant[environment, record["InductiveType"]],
	"RewriteRule",
		$closureAxioms[name] = "RewriteRule",
	"Hole",
		$closureHoles[name] = record;
		visitTerm[environment, record["Type"]],
	_,
		visitTerm[environment, record["Type"]]
]

visitTerm[environment_, term_] := Scan[Function[name, visitConstant[environment, name]], unseenConstants[term]]

propositionTypeQ[environment_, type_] := MatchQ[weakHeadNormalForm[environment, <||>, inferType[environment, <||>, type]], universeSort[0]]

(* the constants the type and the value of a term mention: of a constant, those of its declaration *)
typeAndValueConstants[environment_, term_] := Replace[queryCoreTerm[environment, term], {
	constantReference[name_, _] :> Block[{constantFields = constantRecord[environment, name]},
		DeleteDuplicates[Join @@ Map[termConstants, DeleteMissing[Lookup[constantFields, {"Type", "Value"}]]]]
	],
	core_ :> DeleteDuplicates[Join[termConstants[core], termConstants[withKernelCaches[inferType[environment, <||>, core]]]]]
}]

(* the constants a core term mentions, each shared subterm visited once *)
termConstants[term_] := Block[{$constantsSeen = <||>}, unseenConstants[term]]

(* the constants in the subterms of term not seen yet *)
unseenConstants[term_] := DeleteDuplicates @ Flatten @ Last @ Reap[collectConstants[term], $constantTag]

collectConstants[term_] := If[ ! KeyExistsQ[$constantsSeen, term], $constantsSeen[term] = True; constantsOf[term]]

constantsOf[constantReference[name_, _]] := Sow[name, $constantTag]
constantsOf[application[function_, argument_]] := (collectConstants[function]; collectConstants[argument])
constantsOf[(lambdaAbstraction | dependentFunctionType)[_, domain_, body_, _]] := (collectConstants[domain]; collectConstants[body])
constantsOf[localDefinition[_, type_, value_, body_]] := (collectConstants[type]; collectConstants[value]; collectConstants[body])
constantsOf[projection[structure_, _, term_]] := (Sow[structure, $constantTag]; collectConstants[term])
constantsOf[cubicalSystem[branches_List]] := Scan[collectConstants, Flatten[branches, 1]]
constantsOf[_] := Null


(* ::Subsection:: *)
(*Checking an environment*)


Options[TypeTheoryCheck] = {Method -> Automatic}

(* The compiled kernel (CompiledKernel.wl) checks the declarations but inductive types, their constructors and
   recursors, and quotient types, which are declared again after it, each after the records before it as they are.
   Where it refuses a declaration, those before it are declared again first, so that the failure is that of the first
   declaration in order that does not check. Where it does not handle the environment, or Method -> "Symbolic", every
   declaration is replayed with the kernel of TypeChecking.wl. *)
TypeTheoryCheck[environment_?environmentQ, OptionsPattern[]] := withStoreCleanup @ catchKernelFailure @ Replace[
	If[MemberQ[{Automatic, "Compiled"}, OptionValue[Method]], compiledKernelCheck[environment], None],
	{
		failure_Failure :> (
			replayNames[environment, Take[environmentNames[environment], failure["Position"] - 1], replayGenerated[environment]];
			throwFailure[Failure[failure["Tag"], KeyDrop[Last[failure], "Position"]]]
		),
		None /; OptionValue[Method] === "Compiled" :> kernelFailure[
			"CompiledKernelUnavailable",
			"The compiled kernel has no library for this platform and version, or does not handle this environment.",
			{}
		],
		None :> replayEnvironment[environment, Function[{partial, name, record}, replayDeclaration[environment, partial, name -> record]]],
		_Success :> replayEnvironment[environment, replayGenerated[environment]]
	}
]

(* after the compiled kernel, the inductive types and quotients are declared again, and the other records added as they are *)
replayGenerated[environment_][partial_, name_, record_] := If[
	MemberQ[{"InductiveType", "Constructor", "Recursor", "Quotient"}, record["Kind"]],
	replayDeclaration[environment, partial, name -> record],
	registerWhenDeclared[addConstantRecords[partial, <|name -> record|>], naturalNumberSettings[environment]]
]

replayNames[environment_, names_List, replay_] := Fold[
	Function[{partial, name}, replay[partial, name, constantRecord[environment, name]]],
	emptyEnvironmentOf[environmentRules[environment]],
	names
]

replayEnvironment[environment_, replay_] := With[{replayed = replayNames[environment, environmentNames[environment], replay]},
	If[ naturalNumberSettings[replayed] =!= naturalNumberSettings[environment],
		kernelFailure["DeclarationMismatch", "The natural numbers of the environment do not match its declarations.", {}]
	];
	Success["EnvironmentChecked", <|
		"MessageTemplate" -> "All `1` constants of the environment check again from their declarations.",
		"MessageParameters" -> {Length[environmentNames[environment]]},
		"Constants" -> Length[environmentNames[environment]]
	|>]
]

(* Constructors and recursors are generated with their inductive type, which comes before them; every
   record must come out of the replay exactly as it is in the environment. *)
replayDeclaration[original_, replayed_, name_ -> record_] := With[
	{extended = If[generatedQ[record, name], replayed, redeclare[original, replayed, name, record]]},
	If[ ! constantDeclaredQ[extended, name] || constantRecord[extended, name] =!= record,
		kernelFailure["DeclarationMismatch", "The record of `1` does not match the record that checking its declaration gives.", {HoldForm @@ name}]
	];
	registerWhenDeclared[extended, naturalNumberSettings[original]]
]

redeclare[original_, replayed_, name_, record_] := Replace[record["Kind"], {
	"Axiom" :> declareAxiom[replayed, name, record["UniverseParameters"], record["Type"], Lookup[record, "Annotation", None], Lookup[record, "Overloads", None]],
	"Hole" :> declareHole[replayed, name, record["UniverseParameters"], record["Type"], record["Annotation"], record["Theorem"]],
	"Definition" | "Opaque" :> declareDefinition[replayed, name, record["UniverseParameters"], record["Type"], record["Value"], recordRoles[record]],
	"Theorem" :> declareTheorem[replayed, name, record["UniverseParameters"], record["Type"], record["Value"], Lookup[record, "Annotation", None]],
	"RewriteRule" :> declareRewriteRule[replayed, name, record["UniverseParameters"], record["NumberOfVariables"], record["LeftHandSide"], record["RightHandSide"]],
	"Quotient" :> declareQuotients[replayed, record["Equality"], record["QuotientNames"]],
	"Cubical" :> declareCubical[replayed, record["Sum"]],
	"InductiveType" :> declareInductiveTypes[
		replayed,
		record["UniverseParameters"],
		record["NumberOfParameters"],
		Function[member, member -> constantRecord[original, member]["Type"]] /@ record["Block"],
		Function[constructor, constructor -> constantRecord[original, constructor]["Type"]] /@ Catenate[Function[member, constantRecord[original, member]["Constructors"]] /@ record["Block"]]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name, kind}]
}]

(* ::Subsection:: *)
(*Translations between rules*)


Options[TypeTheoryTranslate] = {"Axioms" -> False}

TypeTheoryTranslate[environment_?environmentQ, rules_?rulesQ, OptionsPattern[]] := withStoreCleanup @ catchKernelFailure @ With[
	{
		direction = Replace[{TrueQ[rulesSetting[environment, "Prop"]], TrueQ[rules["Prop"]]}, {{True, False} -> "LoseProp", {False, True} -> "GainProp", _ -> "SameProp"}],
		axiomsQ = TrueQ[OptionValue["Axioms"]],
		primary = primaryNames[environment]
	},
	{
		result = Fold[
			Function[{state, name}, translateDeclaration[environment, state, name, direction, axiomsQ]],
			<|"Environment" -> emptyEnvironmentOf[rules], "Failures" -> <||>|>,
			primary
		]
	},
	Success["Translated", <|
		"MessageTemplate" -> "`1` of the `2` declarations translate to the rules `3`.",
		"MessageParameters" -> {Length[primary] - Length[result["Failures"]], Length[primary], rules["Name"]},
		"Environment" -> result["Environment"],
		"Failures" -> KeyMap[ReleaseHold, result["Failures"]]
	|>]
]

(* the declaration of name redeclared in the environment of the other rules, or its failure recorded *)
translateDeclaration[original_, state_Association, name_, direction_String, axiomsQ_] := With[{record = constantRecord[original, name]},
	If[ record["Kind"] === "Axiom" && ! axiomsQ,
		Append[state, "Failures" -> Append[state["Failures"], name -> Failure["AxiomLeftOut", <|
			"MessageTemplate" -> "`1` is an axiom, which a translation keeps only with \"Axioms\" -> True.",
			"MessageParameters" -> {HoldForm @@ name}
		|>]]],
		Replace[catchKernelFailure[translatedDeclaration[original, state["Environment"], name, record, direction]], {
			failure_Failure :> Append[state, "Failures" -> Append[state["Failures"], name -> failure]],
			extended_ :> Append[state, "Environment" -> Replace[catchKernelFailure[registerWhenDeclared[extended, naturalNumberSettings[original]]], _Failure -> extended]]
		}]
	]
]

(* the recursors' levels lowered, or else kept, where the rules lose Prop *)
translatedDeclaration[original_, target_, name_, record_, direction_String] := With[
	{attempt = Function[mode, catchKernelFailure[translatedRecord[original, target, name, record, direction, Function[term, translatedTerm[original, target, direction, mode, term]]]]]},
	Replace[attempt["Lowered"], failure_Failure /; direction === "LoseProp" :> Replace[attempt["Kept"], _Failure -> failure]]
]

translatedRecord[original_, target_, name_, record_, direction_, translate_] := Replace[record["Kind"], {
	"Axiom" :> declareAxiom[target, name, record["UniverseParameters"], translate[record["Type"]], Lookup[record, "Annotation", None], Lookup[record, "Overloads", None]],
	"Hole" :> declareHole[target, name, record["UniverseParameters"], translate[record["Type"]], record["Annotation"], record["Theorem"]],
	"Definition" | "Opaque" :> declareDefinition[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]], recordRoles[record]],
	"Theorem" /; direction === "GainProp" :> declareDefinition[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]]],
	"Theorem" :> declareTheorem[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]], Lookup[record, "Annotation", None]],
	"RewriteRule" :> declareRewriteRule[target, name, record["UniverseParameters"], record["NumberOfVariables"], translate[record["LeftHandSide"]], translate[record["RightHandSide"]]],
	"Quotient" :> declareQuotients[target, record["Equality"], record["QuotientNames"]],
	"Cubical" :> declareCubical[target, record["Sum"]],
	"InductiveType" :> With[
		{
			constructorTypes = Function[constructor, constructor -> translate[constantRecord[original, constructor]["Type"]]] /@
				Catenate[Function[member, constantRecord[original, member]["Constructors"]] /@ record["Block"]]
		},
		declareInductiveTypes[
			target,
			record["UniverseParameters"],
			record["NumberOfParameters"],
			Function[member, member -> raisedProposition[original, target, direction, record, constructorTypes, member, translate[constantRecord[original, member]["Type"]]]] /@ record["Block"],
			constructorTypes
		]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name}]
}]

(* an inductive proposition, where the rules lose Prop, lives in the universe of its largest field that is
   not of a type of its block, and in Type at least *)
raisedProposition[original_, target_, "LoseProp", record_, constructorTypes_List, member_, type_] /; conclusionSort[constantRecord[original, member]["Type"]] === universeSort[0] :=
	withConclusion[type, universeSort[normalizeLevel[levelMaximum @@ Prepend[
		Catenate[Function[constructor, fieldLevels[target, <||>, record["NumberOfParameters"], record["Block"], Last[constructor], {}]] /@ constructorTypes],
		1
	]]]]
raisedProposition[_, _, _, _, _, _, type_] := type

conclusionSort[dependentFunctionType[_, _, codomain_, _]] := conclusionSort[codomain]
conclusionSort[sort_] := sort

withConclusion[dependentFunctionType[name_, domain_, codomain_, binder_], sort_] := Construct[dependentFunctionType, name, domain, withConclusion[codomain, sort], binder]
withConclusion[_, sort_] := sort

(* the universes of a constructor's fields, its parameters skipped *)
fieldLevels[target_, context_, skipped_Integer, block_List, dependentFunctionType[name_, domain_, codomain_, binder_], levels_List] := With[{id = freshFreeVariable[]},
	fieldLevels[
		target,
		extendContext[context, id, name, domain, binder],
		Max[skipped - 1, 0],
		block,
		instantiateBoundVariable[codomain, freeVariable[id]],
		If[ skipped > 0 || ! FreeQ[domain, constantReference[Alternatives @@ block, _]], levels, Append[levels, sortLevel[target, context, domain]]]
	]
]
fieldLevels[_, _, _, _, _, levels_List] := levels

(* Where the rules lose Prop, Prop becomes Type, the lowest universe of types, and every other sort stays: a
   level l becomes max(l, 1), so a constant keeps its universe levels, its own sorts lifted the same way. A
   recursor's level moves with the meaning of its motive's universe. *)
translatedTerm[original_, target_, direction_, mode_, term_] := ReplaceAll[If[TrueQ[rulesSetting[target, "Quantities"]], term, withoutQuantities[term]], {
	universeSort[level_] /; direction === "LoseProp" :> With[{lifted = normalizeLevel[levelMaximum[level, 1]]}, universeSort[lifted] /; True],
	constantReference[name : HoldComplete[_InductiveRecursor], levels_List] :> With[{moved = recursorLevels[original, target, direction, mode, name, levels]}, constantReference[name, moved] /; True]
}]

(* the levels of a recursor in the other rules: its first is the universe its motive goes into, if it has one *)
recursorLevels[original_, target_, direction_, mode_, name_, levels_List] := With[
	{
		sourceUniverse = TrueQ[constantRecord[original, name]["EliminationUniverse"]],
		targetUniverse = constantDeclaredQ[target, name] && TrueQ[constantRecord[target, name]["EliminationUniverse"]]
	},
	Which[
		direction === "LoseProp" && sourceUniverse && targetUniverse && mode === "Lowered", Prepend[Rest[levels], loweredUniverse[First[levels]]],
		direction === "LoseProp" && ! sourceUniverse && targetUniverse, Prepend[levels, 0],
		direction === "GainProp" && sourceUniverse && targetUniverse, Prepend[Rest[levels], normalizeLevel[levelSuccessor[First[levels], 1]]],
		True, levels
	]
]

(* the level u with Sort (u + 1) the translation of Sort l, max(l, 1): l less one, or 0 for Prop; a universe
   parameter that may be 0 has none, and stays, so what uses it fails to check *)
loweredUniverse[level_Integer] := Max[level, 1] - 1
loweredUniverse[levelSuccessor[base_, k_Integer]] /; k >= 1 := normalizeLevel[levelSuccessor[base, k - 1]]
loweredUniverse[level_] := level

(* each registration of the natural numbers is replayed as soon as the constants it names are declared *)
registerWhenDeclared[replayed_, settings_Association] := With[
	{next = Replace[naturalNumberSettings[replayed], {registered_Association :> Length[registered["Registrations"]] + 1, None -> 1}]},
	If[ next <= Length[settings["Registrations"]] && AllTrue[registrationNames[settings, next], Function[name, constantDeclaredQ[replayed, name]]],
		registerWhenDeclared[registerNaturalNumbers[replayed, registrationOf[settings, next]], settings],
		replayed
	]
]
registerWhenDeclared[replayed_, None] := replayed
