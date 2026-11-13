(* ::Package:: *)

(*
Declarations: the constructors TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem,
TypeTheoryInductiveType, TypeTheoryNaturalNumbers, TypeTheoryRewriteRule and TypeTheoryQuotients, and the
environments built from them.

A declaration is inert data. Its arguments are held, so it reads like mathematics and nothing in it
evaluates, and it means nothing until it is added to an environment:

	TypeTheoryAxiom[name, type]
	TypeTheoryDefinition[name, value]                           value may be Typed[v, type]
	TypeTheoryDefinition[name, value, "Opaque" -> True]         checked as a definition, but never unfolded
	TypeTheoryTheorem[name, statement, proof]
	TypeTheoryTheorem[name, proof]                              proof a finished TypeTheoryProof
	TypeTheoryInductiveType[name, type, {constructor -> type, ...}]
	TypeTheoryInductiveType[{name -> type, ...}, {constructor -> type, ...}]
	                                                            mutually inductive types
	TypeTheoryNaturalNumbers[type, zero, successor]            the literals 0, 1, 2, ... become elements of type
	TypeTheoryNaturalNumbers[type, zero, successor, <|role -> operation, ...|>]
	                                                            and the operations compute on literals
	TypeTheoryNaturalNumbers[type, zero, successor, addition]   the same, with addition the only operation
	TypeTheoryRewriteRule[name, ForAll[binders, lhs -> rhs]]    lhs, an axiom applied to arguments, computes to rhs
	TypeTheoryQuotients[]                                       the quotient types (Quotients.wl)
	TypeTheoryQuotients[equality, {type, introduction, lift, induction}]
	                                                            the same under other names, with another equality
	TypeTheoryCubical[sum]                                      the interval, paths, transport and composition of cubical
	                                                            type theory (Cubical.wl)

TypeTheoryEnvironment[environment, {declaration, ...}] elaborates each declaration's terms in the
environment so far, has the kernel check them, and gives the extended environment, or a Failure for the
first declaration that does not check. Append[environment, declaration] adds one declaration.

TypeTheoryEnvironment[rules] starts an environment with no constants that follows the TypeTheoryRules
rules; every environment made from it follows them too. Rewrite rules may only be declared where the
rules allow them, and under rules without Prop a theorem may state any type. Under rules with
quantities, the value of a definition, the proof of a theorem and the right side of a rewrite rule pass
the live check of Quantities.wl.

A name is any expression: a symbol, or a string for a constant imported from elsewhere. Universe
parameters are the symbols and strings in universe levels, in the order they first appear; the option
"UniverseParameters" lists them explicitly.

The core functions declareAxiom, declareDefinition and declareTheorem take core terms. Like
declareInductiveType and registerNaturalNumbers, they check everything themselves and throw a kernel
failure when a check fails.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryAxiom]
PackageExported[TypeTheoryDefinition]
PackageExported[TypeTheoryTheorem]
PackageExported[TypeTheoryInductiveType]
PackageExported[TypeTheoryNaturalNumbers]
PackageExported[TypeTheoryRewriteRule]
PackageExported[TypeTheoryQuotients]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[$recheckedConstants]
PackageScoped[coreRecordsOf]
PackageScoped[declareAxiom]
PackageScoped[declareDefinition]
PackageScoped[declareTheorem]
PackageScoped[declareRewriteRule]
PackageScoped[emptyEnvironmentOf]
PackageScoped[addDeclaration]
PackageScoped[declarationQ]
PackageScoped[declarationUniverseParameters]
PackageScoped[universeParameterNames]
PackageScoped[heldOptionValue]
PackageScoped[$emptyEnvironment]
PackageScoped[$deferKernelChecks]


(* ::Section:: *)
(*Usage Messages*)


coreRecordsOf::usage = "coreRecordsOf[environment, <|HoldComplete[name] -> record, ...|>] gives the records that declaring each axiom, theorem, \
opaque constant and definition again in environment gives, in order and with the checks deferred, from the kind, the type, the value and the \
universe parameters of its record: the records a batch of such declarations gives."
$recheckedConstants::usage = "$recheckedConstants is the list of the constants that the compiled kernel left undecided and the kernel of TypeChecking.wl checked, in the last batch of declarations or the last TypeTheoryCheck of an environment."
TypeTheoryAxiom::usage = "TypeTheoryAxiom[name, type] declares name as an axiom of the given type, when added to a TypeTheoryEnvironment.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear."
TypeTheoryDefinition::usage = "TypeTheoryDefinition[name, value] declares name as a definition with the given value, when added to a TypeTheoryEnvironment.\n\
TypeTheoryDefinition[name, Typed[value, type]] gives the definition the given type.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear. \
The option \"Instance\" -> True makes the definition an instance of its type's class, the constant its type applies at the end, which elaboration finds \
for an argument of an instance-implicit binder. The option \"Coercion\" -> True makes a function of one explicit argument a coercion, which elaboration \
applies to a term whose type is the function's domain where its codomain is expected. The option \"Opaque\" -> True makes the definition opaque: \
its value is checked against its type, but it never unfolds, so it equals only itself."
TypeTheoryTheorem::usage = "TypeTheoryTheorem[name, statement, proof] declares name as a theorem: proof must prove statement when it is added to a TypeTheoryEnvironment. \
statement must be a proposition, or under rules without Prop any type; a theorem is never unfolded.\n\
TypeTheoryTheorem[name, proof] declares the statement of the finished TypeTheoryProof proof.\n\
proof is a term, a TypeTheoryTerm or a finished TypeTheoryProof. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryInductiveType::usage = "TypeTheoryInductiveType[name, type, {constructor1 -> type1, ...}] declares the inductive type name with the given constructors, \
and its recursor InductiveRecursor[name], when added to a TypeTheoryEnvironment.\n\
The option \"Parameters\" -> n makes the first n arguments of name parameters, which every constructor takes first and passes on unchanged; \
Automatic takes as many as every constructor allows. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryRewriteRule::usage = "TypeTheoryRewriteRule[name, ForAll[{Typed[x, type], ...}, lhs -> rhs]] declares that lhs computes to rhs for every \
x, ..., when added to a TypeTheoryEnvironment whose rules allow rewrite rules.\n\
lhs must be an axiom applied to arguments in which each variable occurs, and rhs must have the type of lhs. Like an axiom, a rewrite rule is \
trusted: it may make the theory inconsistent, or computation endless. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryQuotients::usage = "TypeTheoryQuotients[] declares the quotient types, QuotientType, QuotientIntroduction, QuotientLift and \
QuotientInduction, when added to a TypeTheoryEnvironment whose rules have quotients and whose Equal is the equality of the prelude: \
QuotientLift[f, h, QuotientIntroduction[r, a]] computes to f[a].\n\
TypeTheoryQuotients[equality, {type, introduction, lift, induction}] declares them under the given names, with the inductive type equality as the equality."
TypeTheoryNaturalNumbers::usage = "TypeTheoryNaturalNumbers[type, zero, successor] registers the inductive type type, with the constructors zero and successor, \
as the natural numbers, so the literals 0, 1, 2, ... are elements of type.\n\
TypeTheoryNaturalNumbers[type, zero, successor, <|role -> operation, ...|>] also registers operations that the kernel computes on literals with integers, \
trusting that each computes what its role names: \"Addition\", \"Subtraction\", \"Multiplication\", \"Power\", \"Quotient\", \"Remainder\", \"GCD\", \"Log2\", \
\"BitAnd\", \"BitOr\", \"BitXor\", \"ShiftLeft\", \"ShiftRight\", and \"Equal\" and \"LessEqual\", which give Booleans. A later registration of the same \
natural numbers adds operations.\n\
TypeTheoryNaturalNumbers[type, zero, successor, addition] registers addition as the only operation."

declareAxiom::usage = "declareAxiom[environment, HoldComplete[name], {HoldComplete[u], ...}, type] checks the core type and gives environment with the axiom name added."
declareDefinition::usage = "declareDefinition[environment, HoldComplete[name], {HoldComplete[u], ...}, type, value] checks the core value against the core type \
and gives environment with the definition name added.\n\
declareDefinition[environment, HoldComplete[name], {HoldComplete[u], ...}, type, value, <|\"Instance\" -> True, \"Coercion\" -> True|>] adds it as an instance or \
a coercion for elaboration, which the kernel checks as any definition. With \"Opaque\" -> True its record is of the kind \"Opaque\", which never unfolds."
declareTheorem::usage = "declareTheorem[environment, HoldComplete[name], {HoldComplete[u], ...}, statement, proof] checks that statement is a proposition, or \
under rules without Prop a type, and that proof proves it, and gives environment with the theorem name added."
declareRewriteRule::usage = "declareRewriteRule[environment, HoldComplete[name], {HoldComplete[u], ...}, numberOfVariables, left, right] checks the rewrite rule \
whose sides are the core functions left and right of its variables, and gives environment with it added."
emptyEnvironmentOf::usage = "emptyEnvironmentOf[rules] gives the environment with no constants that follows rules, the same one each time."
addDeclaration::usage = "addDeclaration[environment, declaration] elaborates and checks the declaration and gives the extended environment, or throws a kernel failure."
declarationQ::usage = "declarationQ[expr] gives True if expr is a declaration: TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, \
TypeTheoryNaturalNumbers, TypeTheoryRewriteRule, TypeTheoryQuotients or TypeTheoryCubical."
declarationUniverseParameters::usage = "declarationUniverseParameters[head, Hold[options], {syntax, ...}] gives the universe parameters {HoldComplete[u], ...} \
of a declaration from its \"UniverseParameters\" option, or from the universe levels in the syntax trees."
universeParameterNames::usage = "universeParameterNames[{syntax, ...}] gives the symbols and strings in universe levels of the syntax trees, \
as {HoldComplete[u], ...} in the order they first appear."
heldOptionValue::usage = "heldOptionValue[head, Hold[options], name] gives HoldComplete[value] for the option name among the held options, or among the defaults Options[head]."
$emptyEnvironment::usage = "$emptyEnvironment is the environment with no constants, in which a TypeTheoryTerm without an environment is checked."
$deferKernelChecks::usage = "$deferKernelChecks is True while declarations are added for the compiled kernel to check them all at once: axioms, definitions, \
theorems and holes are added without the kernel's checks, inductive types with them but the universes of their constructors' fields."


(* ::Section:: *)
(*Function Definitions*)


Options[TypeTheoryAxiom] = {"UniverseParameters" -> Automatic, "Annotation" -> None, "Overloads" -> None, "Implementation" -> None}
Options[TypeTheoryDefinition] = {"UniverseParameters" -> Automatic, "Instance" -> False, "Coercion" -> False, "Opaque" -> False, "Overloads" -> None}
Options[TypeTheoryTheorem] = {"UniverseParameters" -> Automatic, "Annotation" -> None}
Options[TypeTheoryInductiveType] = {"Parameters" -> Automatic, "UniverseParameters" -> Automatic}
Options[TypeTheoryRewriteRule] = {"UniverseParameters" -> Automatic}

SetAttributes[{TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, TypeTheoryNaturalNumbers, TypeTheoryRewriteRule, TypeTheoryQuotients, TypeTheoryCubical}, HoldAll]
(* a sequence, Sequence[a, b], is a term, not the arguments a and b *)
SetAttributes[{TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, TypeTheoryNaturalNumbers, TypeTheoryRewriteRule, TypeTheoryQuotients, TypeTheoryCubical}, SequenceHold]

declarationQ[_TypeTheoryAxiom | _TypeTheoryDefinition | _TypeTheoryTheorem | _TypeTheoryInductiveType | _TypeTheoryNaturalNumbers | _TypeTheoryRewriteRule] := True
declarationQ[TypeTheoryQuotients[] | TypeTheoryQuotients[_, {_, _, _, _}] | TypeTheoryCubical[_]] := True
declarationQ[_] := False


(* ::Subsection:: *)
(*Environments from declarations*)


(* without an environment to extend, declarations extend the default environment; TypeTheoryEnvironment[] has none *)
TypeTheoryEnvironment[] := $emptyEnvironment
TypeTheoryEnvironment[rules_TypeTheoryRules?rulesQ] := emptyEnvironmentOf[rules]
TypeTheoryEnvironment[rules_TypeTheoryRules?rulesQ, declarations : (_List | _?declarationQ)] := TypeTheoryEnvironment[emptyEnvironmentOf[rules], declarations]
TypeTheoryEnvironment["Prelude"] := preludeEnvironment[]
TypeTheoryEnvironment["Constructive"] := constructiveEnvironment[]
TypeTheoryEnvironment["HomotopyTypeTheory"] := homotopyTypeTheoryEnvironment[]
TypeTheoryEnvironment["Integers"] := integersEnvironment[]
TypeTheoryEnvironment["Rationals"] := rationalsEnvironment[]
TypeTheoryEnvironment["Machine"] := machineEnvironment[]
TypeTheoryEnvironment["MachineReals"] := machineRealsEnvironment[]
TypeTheoryEnvironment["Cubical"] := cubicalEnvironment[]
TypeTheoryEnvironment["WolframLanguage"] := wolframLanguageEnvironment[]
TypeTheoryEnvironment[name_String] := Failure["UnknownEnvironment", <|
	"MessageTemplate" -> "`1` is not the name of a library environment, which are `2`.",
	"MessageParameters" -> {name, $environmentNames}
|>]
(* a library environment by its name, extended *)
TypeTheoryEnvironment[name_String, rest__] := Replace[TypeTheoryEnvironment[name], environment_?environmentQ :> TypeTheoryEnvironment[environment, rest]]
TypeTheoryEnvironment[declarations_List, options : OptionsPattern[]] := TypeTheoryEnvironment[defaultEnvironment[], declarations, options]
(* rules or an environment that failed, as rules of a name of none *)
TypeTheoryEnvironment[failure_Failure, ___] := failure
TypeTheoryEnvironment[declaration_?declarationQ] := TypeTheoryEnvironment[defaultEnvironment[], {declaration}]
TypeTheoryEnvironment[environment_?environmentQ, declaration_?declarationQ] := TypeTheoryEnvironment[environment, {declaration}]

Options[TypeTheoryEnvironment] = {Method -> Automatic}

(* the stores of the steps in between are removed, and so are all of them when a declaration fails; with
   Method -> "Compiled" the compiled kernel checks the declarations at once, after they are all added *)
TypeTheoryEnvironment[environment_?environmentQ, declarations_List, OptionsPattern[]] := withStoreCleanup @ catchKernelFailure @ If[
	OptionValue[Method] === "Compiled" && compiledKernelAvailableQ[],
	compiledDeclarations[environment, declarations],
	Fold[addDeclaration, environment, declarations]
]

(* Axioms, definitions, theorems and holes are added without the kernel's checks, and inductive types with them but
   for the universes of their constructors' fields; then the compiled kernel checks every declaration added, in order. Where adding one fails, or the compiled kernel
   does not handle the environment, the declarations are added again with each one checked, so that a failure is
   that of the first declaration in order that does not check. *)
compiledDeclarations[environment_, declarations_List] := Replace[
	(* a registration among the declarations leaves to the compiled kernel the equations it checks: the declarations are
	   kept only where its check succeeds, and where it refuses an equation they are added again one at a time, the
	   registration comparing its equations itself and naming the one that fails *)
	catchKernelFailure[Block[{$deferKernelChecks = True, $deferRegistrationEquations = True}, $recheckedConstants = {}; deferredDeclarations[environment, declarations]]],
	{
		_Failure :> Fold[addDeclaration, environment, declarations],
		extended_ :> Replace[compiledKernelCheck[extended, Length[environmentNames[environment]], registrationCount[environment], declarationRecheck[environment, declarations, extended]], {
			failure_Failure /; TrueQ[failure["RegistrationEquation"]] :> Fold[addDeclaration, environment, declarations],
			failure_Failure :> throwFailure[Failure[failure["Tag"], KeyDrop[Last[failure], "Position"]]],
			None :> Fold[addDeclaration, environment, declarations],
			_Success :> extended
		}]
	}
]

(* The recheck of a record that the compiled kernel leaves undecided, in an environment with a literal it does not hold:
   the declaration of the record's constant is added by addDeclaration, which checks it with the kernel of
   TypeChecking.wl, to the environment of the declarations before it, as it would be with the declarations added one at
   a time. Those before it are added unchecked, as the batch was: the compiled kernel has accepted their records, or
   they were checked here; a registration among them compares its equations itself, the compiled kernel not having
   reached them yet, so $deferRegistrationEquations is not bound here. It gives the record's position, through which
   the compiled kernel then takes the constants as they are; the Failure of the declaration, which is the batch's; or
   None, for which the declarations are added one at a time, where the constant is no declaration's of the batch, the
   declarations are not met in order, or the record checked is not the record the batch has. $recheckedConstants lists
   the constants given to this check in the last batch. *)
declarationRecheck[environment_, declarations_List, extended_] := Module[
	(* the declarations are kept in a variable: written into the function, their list would be walked at each call *)
	{batch = declarations, names = environmentNames[extended], owners = declarationOwners[declarations], prefix = environment, added = 0, done = <||>},
	Function[position, With[{name = Extract[names, position]},
		{index = Lookup[owners, Key[Lookup[constantRecord[extended, name], "InductiveType", name]], None]},
		Which[
			! IntegerQ[index], None,
			KeyExistsQ[done, index], position,
			index <= added, None,
			True,
				AppendTo[$recheckedConstants, name];
				prefix = Block[{$deferKernelChecks = True}, deferredDeclarations[prefix, Take[batch, {added + 1, index - 1}]]];
				Replace[catchKernelFailure[addDeclaration[prefix, Extract[batch, index]]], {
					failure_Failure :> failure,
					checked_ :> (
						prefix = checked;
						added = index;
						done[index] = True;
						If[constantRecord[checked, name] === constantRecord[extended, name], position, None]
					)
				}]
		]
	]]
]

$recheckedConstants = {}

(* the declaration, by its place in the list, of each name the declarations give: a constructor or a recursor is its
   inductive type's *)
declarationOwners[declarations_List] := Association[MapIndexed[
	Function[{declaration, index}, Function[name, name -> First[index]] /@ declaredNames[declaration]],
	declarations
]]

declaredNames[declaration : (_TypeTheoryAxiom | _TypeTheoryDefinition | _TypeTheoryTheorem)] := {HoldComplete @@ Take[declaration, 1]}
declaredNames[TypeTheoryInductiveType[types : {(_Rule | _RuleDelayed) ..}, ___]] := Cases[Unevaluated[types], (Rule | RuleDelayed)[type_, _] :> HoldComplete[type]]
declaredNames[declaration_TypeTheoryInductiveType] := {HoldComplete @@ Take[declaration, 1]}
declaredNames[TypeTheoryQuotients[_, constants_List]] := Cases[Unevaluated[constants], constant_ :> HoldComplete[constant]]
declaredNames[_] := {}

$deferKernelChecks = False

registrationCount[environment_] := Replace[naturalNumberSettings[environment], {settings_Association :> Length[settings["Registrations"]], _ -> 0}]

(* With the checks deferred, a run of axioms, definitions and theorems given as core terms, with no option but their
   universe parameters as strings and a definition's "Opaque", as an import writes them, gives its records at once,
   the records declareAxiom, declareDefinition and declareTheorem give, and they are added in one step: adding each
   would make a store of its own, and a declaration's options, elaboration and roles cost more than its record. Any
   failure, as a name declared twice, sends the batch to the declarations one at a time, which report it. *)
deferredDeclarations[environment_, declarations_List] := withRecordHeights[Fold[deferredRun, environment, SplitBy[declarations, coreDeclarationQ]]]

deferredRun[environment_, run : {first_, ___}] /; coreDeclarationQ[first] := addConstantRecords[environment, coreRecords[environment, run]]
deferredRun[environment_, run_List] := Fold[addDeclaration, environment, run]

With[{core = _application | _lambdaAbstraction | _dependentFunctionType | _localDefinition | _projection | _constantReference | _universeSort | _naturalLiteral},
	coreDeclarationQ[TypeTheoryAxiom[_String, core, "UniverseParameters" -> {___String}]] := True;
	coreDeclarationQ[TypeTheoryTheorem[_String, core, core, "UniverseParameters" -> {___String}]] := True;
	coreDeclarationQ[TypeTheoryDefinition[_String, Typed[core, core], "UniverseParameters" -> {___String}, Repeated["Opaque" -> True | False, {0, 1}]]] := True
]
coreDeclarationQ[_] := False

(* in order, so that a definition's height takes those of the definitions before it in the run; the heights of the
   constants the batch's definitions mention are kept for the batch, as a constant's height stays what it was declared
   with, where looking each up in the environment again for every definition mentioning it was most of a run's time *)
coreRecords[environment_, run_List] := With[{names = Function[declaration, HoldComplete @@ Take[declaration, 1]] /@ run},
	If[ ! DuplicateFreeQ[names],
		kernelFailure["AlreadyDeclared", "`1` is already declared.", {HoldForm @@ First[Select[Tally[names], Function[pair, Last[pair] > 1]]][[1]]}]
	];
	AssociationThread[names, MapThread[coreRecord[environment], {names, run}]]
]

coreRecord[environment_][name_, TypeTheoryAxiom[_, type_, "UniverseParameters" -> parameters_]] := coreRecordOf[environment][name, "Axiom", type, None, HoldComplete /@ parameters]
coreRecord[environment_][name_, TypeTheoryTheorem[_, statement_, proof_, "UniverseParameters" -> parameters_]] := coreRecordOf[environment][name, "Theorem", statement, proof, HoldComplete /@ parameters]
coreRecord[environment_][name_, TypeTheoryDefinition[_, Typed[value_, type_], "UniverseParameters" -> parameters_, "Opaque" -> True]] := coreRecordOf[environment][name, "Opaque", type, value, HoldComplete /@ parameters]
coreRecord[environment_][name_, TypeTheoryDefinition[_, Typed[value_, type_], "UniverseParameters" -> parameters_, ___]] := coreRecordOf[environment][name, "Definition", type, value, HoldComplete /@ parameters]

(* the record of a core axiom, theorem, opaque constant or definition from its kind, type, value and universe
   parameters, the record declareAxiom, declareTheorem and declareDefinition give with no option but "Opaque" *)
coreRecordOf[environment_][name_, "Axiom", type_, _, parameters_] := (
	heights[name] = 0;
	<|"Kind" -> "Axiom", "Type" -> type, "UniverseParameters" -> parameters|>
)
coreRecordOf[environment_][name_, "Theorem", type_, value_, parameters_] := (
	heights[name] = 0;
	<|"Kind" -> "Theorem", "Type" -> type, "UniverseParameters" -> parameters, "Value" -> value|>
)
coreRecordOf[environment_][name_, "Opaque", type_, value_, parameters_] := (
	heights[name] = 0;
	<|"Kind" -> "Opaque", "Type" -> type, "UniverseParameters" -> parameters, "Value" -> value|>
)
coreRecordOf[environment_][name_, "Definition", type_, value_, parameters_] := With[
	{height = 1 + Max[0, Function[constant, Lookup[heights, Key[constant], heights[constant] = Lookup[constantRecord[environment, constant], "Height", 0]]] /@
		DeleteDuplicates[Cases[value, constantReference[constant_, _] :> constant, {0, Infinity}]]]},
	heights[name] = height;
	Join[
		<|"Kind" -> "Definition", "Type" -> type, "UniverseParameters" -> parameters, "Value" -> value, "Height" -> height|>,
		If[projectionFunctionQ[value], <|"Hint" -> "Abbreviation"|>, <||>]
	]
]

(* the records of a run of records declared again, in order, so that a definition's height takes those of the
   definitions made before it in the run *)
coreRecordsOf[environment_, records_Association] := withRecordHeights[
	Association[KeyValueMap[
		Function[{name, record}, name -> coreRecordOf[environment][name, record["Kind"], record["Type"], Lookup[record, "Value", None], record["UniverseParameters"]]],
		records
	]]
]

(* the heights of the definitions a batch makes, which coreRecordOf reads and sets, kept for the batch alone *)
SetAttributes[withRecordHeights, HoldAll]
withRecordHeights[body_] := Block[{heights = <||>}, body]

TypeTheoryEnvironment /: Append[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, declaration_] := TypeTheoryEnvironment[environment, {declaration}]

(* one empty environment per rules, kept for the session *)
emptyEnvironmentOf[rules_] /; rules === $defaultRules := $emptyEnvironment
emptyEnvironmentOf[rules_] := Lookup[$emptyEnvironments, Key[rules], $emptyEnvironments[rules] = withoutStoreTracking[emptyEnvironment[rules]]]

$emptyEnvironments = <||>


addDeclaration[environment_, TypeTheoryAxiom[name_, type_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryAxiom, Hold[options], {toSyntax[type]}]},
	Replace[generalizedType[environment, HoldComplete[type], universeParameters], {core_, parameters_} :>
		declareAxiom[environment, HoldComplete[name], parameters, core, declarationAnnotation[Hold[options]], declarationOverloads[Hold[options]], declarationImplementation[Hold[options]]]
	]
]

(* a type elaborated with each level nothing decided made a universe parameter: {type, universe parameters} *)
generalizedType[environment_, held_HoldComplete, universeParameters_List] := Block[{$levelGeneralization = "Parameters", $generalizedLevels = {}},
	With[{core = closedType[environment, held, universeParameters]}, {core, Join[universeParameters, $generalizedLevels]}]
]

(* the operation an "Overloads" option names, one of those whose meanings elaboration chooses by the types *)
declarationOverloads[Hold[options___]] := Replace[Cases[Hold[options], HoldPattern["Overloads" -> operation_] :> HoldComplete[operation], {1}], {
	{} -> None,
	{HoldComplete[None], ___} -> None,
	{operation : HoldComplete[Plus | Times | Subtract | Power | Minus | LessEqual | Less | GreaterEqual | Greater], ___} :> operation,
	{other_, ___} :> kernelFailure[
		"OverloadedOperation",
		"`1` cannot be overloaded: \"Overloads\" takes Plus, Times, Subtract, Power, Minus, LessEqual, Less, GreaterEqual or Greater.",
		{HoldForm @@ other}
	]
}]

overloadsField[None] := <||>
overloadsField[operation_HoldComplete] := <|"Overloads" -> operation|>

(* The Wolfram Language function an axiom names as what computes it, as a symbol: the constant stays opaque to the
   kernel, which never runs it, and a saved environment keeps only the name, so that loading one runs nothing; the
   definitions come from the paclet that defines the symbol. *)
declarationImplementation[Hold[options___]] := Replace[Cases[Hold[options], HoldPattern["Implementation" -> implementation_] :> HoldComplete[implementation], {1}], {
	{} -> None,
	{HoldComplete[None], ___} -> None,
	{implementation : HoldComplete[_Symbol], ___} :> implementation,
	{HoldComplete[other_], ___} :> kernelFailure[
		"InvalidOption",
		"The value of the option \"Implementation\" must be a symbol, the function that computes the constant, not `1`.",
		{HoldForm[other]}
	]
}]

implementationField[None] := <||>
implementationField[implementation_HoldComplete] := <|"Implementation" -> implementation|>

(* the "Annotation" given, evaluated, kept in the record as it is; None for none *)
declarationAnnotation[Hold[options___]] := Replace[Cases[Hold[options], HoldPattern["Annotation" -> annotation_] :> annotation, {1}], {{} -> None, {annotation_, ___} :> annotation}]

annotationField[None] := <||>
annotationField[annotation_] := <|"Annotation" -> annotation|>

(* a definition keeps the type it is given, implicit binders included, and its value only has to have
   that type: an imported projection, for one, takes its parameters explicitly in the value *)
addDeclaration[environment_, TypeTheoryDefinition[name_, Typed[value_, type_], options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryDefinition, Hold[options], {toSyntax[Typed[value, type]]}]},
	Replace[generalizedType[environment, HoldComplete[type], universeParameters], {typeCore_, parameters_} :>
		declareDefinition[
			environment, HoldComplete[name], parameters, typeCore, closedValue[environment, HoldComplete[value], typeCore, parameters],
			Join[definitionRoles[Hold[options], typeCore], overloadsField[declarationOverloads[Hold[options]]]]
		]
	]
]

addDeclaration[environment_, TypeTheoryDefinition[name_, value_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryDefinition, Hold[options], {toSyntax[value]}]},
	{elaborated = elaborateClosedTerm[environment, HoldComplete[value], None, universeParameters]},
	declareDefinition[
		environment, HoldComplete[name], universeParameters, betaNormalize[Last[elaborated]], First[elaborated],
		Join[definitionRoles[Hold[options], betaNormalize[Last[elaborated]]], overloadsField[declarationOverloads[Hold[options]]]]
	]
]

(* the roles the options give a definition: for elaboration, an instance's type, under its binders, is a
   constant applied to arguments, its class, and a coercion's type, under its implicit binders, is a
   function of an explicit argument; for the kernel, a definition of any type may be opaque *)
definitionRoles[heldOptions_Hold, type_] := Select[
	<|
		"Instance" -> roleOption[heldOptions, "Instance", MatchQ[First @ applicationSpine[functionTypeConclusion[type]], _constantReference],
			"InstanceTypeExpected", "The type of an instance must be a class, a constant applied to arguments, under its binders."],
		"Coercion" -> roleOption[heldOptions, "Coercion", MatchQ[explicitFunctionType[type], dependentFunctionType[_, _, _, binder_ /; binderKind[binder] === "Explicit"]],
			"CoercionTypeExpected", "The type of a coercion must be a function of an explicit argument, under its implicit binders."],
		"Opaque" -> roleOption[heldOptions, "Opaque"]
	|>,
	TrueQ
]

roleOption[heldOptions_Hold, option_String] := roleOption[heldOptions, option, True, None, None]
roleOption[heldOptions_Hold, option_String, fitsQ_, tag_, message_] := Replace[heldOptionValue[TypeTheoryDefinition, heldOptions, option], {
	HoldComplete[False] -> False,
	HoldComplete[True] /; fitsQ -> True,
	HoldComplete[True] :> kernelFailure[tag, message, {}],
	HoldComplete[other_] :> kernelFailure["InvalidOption", "The value of the option `1` must be True or False, not `2`.", {option, HoldForm[other]}]
}]

functionTypeConclusion[dependentFunctionType[_, _, codomain_, _]] := functionTypeConclusion[codomain]
functionTypeConclusion[type_] := type

explicitFunctionType[dependentFunctionType[_, _, codomain_, binder_]] /; binderKind[binder] =!= "Explicit" := explicitFunctionType[codomain]
explicitFunctionType[type_] := type

(* a proof with holes declares a constant for each before the theorem (Holes.wl); the statement has none *)
addDeclaration[environment_, TypeTheoryTheorem[name_, statement_, proof_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryTheorem, Hold[options], {toSyntax[statement], toSyntax[proof]}]},
	Replace[Block[{$propositionExpected = True}, generalizedType[environment, HoldComplete[statement], universeParameters]], {type_, parameters_} :>
		Block[{$elaboratedHoles = {}},
			declareTheoremWithHoles[
				environment, HoldComplete[name], parameters, type, theoremValue[environment, HoldComplete[proof], type, parameters],
				declarationAnnotation[Hold[options]]
			]
		]
	]
]

(* the statement and universe parameters come from the proof, which is evaluated in the environment the theorem goes
   into, as a proof given with its statement is (theoremValue) *)
addDeclaration[environment_, TypeTheoryTheorem[name_, proof_, options : OptionsPattern[]]] := Replace[Block[{$TypeTheoryEnvironment = environment}, proof], {
	state : TypeTheoryProof[_Association] :> Block[{$elaboratedHoles = {}},
		declareTheoremWithHoles[environment, HoldComplete[name], proofUniverseParameters[state], proofStatement[state], completedProofTerm[state], declarationAnnotation[Hold[options]]]
	],
	failure_Failure :> throwFailure[failure],
	other_ :> kernelFailure["ProofExpected", "`1` is not a TypeTheoryProof.", {Short[other]}]
}]

declareTheoremWithHoles[environment_, name_, universeParameters_, type_, value_, annotation_] := If[ $elaboratedHoles === {},
	declareTheorem[environment, name, universeParameters, type, value, annotation],
	declareWithHoles[
		environment, name, universeParameters, value, $elaboratedHoles,
		Function[{extended, closedValue}, declareTheorem[extended, name, universeParameters, type, closedValue, annotation]]
	]
]

addDeclaration[environment_, TypeTheoryInductiveType[name_, type_, constructors_List, options : OptionsPattern[]]] :=
	inductiveBlock[environment, {{HoldComplete[name], HoldComplete[type]}}, constructorSpecifications[constructors], Hold[options]]

(* mutually inductive types: their types, then the constructors of all of them *)
addDeclaration[environment_, TypeTheoryInductiveType[types : {(_Rule | _RuleDelayed) ..}, constructors_List, options : OptionsPattern[]]] :=
	inductiveBlock[environment, constructorSpecifications[types], constructorSpecifications[constructors], Hold[options]]

inductiveBlock[environment_, parsedTypes_List, parsedConstructors_List, heldOptions_Hold] := Module[
	{universeParameters, typeCores, provisional, constructorCores},
	universeParameters = declarationUniverseParameters[TypeTheoryInductiveType, heldOptions, Function[pair, toSyntax @@ Last[pair]] /@ Join[parsedTypes, parsedConstructors]];
	typeCores = Function[pair, First[pair] -> closedType[environment, Last[pair], universeParameters]] /@ parsedTypes;
	(* the constructor types may mention the types being declared *)
	provisional = addConstantRecords[environment, Association[Function[typeCore, First[typeCore] -> <|
		"Kind" -> "InductiveType",
		"Type" -> Last[typeCore],
		"UniverseParameters" -> universeParameters,
		"NumberOfParameters" -> 0,
		"NumberOfIndices" -> 0,
		"Constructors" -> {},
		"LargeElimination" -> False,
		"Recursive" -> False,
		"Block" -> Keys[typeCores]
	|>] /@ typeCores]];
	constructorCores = Function[pair, First[pair] -> closedType[provisional, Last[pair], universeParameters]] /@ parsedConstructors;
	declareInductiveTypes[
		environment,
		universeParameters,
		Replace[heldOptionValue[TypeTheoryInductiveType, heldOptions, "Parameters"], {
			HoldComplete[Automatic] :> sharedParameterCount[provisional, Values[typeCores], Values[constructorCores]],
			HoldComplete[n_Integer?NonNegative] :> n,
			HoldComplete[other_] :> kernelFailure["InvalidOption", "The value of the option \"Parameters\" must be a non-negative integer or Automatic, not `1`.", {HoldForm[other]}]
		}],
		typeCores,
		constructorCores
	]
]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_]] :=
	naturalNumbersRegistration[environment, HoldComplete[type], HoldComplete[zero], HoldComplete[successor], <||>]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_, operations_Association]] :=
	naturalNumbersRegistration[environment, HoldComplete[type], HoldComplete[zero], HoldComplete[successor], heldOperations[operations]]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_, addition_]] :=
	naturalNumbersRegistration[environment, HoldComplete[type], HoldComplete[zero], HoldComplete[successor], <|"Addition" -> HoldComplete[addition]|>]

(* the operations' names stay held, as every name in a declaration does *)
SetAttributes[heldOperations, HoldAllComplete]
heldOperations[Association[rules___]] := Association @ Cases[HoldComplete[rules], (Rule | RuleDelayed)[role_, name_] :> (role -> HoldComplete[name])]

(* an alias names its constant here too, as Naturals does NonNegativeIntegers *)
naturalNumbersRegistration[environment_, type_, zero_, successor_, operations_] := registerNaturalNumbers[
	environment,
	<|
		"Type" -> aliasResolvedName[environment, type],
		"Zero" -> aliasResolvedName[environment, zero],
		"Successor" -> aliasResolvedName[environment, successor],
		"Operations" -> Map[Function[name, aliasResolvedName[environment, name]], operations]
	|>
]

(* the two sides are elaborated as functions of the rule's variables, the right one against the type of the left *)
addDeclaration[environment_, TypeTheoryRewriteRule[name_, rule_, options : OptionsPattern[]]] := With[
	{
		universeParameters = declarationUniverseParameters[TypeTheoryRewriteRule, Hold[options], {toSyntax[rule]}],
		sides = rewriteRuleSides[HoldComplete[rule]]
	},
	If[ ! rulesSetting[environment, "RewriteRules"],
		kernelFailure["RewriteRulesNotAllowed", "The rules of the environment do not allow the rewrite rule `1`.", {HoldForm[name]}]
	];
	With[{left = elaborateClosedTerm[environment, sides["Left"], None, universeParameters]},
		declareRewriteRule[
			environment,
			HoldComplete[name],
			universeParameters,
			sides["NumberOfVariables"],
			First[left],
			First[elaborateClosedTerm[environment, sides["Right"], Last[left], universeParameters]]
		]
	]
]

addDeclaration[environment_, TypeTheoryQuotients[]] := addDeclaration[environment, TypeTheoryQuotients[Equal, {QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction}]]
addDeclaration[environment_, TypeTheoryQuotients[equality_, {type_, introduction_, lift_, induction_}]] :=
	declareQuotients[environment, HoldComplete[equality], HoldComplete /@ Unevaluated[{type, introduction, lift, induction}]]

addDeclaration[environment_, TypeTheoryCubical[sum_]] := declareCubical[environment, HoldComplete[sum]]

addDeclaration[_, other_] := kernelFailure["DeclarationExpected", "`1` is not a declaration.", {Short[other]}]

rewriteRuleSides[HoldComplete[ForAll[binders_, Rule[left_, right_]]]] :=
	<|"Left" -> HoldComplete[Function[binders, left]], "Right" -> HoldComplete[Function[binders, right]], "NumberOfVariables" -> Length[listElements[toSyntax[binders]]]|>
rewriteRuleSides[HoldComplete[Rule[left_, right_]]] := <|"Left" -> HoldComplete[left], "Right" -> HoldComplete[right], "NumberOfVariables" -> 0|>
rewriteRuleSides[HoldComplete[other_]] := kernelFailure["RewriteRuleSpecification", "`1` is not a rewrite rule: write ForAll[{Typed[x, type], ...}, lhs -> rhs].", {HoldForm[other]}]


(* A proof written as TypeTheoryProof[...] runs here, in the environment the theorem goes into: in a list of
   declarations, those before it are there and those after it are not. Its term is checked by the kernel as any
   theorem's value is. Any other proof is a term, which may also name a finished proof stored in a symbol. *)
theoremValue[environment_, HoldComplete[proof_TypeTheoryProof], _, _] := Replace[Block[{$TypeTheoryEnvironment = environment}, proof], {
	state : TypeTheoryProof[_Association] :> completedProofTerm[state],
	failure_Failure :> throwFailure[failure]
}]
theoremValue[environment_, held_HoldComplete, type_, universeParameters_List] := closedValue[environment, held, type, universeParameters]

(* A type or value given in full, every argument and universe level written out, as an import writes it,
   goes into the declaration without elaboration: the kernel checks the declaration all the same. *)
closedType[environment_, held_HoldComplete, universeParameters_List] :=
	Replace[explicitTerm[environment, held, universeParameters], None :> elaborateClosedType[environment, held, universeParameters]]

closedValue[environment_, held_HoldComplete, type_, universeParameters_List] :=
	Replace[explicitTerm[environment, held, universeParameters], None :> First[elaborateClosedTerm[environment, held, type, universeParameters]]]

(* {constructor -> type, ...}, held, as {{HoldComplete[constructor], HoldComplete[type]}, ...} *)
SetAttributes[constructorSpecifications, HoldFirst]
constructorSpecifications[constructors_] := With[
	{parsed = Cases[Unevaluated[constructors], (Rule | RuleDelayed)[constructor_, type_] :> {HoldComplete[constructor], HoldComplete[type]}]},
	If[ Length[parsed] =!= Length[Unevaluated[constructors]],
		kernelFailure["ConstructorSpecification", "Each constructor must be given as constructor -> type.", {}],
		parsed
	]
]


(* ::Subsection:: *)
(*Parameters*)


(* The largest n such that every type of the block takes the first type's first n binders first, and every
   constructor takes them first, with the same types, and passes them on unchanged to its result. *)
sharedParameterCount[environment_, typeCores_List, constructorTypes_List] := Module[{typeContext, typeIds, resultType},
	{typeContext, typeIds, resultType} = typeTelescope[environment, <||>, First[typeCores]];
	Min[
		Length[typeIds],
		Function[typeCore, First[matchLeadingBinders[environment, typeContext, typeIds, typeCore, 0]]] /@ Rest[typeCores],
		Function[constructorType, constructorParameterCount[environment, typeContext, typeIds, constructorType]] /@ constructorTypes
	]
]

constructorParameterCount[environment_, typeContext_, typeIds_List, constructorType_] := Module[{matched, remaining, conclusion},
	{matched, remaining} = matchLeadingBinders[environment, typeContext, typeIds, constructorType, 0];
	conclusion = Last @ typeTelescope[environment, typeContext, remaining];
	commonPrefixLength[Last @ applicationSpine[conclusion], freeVariable /@ Take[typeIds, matched]]
]

(* the types are elaborated and checked (closedType), but compared outside the block's check, so the type
   queries of the comparison check *)
matchLeadingBinders[_, _, {}, constructorType_, count_Integer] := {count, constructorType}
matchLeadingBinders[environment_, typeContext_, {id_, rest___}, constructorType_, count_Integer] := Replace[
	weakHeadNormalForm[environment, typeContext, constructorType],
	{
		dependentFunctionType[_, domain_, codomain_, _] /; definitionallyEqualQ[environment, typeContext, domain, typeContext[id]["Type"]] :>
			matchLeadingBinders[environment, typeContext, {rest}, instantiateBoundVariable[codomain, freeVariable[id]], count + 1],
		other_ :> {count, other}
	}
]

commonPrefixLength[first_List, second_List] := With[{length = Min[Length[first], Length[second]]},
	LengthWhile[Transpose[{Take[first, length], Take[second, length]}], Apply[SameQ]]
]


(* ::Subsection:: *)
(*Options and universe parameters*)


heldOptionValue[head_Symbol, Hold[options___], name_String] := First[Cases[
	Join[Hold[options], Hold @@ Options[head]],
	(Rule | RuleDelayed)[name, value_] :> HoldComplete[value],
	{1, 2}
]]

(* the syntax trees are worked out only when the universe parameters are not given: an import gives them,
   with terms too large to walk for nothing *)
SetAttributes[declarationUniverseParameters, HoldRest]
declarationUniverseParameters[head_Symbol, heldOptions_Hold, syntaxes_] := Replace[heldOptionValue[head, heldOptions, "UniverseParameters"], {
	HoldComplete[Automatic] :> universeParameterNames[syntaxes],
	HoldComplete[{parameters___}] /; AllTrue[Unevaluated[{parameters}], Function[parameter, MatchQ[Unevaluated[parameter], _Symbol | _String], HoldAll]] :>
		HoldComplete /@ Unevaluated[{parameters}],
	HoldComplete[other_] :> kernelFailure[
		"InvalidOption",
		"The value of the option \"UniverseParameters\" must be a list of symbols or strings, or Automatic, not `1`.",
		{HoldForm[other]}
	]
}]

universeParameterNames[syntaxes_List] := DeleteDuplicates @ Catenate[levelParameterNames /@ Join[
	Cases[syntaxes, syntaxApplication[syntaxSymbol[HoldComplete[TypeUniverse]], {level_}] :> level, {0, Infinity}],
	Catenate @ Cases[syntaxes, syntaxApplication[syntaxSymbol[HoldComplete[Subscript]], {_, levels__}] :> {levels}, {0, Infinity}]
]]

(* the symbols and strings of a level, leaving out the heads Plus, Max and ImpredicativeMaximum *)
levelParameterNames[syntaxSymbol[held_]] := {held}
levelParameterNames[syntaxString[name_]] := {HoldComplete[name]}
levelParameterNames[syntaxApplication[_, arguments_List]] := Catenate[levelParameterNames /@ arguments]
levelParameterNames[_] := {}


(* ::Subsection:: *)
(*Core declarations*)


(* A declaration's type is checked before its value, so every comparison in its check is of checked terms or
   their reducts, where definitional equality infers the types it asks without checking (withCheckedTerms). *)
declareAxiom[environment_, name_HoldComplete, universeParameters_List, type_, annotation_ : None, overloads_ : None, implementation_ : None] := withCheckedTerms[
	If[ ! $deferKernelChecks,
		checkUniverseParameters[name, universeParameters, {type}];
		sortLevel[environment, <||>, type]
	];
	addConstantRecords[environment, <|name -> Join[
		<|"Kind" -> "Axiom", "Type" -> type, "UniverseParameters" -> universeParameters|>,
		annotationField[annotation], overloadsField[overloads], implementationField[implementation]
	]|>]
]

(* An instance or a coercion is a definition the elaborator may apply; the kernel checks it as any other.
   An opaque definition is checked as any other too, but its record is of the kind "Opaque", which
   nothing unfolds: like an axiom it equals only itself, and unlike one its type has an element. A
   definition that unfolds has a height, which decides which of two definitions unfolds first when the
   kernel compares them (TypeChecking.wl), and a projection function is an abbreviation, which unfolds
   before the others. *)
declareDefinition[environment_, name_HoldComplete, universeParameters_List, type_, value_, roles_Association : <||>] := withCheckedTerms[
	If[ ! $deferKernelChecks,
		checkUniverseParameters[name, universeParameters, {type, value}];
		sortLevel[environment, <||>, type];
		checkHasType[environment, <||>, value, type];
		If[rulesSetting[environment, "Quantities"], checkLiveUses[environment, value]]
	];
	addConstantRecords[environment, <|name -> Join[
		<|"Kind" -> If[TrueQ[roles["Opaque"]], "Opaque", "Definition"], "Type" -> type, "UniverseParameters" -> universeParameters, "Value" -> value|>,
		If[TrueQ[roles["Opaque"]], <||>, <|"Height" -> definitionHeight[environment, value]|>],
		If[! TrueQ[roles["Opaque"]] && projectionFunctionQ[value], <|"Hint" -> "Abbreviation"|>, <||>],
		Select[KeyTake[roles, {"Instance", "Coercion"}], TrueQ],
		KeyTake[roles, {"Overloads"}]
	]|>]
]

(* a definition's height: one more than the greatest height of the definitions its value
   mentions, so a definition is higher than each definition it is defined by *)
definitionHeight[environment_, value_] := 1 + Max[0, Function[constant, Lookup[constantRecord[environment, constant], "Height", 0]] /@
	DeleteDuplicates[Cases[value, constantReference[name_, _] :> name, {0, Infinity}]]
]

(* a theorem is a proposition, or under rules without Prop a type, and its proof is never unfolded *)
declareTheorem[environment_, name_HoldComplete, universeParameters_List, type_, value_, annotation_ : None] := withCheckedTerms[
	If[ ! $deferKernelChecks,
		checkUniverseParameters[name, universeParameters, {type, value}];
		If[ ! levelEquivalentQ[sortLevel[environment, <||>, type], 0] && rulesSetting[environment, "Prop"],
			kernelFailure["PropositionExpected", "The statement of the theorem `1` must be a proposition.", {HoldForm @@ name}]
		];
		checkHasType[environment, <||>, value, type];
		If[rulesSetting[environment, "Quantities"], checkLiveUses[environment, value]]
	];
	addConstantRecords[environment, <|name -> Join[<|"Kind" -> "Theorem", "Type" -> type, "UniverseParameters" -> universeParameters, "Value" -> value|>, annotationField[annotation]]|>]
]

(* The left side is an axiom applied to a pattern: each argument is a variable of the rule, a term
   without variables, or a constant applied to such arguments. Every variable occurs in it, and every
   universe parameter is a level of the axiom, so a match determines the right side. *)
declareRewriteRule[environment_, name_HoldComplete, universeParameters_List, numberOfVariables_Integer, left_, right_] := Module[
	{body, head, headLevels},
	checkUniverseParameters[name, universeParameters, {left, right}];
	checkHasType[environment, <||>, right, inferType[environment, <||>, left]];
	body = functionBody[left, numberOfVariables];
	{head, headLevels} = Replace[First @ applicationSpine[body], {
		constantReference[axiom_, levels_List] /; constantRecord[environment, axiom]["Kind"] === "Axiom" :> {axiom, levels},
		_ :> kernelFailure["RewriteRuleHead", "The left side of the rewrite rule `1` must be an axiom applied to arguments.", {HoldForm @@ name}]
	}];
	If[ ! AllTrue[Last @ applicationSpine[body], Function[argument, patternQ[argument, numberOfVariables]]],
		kernelFailure["RewriteRulePattern", "The left side of the rewrite rule `1` is not a pattern: a variable occurs inside a function or under a head that is not a constant.", {HoldForm @@ name}]
	];
	If[ ! AllTrue[Range[0, numberOfVariables - 1], Function[index, boundVariableOccursQ[body, index]]],
		kernelFailure["RewriteRuleVariable", "Every variable of the rewrite rule `1` must occur in its left side.", {HoldForm @@ name}]
	];
	If[ ! SubsetQ[Cases[headLevels, levelParameter[parameter_] :> parameter], universeParameters],
		kernelFailure["RewriteRuleUniverse", "Every universe parameter of the rewrite rule `1` must be a universe level of its head.", {HoldForm @@ name}]
	];
	If[rulesSetting[environment, "Quantities"], checkRewriteRuleUses[environment, name, numberOfVariables, left, right]];
	addRewriteRuleRecord[environment, name, <|
		"Kind" -> "RewriteRule",
		"Type" -> None,
		"UniverseParameters" -> universeParameters,
		"Head" -> head,
		"NumberOfVariables" -> numberOfVariables,
		"LeftHandSide" -> left,
		"RightHandSide" -> right
	|>]
]

functionBody[term_, 0] := term
functionBody[lambdaAbstraction[_, _, body_, _], n_Integer?Positive] := functionBody[body, n - 1]
functionBody[_, _] := kernelFailure["RewriteRuleSpecification", "The sides of a rewrite rule must be functions of its variables.", {}]

patternQ[boundVariable[index_], numberOfVariables_] := index < numberOfVariables
patternQ[term_, numberOfVariables_] /; NoneTrue[Range[0, numberOfVariables - 1], Function[index, boundVariableOccursQ[term, index]]] := True
patternQ[term_, numberOfVariables_] := With[{spine = applicationSpine[term]},
	MatchQ[First[spine], _constantReference] && Last[spine] =!= {} && AllTrue[Last[spine], Function[argument, patternQ[argument, numberOfVariables]]]
]
