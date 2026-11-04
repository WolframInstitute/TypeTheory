(* ::Package:: *)

(*
WolframDefinitions: reading the definitions of a Wolfram Language symbol, the first step of typing them.

The definitions are lowered by the compiler of the WolframKernel project, which the paclet Wolfram/KernelCompiler
publishes: its ToCore turns a symbol's definitions into a Core`Program, each definition a match program of the Match
IR for its left side and Core for its right side. TypeTheory loads that paclet only when definitions are read, as
LeanLink loads TypeTheory, and gives a Failure naming how to install it where it is missing. The Core`/Match` forms
are versioned by $CoreVersion, which must be the version this file is written for; they are read by their names, in
whichever context the paclet puts them, as coreForm["Call"][...].

TypeTheoryFormalize makes a symbol a constant, at the best of two tiers:

	a definition       its single definition translates: arguments bound by plain or head-typed patterns, a body of
	                   arithmetic, calls of built-ins with a signature here and of other symbols, formalized first;
	                   elaboration types it, or checks it against the type the option "Type" gives
	an axiom           otherwise, of the type "Type" gives, or of the type Expressions -> ... -> Expressions its
	                   arguments take, with "Implementation" -> symbol: Wolfram computes it, the kernel never does

A built-in that a body calls gets its signature from $wolframSignatures, declared only where it is used and not
declared already: precise where the built-in allows, as Simplify : A -> A, and over Expressions, the type of any
Wolfram Language expression, otherwise. No equation about a built-in is assumed, so nothing more is trusted.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryFormalize]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[lowerDefinitions]
PackageScoped[loadKernelCompiler]
PackageScoped[kernelCompilerSymbol]
PackageScoped[coreNormal]
PackageScoped[coreForm]
PackageScoped[definitionStatements]
PackageScoped[fullName]
PackageScoped[missingDeclarations]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryFormalize::usage = "TypeTheoryFormalize[symbol] gives the declarations that make the Wolfram Language function symbol a constant of the default environment: a definition read off its definitions where they translate, typed by elaboration, and otherwise an axiom that symbol computes. TypeTheoryFormalize[symbol, environment] makes them for environment. The option \"Type\" -> type gives the type the constant must have. With \"Meaning\" -> \"Rules\", it gives instead the rules of symbol, a definition of type Expressions -> Option[Expressions] in TypeTheoryEnvironment[\"WolframLanguage\"]: the expression each expression rewrites to by the first rule that matches it."
lowerDefinitions::usage = "lowerDefinitions[HoldComplete[symbol]] gives the Core`Program of the definitions of symbol, by the compiler's ToCore, or a Failure."
kernelCompilerSymbol::usage = "kernelCompilerSymbol[name] gives the symbol of the compiler named name, in the context the paclet Wolfram/KernelCompiler puts it, or None."
coreNormal::usage = "coreNormal[program] gives program with each form of Core and Match as coreForm[name]."
coreForm::usage = "coreForm[name] is the form of Core or Match named name, as coreNormal writes it."
definitionStatements::usage = "definitionStatements[symbol] gives the DownValues of symbol as held statements HoldComplete[lhs := rhs], in the order the Wolfram Language tries them."
fullName::usage = "fullName[symbol] gives the full name of symbol, its context and its name, without evaluating it."
missingDeclarations::usage = "missingDeclarations[environment, declarations] gives the declarations whose constants environment does not declare yet."
loadKernelCompiler::usage = "loadKernelCompiler[] loads the paclet Wolfram/KernelCompiler and gives True, or gives a Failure where it is missing or writes Core of another version."


(* ::Section:: *)
(*Function Definitions*)


$kernelCompilerResource = "https://www.wolframcloud.com/obj/nikm/DeployedResources/Paclet/Wolfram/KernelCompiler"

(* the version of the compiler's Core`/Match` forms that reading definitions is written for, and the paclet's versions
   that write it *)
$kernelCompilerCoreVersion = 1
$kernelCompilerVersions = "0.1."

$kernelCompilerLoaded = False

(* the contexts the paclet has put the compiler in, the published one first *)
kernelCompilerSymbol[name_String] := Replace[SelectFirst[{"Wolfram`KernelCompiler`", "Compiler`"}, Function[context, NameQ[context <> name]]], {
	context_String :> Symbol[context <> name],
	_ :> None
}]

(* loaded once; a paclet installed after a failure is found the next time *)
loadKernelCompiler[] := Which[
	$kernelCompilerLoaded,
		True,
	! AnyTrue[PacletFind["Wolfram/KernelCompiler"], Function[paclet, StringStartsQ[paclet["Version"], $kernelCompilerVersions]]],
		Failure["KernelCompilerMissing", <|
			"MessageTemplate" -> "Reading Wolfram Language definitions needs the paclet Wolfram/KernelCompiler `1`*. Install it with `2`.",
			"MessageParameters" -> {$kernelCompilerVersions, "PacletInstall[ResourceObject[\"" <> $kernelCompilerResource <> "\"]]"}
		|>],
	True,
		(* off the context path, which it would join: the paclet's names, its own TypeTheoryCheck among them, must not
		   shadow TypeTheory's; its functions are called by their full names *)
		Block[{$ContextPath = $ContextPath}, Needs["Wolfram`KernelCompiler`"]];
		If[ kernelCompilerSymbol["$CoreVersion"] === $kernelCompilerCoreVersion,
			$kernelCompilerLoaded = True,
			Failure["KernelCompilerVersion", <|
				"MessageTemplate" -> "The paclet Wolfram/KernelCompiler writes Core of version `1`, and reading definitions is written for version `2`.",
				"MessageParameters" -> {kernelCompilerSymbol["$CoreVersion"], $kernelCompilerCoreVersion}
			|>]
		]
]

(* the definitions as held statements, lhs := rhs, which is what ToCore takes; nothing of them evaluates *)
SetAttributes[definitionStatements, HoldAllComplete]
definitionStatements[symbol_Symbol] := Cases[DownValues[symbol], RuleDelayed[HoldPattern[lhs_], rhs_] :> HoldComplete[SetDelayed[lhs, rhs]]]

lowerDefinitions[HoldComplete[symbol_Symbol]] := Replace[loadKernelCompiler[], {
	True :> coreNormal[kernelCompilerSymbol["ToCore"][definitionStatements[symbol]]],
	failure_Failure :> failure
}]

(* the Core and Match forms by their names, coreForm["Call"], coreForm["Bind"], ..., whichever context they are in *)
coreNormal[program_] := ReplaceAll[program, form_Symbol /; coreContextQ[form] :> coreForm[SymbolName[Unevaluated[form]]]]

SetAttributes[coreContextQ, HoldAllComplete]
coreContextQ[form_Symbol] := MemberQ[{"Core`", "Match`", "Wolfram`KernelCompiler`Core`", "Wolfram`KernelCompiler`Match`"}, Context[Unevaluated[form]]]


(* ::Subsection:: *)
(*Formalizing a symbol*)


SetAttributes[TypeTheoryFormalize, HoldAll]

TypeTheoryFormalize[symbol_Symbol, options : OptionsPattern[]] := catchKernelFailure[formalizeMeaning[defaultEnvironment[], HoldComplete[symbol], Hold[options]]]
TypeTheoryFormalize[symbol_Symbol, environment_, options : OptionsPattern[]] /; environmentQ[environment] :=
	catchKernelFailure[formalizeMeaning[environment, HoldComplete[symbol], Hold[options]]]

(* the option "Meaning": "Function", the default, a constant that is the function symbol computes, or "Rules", its rules
   as a rewriting of expressions *)
formalizeMeaning[environment_, held_, options_Hold] := Replace[Cases[options, HoldPattern["Meaning" -> meaning_] :> meaning, {1}], {
	{} | {"Function", ___} :> formalize[environment, held, formalizeType[options]],
	{"Rules", ___} :> rulesDeclarations[environment, held],
	{other_, ___} :> kernelFailure["InvalidOption", "The value of the option \"Meaning\" must be \"Function\" or \"Rules\", not `1`.", {other}]
}]

(* the type the option "Type" gives, held, or None *)
formalizeType[Hold[options___]] := Replace[Cases[Hold[options], HoldPattern["Type" -> type_] :> HoldComplete[type], {1}], {{} -> None, {type_, ___} :> type}]

(* the symbols formalized now, so that two that call each other end as axioms, not in a loop *)
$formalizing = {}

formalize[environment_, held_HoldComplete, type_] := Block[{$formalizing = Append[$formalizing, held]},
	Replace[lowerDefinitions[held], {
		_Failure /; type =!= None :> {implementedAxiom[held, type]},
		failure_Failure :> failure,
		program_ :> formalizeProgram[environment, held, type, Cases[Lookup[First[program], fullName @@ held, {}], coreForm["Definition"][___]]]
	}]
]

SetAttributes[fullName, HoldAllComplete]
fullName[symbol_Symbol] := Context[Unevaluated[symbol]] <> SymbolName[Unevaluated[symbol]]

formalizeProgram[environment_, held_, type_, definitions_List] := Replace[translatedDefinitions[held, definitions], {
	{value_HoldComplete, calls_List} :> candidateDeclarations[environment, held, type, definitions, calls, Function[extended, DeleteDuplicates[{value, withoutHeadTypes[value]}]]],
	{"NaturalRecursion", parts_Association, calls_List} :>
		candidateDeclarations[environment, held, type, definitions, calls, Function[extended, naturalRecursionCandidates[extended, type, parts]]],
	{"ListRecursion", parts_Association, calls_List} :>
		candidateDeclarations[environment, held, type, definitions, calls, Function[extended, listRecursionCandidates[extended, type, parts]]],
	_ :> fallbackDeclarations[environment, held, type, definitions]
}]

(* the declarations the calls need, then the definition of the first candidate value that checks; the fallback where
   none does *)
candidateDeclarations[environment_, held_, type_, definitions_, calls_, candidatesOf_] := Replace[calledDeclarations[environment, held, calls], {
	declarations_List :> With[{extended = TypeTheoryEnvironment[environment, declarations]},
		Replace[
			SelectFirst[candidatesOf[extended], Function[value, ! FailureQ[Quiet[TypeTheoryEnvironment[extended, {definitionOf[held, value, type]}]]]], None],
			{None :> fallbackDeclarations[environment, held, type, definitions], value_ :> Append[declarations, definitionOf[held, value, type]]}
		]
	],
	_ :> fallbackDeclarations[environment, held, type, definitions]
}]

(* the value with its arguments untyped, for a type given that the heads of its patterns, as _Integer, would contradict,
   such as NonNegativeIntegers -> NonNegativeIntegers *)
withoutHeadTypes[HoldComplete[Function[{binders___}, body_]]] := HoldComplete[Function[{binders}, body]] /. HoldPattern[Typed[symbol_Symbol, Integers | Rationals]] :> symbol
withoutHeadTypes[value_] := value

definitionOf[HoldComplete[symbol_], HoldComplete[value_], None] := TypeTheoryDefinition[symbol, value]
definitionOf[HoldComplete[symbol_], HoldComplete[value_], HoldComplete[type_]] := TypeTheoryDefinition[symbol, Typed[value, type]]

(* the axiom that the symbol computes, of the type given, or of the type Expressions -> ... -> Expressions its
   arguments take *)
fallbackDeclarations[environment_, held_, None, definitions_] := Replace[definitionArities[definitions], {
	{arity_Integer} :> Append[missingDeclarations[environment, expressionsDeclarations[environment]], implementedAxiom[held, expressionsType[arity]]],
	_ :> kernelFailure["Unformalizable", "The definitions of `1` do not take one number of arguments: give its type with \"Type\".", {HoldForm @@ held}]
}]
fallbackDeclarations[_, held_, type_HoldComplete, _] := {implementedAxiom[held, type]}

implementedAxiom[HoldComplete[symbol_], HoldComplete[type_]] := TypeTheoryAxiom[symbol, type, "Implementation" -> symbol]

definitionArities[definitions_] := Union[Cases[definitions, coreForm["Definition"][_, coreForm["Program"][{___, coreForm["Length"][{}, arity_Integer], ___}], ___] :> arity]]

expressionsType[arity_Integer] := HoldComplete @@ {Fold[Function[{codomain, domain}, domain -> codomain], Expressions, ConstantArray[Expressions, arity]]}

(* the declarations of a list that the environment does not declare yet *)
missingDeclarations[environment_, declarations_List] := Select[declarations, Function[declaration, ! constantDeclaredQ[environment, declarationName[declaration]]]]

SetAttributes[declarationName, HoldAllComplete]
declarationName[(TypeTheoryAxiom | TypeTheoryDefinition)[name_, ___]] := HoldComplete[name]

(* the declarations the calls of a body need: the signatures of the built-ins not declared yet, and the formalization of
   the other symbols first; None where a call has neither *)
calledDeclarations[environment_, held_, calls_List] := Catch[
	Fold[
		Function[{declarations, call}, Join[declarations, calledDeclaration[TypeTheoryEnvironment[environment, declarations], held, call]]],
		{},
		DeleteDuplicates[calls]
	],
	untranslatable,
	Function[{value, tag}, None]
]

calledDeclaration[environment_, held_, call_HoldComplete] := Which[
	constantDeclaredQ[environment, call],
		{},
	call === held || MemberQ[$formalizing, call],
		Throw[None, untranslatable],
	KeyExistsQ[$wolframSignatures, call],
		missingDeclarations[environment, Append[If[FreeQ[$wolframSignatures[call], Expressions], {}, expressionsDeclarations[environment]], $wolframSignatures[call]]],
	systemSymbolQ @@ call,
		Throw[None, untranslatable],
	True,
		Replace[formalize[environment, call, None], {declarations_List :> declarations, _ :> Throw[None, untranslatable]}]
]

SetAttributes[systemSymbolQ, HoldAllComplete]
systemSymbolQ[symbol_Symbol] := Context[Unevaluated[symbol]] === "System`"


(* ::Subsection:: *)
(*Translating definitions*)


(* {HoldComplete[value], {HoldComplete[called], ...}} for a symbol's definitions, or None: one definition whose
   arguments are bound by plain or head-typed patterns, and whose body has a counterpart *)
translatedDefinitions[_, {coreForm["Definition"][_, coreForm["Program"][instructions_List], body_, ___]}] := Catch[
	With[{binders = definitionBinders[instructions]},
		Replace[Reap[translatedCore[body, Association[Function[binder, binder["Local"] -> binder["Symbol"]] /@ binders]], untranslatedCall], {
			{HoldComplete[term_], calls_} :> {
				Replace[Join @@ (binderSyntax /@ binders), HoldComplete[parameters___] :> HoldComplete[Function[{parameters}, term]]],
				Catenate[calls]
			}
		}]
	],
	untranslatable,
	Function[{value, tag}, None]
]
(* two definitions by structural recursion on a list, f[{}] and f[{x_, rest___}], whose body calls f only on {rest}:
   {"ListRecursion", <|"Empty" -> HoldComplete[value], "Prepend" -> HoldComplete[value], "Head" -> HoldComplete[x],
   "Rest" -> HoldComplete[rest]|>, calls}, the prepend case's value naming the recursion's result recursionResult *)
translatedDefinitions[held_, definitions : {_, __}] := Replace[
	listRecursionTranslation[held, definitions],
	None :> Replace[naturalRecursionTranslation[held, definitions], None :> guardChainTranslation[definitions]]
]

(* two definitions by recursion on a natural number, f[..., 0, ...] and f[..., n_, ...], the second calling f only on n - 1
   with its other arguments as they are, perhaps with n an _Integer and the condition n > 0, n >= 1 or n != 0, which
   n + 1 meets: {"NaturalRecursion", <|"Zero" -> HoldComplete[value], "Successor" -> HoldComplete[value], "Binders" ->
   {binder, ...}, "Position" -> p|>, calls}, the successor case's value of predecessor, n being predecessor + 1, and of
   recursionResult, the value at predecessor; the other arguments are the binders, by their names in the second *)
naturalRecursionTranslation[_, Except[{_, _}]] := None
naturalRecursionTranslation[held_, definitions : {_, _}] := Catch[
	Replace[SortBy[definitions, Function[definition, zeroPosition[definition] === None]], {
		{zero_, successor_} /; IntegerQ[zeroPosition[zero]] && zeroPosition[successor] === None :> With[
			{
				position = zeroPosition[zero],
				zeroParts = clauseParts[DeleteCases[zero[[2, 1]], coreForm["Same"][_, _]]],
				successorParts = clauseParts[DeleteCases[successor[[2, 1]], coreForm["Guard"][_]]],
				guards = Cases[successor[[2, 1]], coreForm["Guard"][test_] :> test]
			},
			With[{arity = successorParts["Arity"], local = Lookup[successorParts["Locals"], position, Throw[None, untranslatable]]},
				If[ zeroParts["Arity"] =!= arity || Keys[successorParts["Locals"]] =!= Range[arity] || Keys[zeroParts["Locals"]] =!= DeleteCases[Range[arity], position] ||
						! MemberQ[{None, "System`Integer"}, Lookup[successorParts["Heads"], position, None]] ||
						! AllTrue[guards, MatchQ[coreForm["Call"]["System`Greater" | "System`Unequal", {coreForm["Local"][local], coreForm["Constant"][0]}] |
							coreForm["Call"]["System`GreaterEqual", {coreForm["Local"][local], coreForm["Constant"][1]}]]],
					Throw[None, untranslatable]
				];
				With[
					{
						binders = Function[q, If[ q === position,
							<|"Symbol" -> HoldComplete[naturalArgument], "Type" -> HoldComplete[NonNegativeIntegers]|>,
							<|"Symbol" -> ToExpression[successorParts["Sources"][q], InputForm, HoldComplete], "Type" -> headType[Lookup[successorParts["Heads"], q, None]]|>
						]] /@ Range[arity],
						others = DeleteCases[Range[arity], position]
					},
					Replace[
						{
							Reap[translatedCore[zero[[3]], Association[Function[q, zeroParts["Locals"][q] -> binders[[q, "Symbol"]]] /@ others]], untranslatedCall],
							Block[{$naturalRecursion = <|"Self" -> fullName @@ held, "Local" -> local, "Position" -> position, "Others" -> Association[Function[q, q -> successorParts["Locals"][q]] /@ others]|>},
								Reap[translatedCore[successor[[3]], Association[Function[q, successorParts["Locals"][q] -> binders[[q, "Symbol"]]] /@ others]], untranslatedCall]
							]
						},
						{{zeroValue_HoldComplete, zeroCalls_}, {successorValue_HoldComplete, successorCalls_}} :> {
							"NaturalRecursion",
							<|"Zero" -> zeroValue, "Successor" -> successorValue, "Binders" -> binders, "Position" -> position|>,
							Join[Catenate[zeroCalls], Catenate[successorCalls]]
						}
					]
				]
			]
		],
		_ :> None
	}],
	untranslatable,
	Function[{value, tag}, None]
]

(* the position whose argument a definition's pattern gives as 0, or None *)
zeroPosition[coreForm["Definition"][_, coreForm["Program"][instructions_List], ___]] := Replace[
	Cases[instructions, coreForm["Same"][{position_Integer}, HoldComplete[0]] :> position],
	{{position_} :> position, _ -> None}
]
zeroPosition[_] := None

$naturalRecursion = <||>

(* the candidate values of a definition by recursion on a natural number, of the type "Type" gives, its argument at the
   recursion's position NonNegativeIntegers, or of the type of its zero case, where that has no other argument *)
naturalRecursionCandidates[_, type_HoldComplete, parts_] := Replace[curriedParts[type, Length[parts["Binders"]]], {
	{domains_List, resultType_HoldComplete} /; domains[[parts["Position"]]] === HoldComplete[NonNegativeIntegers] :> {naturalRecursionValue[parts, resultType]},
	_ :> {}
}]
naturalRecursionCandidates[environment_, None, parts_] := Replace[With[{zero = TypeTheoryTerm @@ Append[parts["Zero"], environment]}, Quiet[TypeOf[zero]]], {
	TypeTheoryTerm[resultType_, ___] :> {naturalRecursionValue[parts, HoldComplete[resultType]]},
	_ :> {}
}]

(* the domains and the result of a type of arity arguments, A1 -> ... -> An -> B, each held; None where it has fewer *)
curriedParts[type_HoldComplete, 0] := {{}, type}
curriedParts[HoldComplete[domain_ -> codomain_], arity_Integer] := Replace[curriedParts[HoldComplete[codomain], arity - 1], {
	{domains_List, result_} :> {Prepend[domains, HoldComplete[domain]], result},
	_ -> None
}]
curriedParts[_, _] := None

naturalRecursionValue[parts_, resultTypeHeld_HoldComplete] := Replace[
	{parts["Zero"], parts["Successor"], resultTypeHeld, Join @@ (binderSyntax /@ parts["Binders"])},
	{HoldComplete[zero_], HoldComplete[successor_], HoldComplete[b_], HoldComplete[binders___]} :> HoldComplete[
		Function[{binders},
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[number, NonNegativeIntegers]}, b],
				zero,
				Function[{Typed[predecessor, NonNegativeIntegers], Typed[recursionResult, b]}, successor],
				naturalArgument
			]
		]
	]
]

listRecursionTranslation[_, Except[{_, _}]] := None
listRecursionTranslation[held_, definitions : {_, _}] := Catch[
	Replace[SortBy[definitions, Function[definition, ! emptyListDefinitionQ[definition]]], {
		{empty_?emptyListDefinitionQ, prepend : coreForm["Definition"][_, coreForm["Program"][instructions_List], body_, ___]} :> With[
			{
				head = FirstCase[instructions, coreForm["Bind"][source_String, local_String, {1, 1}] :> {source, local}, Throw[None, untranslatable]],
				rest = FirstCase[instructions, coreForm["BindSequence"][source_String, local_String, {1}, 2, 0] :> {source, local}, Throw[None, untranslatable]]
			},
			If[ Sort[instructions[[All, 0]]] =!= Sort[coreForm /@ {"Length", "MinLength", "HeadIs", "Bind", "BindSequence"}] ||
					! MemberQ[instructions, coreForm["HeadIs"][{1}, "System`List"]],
				Throw[None, untranslatable]
			];
			Replace[
				{
					Reap[translatedCore[empty[[3]], <||>], untranslatedCall],
					Block[{$recursion = <|"Self" -> fullName @@ held, "Rest" -> Last[rest], "RestSymbol" -> ToExpression[First[rest], InputForm, HoldComplete]|>},
						Reap[translatedCore[body, <|Last[head] -> ToExpression[First[head], InputForm, HoldComplete]|>], untranslatedCall]
					]
				},
				{{emptyValue_HoldComplete, emptyCalls_}, {prependValue_HoldComplete, prependCalls_}} :> {
					"ListRecursion",
					<|"Empty" -> emptyValue, "Prepend" -> prependValue, "Head" -> ToExpression[First[head], InputForm, HoldComplete], "Rest" -> ToExpression[First[rest], InputForm, HoldComplete]|>,
					Join[Catenate[emptyCalls], Catenate[prependCalls]]
				}
			]
		],
		_ :> None
	}],
	untranslatable,
	Function[{value, tag}, None]
]
translatedDefinitions[_, _] := None

(* definitions whose arguments are bound alike, each but the last with a condition: If[condition, value, ...], the
   last value where no condition holds; the arguments are the last definition's, each definition's own names for them
   taken as theirs *)
guardChainTranslation[definitions_List] := Catch[
	With[{clauses = clauseParts /@ definitions[[All, 2, 1]]},
		If[ ! AllTrue[Most[clauses], Function[clause, clause["Guard"] =!= None]] || Last[clauses]["Guard"] =!= None || Length[Union[clauses[[All, "Arity"]]]] != 1,
			Throw[None, untranslatable]
		];
		With[{binders = chainBinders[clauses]},
			Replace[
				Reap[
					Fold[
						Function[{rest, clauseValue}, With[{locals = Association[Thread[Values[clauseValue[[1]]["Locals"]] -> binders[[All, "Symbol"]]]]},
							Replace[{translatedCore[clauseValue[[1]]["Guard"], locals], translatedCore[clauseValue[[2]], locals], rest},
								{HoldComplete[condition_], HoldComplete[value_], HoldComplete[otherwise_]} :> HoldComplete[If[condition, value, otherwise]]
							]
						]],
						translatedCore[definitions[[-1, 3]], Association[Thread[Values[Last[clauses]["Locals"]] -> binders[[All, "Symbol"]]]]],
						Reverse[Transpose[{Most[clauses], definitions[[;; -2, 3]]}]]
					],
					untranslatedCall
				],
				{HoldComplete[term_], calls_} :> {
					Replace[Join @@ (binderSyntax /@ binders), HoldComplete[parameters___] :> HoldComplete[Function[{parameters}, term]]],
					Append[Catenate[calls], HoldComplete[If]]
				}
			]
		]
	],
	untranslatable,
	Function[{value, tag}, None]
]

(* the parts of a definition's match program: its arity, the local of each argument by position, the head each is
   typed by, and its condition or None; anything else does not translate *)
clauseParts[instructions_List] := With[
	{
		arity = FirstCase[instructions, coreForm["Length"][{}, n_Integer] :> n, Throw[None, untranslatable]],
		guards = Cases[instructions, coreForm["Guard"][test_] :> test]
	},
	If[ ! AllTrue[instructions, MatchQ[coreForm["Length"][{}, _] | coreForm["Bind"][_, _, {_Integer}] | coreForm["HeadIs"][{_Integer}, _String] | coreForm["Guard"][_]]] ||
			Length[guards] > 1,
		Throw[None, untranslatable]
	];
	<|
		"Arity" -> arity,
		"Locals" -> KeySort[Association[Cases[instructions, coreForm["Bind"][source_String, local_String, {position_Integer}] :> position -> local]]],
		"Sources" -> Association[Cases[instructions, coreForm["Bind"][source_String, _, {position_Integer}] :> position -> source]],
		"Heads" -> Association[Cases[instructions, coreForm["HeadIs"][{position_Integer}, head_String] :> position -> head]],
		"Guard" -> First[guards, None]
	|>
]

(* the binders of a chain: the last definition's names, each argument typed by the head every definition gives it,
   where they agree *)
chainBinders[clauses_List] := With[{last = Last[clauses]},
	If[ Keys[last["Locals"]] =!= Range[last["Arity"]] || ! AllTrue[clauses, Function[clause, Keys[clause["Locals"]] === Range[last["Arity"]]]], Throw[None, untranslatable]];
	Function[position, With[{heads = Union[Lookup[clauses[[All, "Heads"]], position, None]]},
		<|"Symbol" -> ToExpression[last["Sources"][position], InputForm, HoldComplete], "Type" -> headType[If[Length[heads] == 1, First[heads], Throw[None, untranslatable]]]|>
	]] /@ Range[last["Arity"]]
]

emptyListDefinitionQ[coreForm["Definition"][_, coreForm["Program"][{coreForm["Length"][{}, 1], coreForm["Same"][{1}, HoldComplete[{}]]}], ___]] := True
emptyListDefinitionQ[_] := False

(* the recursion a prepend case is translated under: the symbol itself, and the rest of the list, bound as a sequence *)
$recursion = <||>

(* the candidate values of a definition by recursion on a list: its types from "Type" where given, {a} -> b, and
   otherwise of the type the empty case has, its elements of any type first and of that type then *)
listRecursionCandidates[environment_, HoldComplete[{elementType_} -> resultType_], parts_] :=
	{listRecursionValue[parts, HoldComplete[], HoldComplete[elementType], HoldComplete[resultType]]}
listRecursionCandidates[_, HoldComplete[_], _] := {}
(* the term is made first, as TypeOf holds its argument *)
listRecursionCandidates[environment_, None, parts_] := Replace[With[{empty = TypeTheoryTerm @@ Append[parts["Empty"], environment]}, Quiet[TypeOf[empty]]], {
	TypeTheoryTerm[resultType_, ___] :> {
		listRecursionValue[parts, HoldComplete[TypedImplicit[elementType, TypeUniverse[u + 1]]], HoldComplete[elementType], HoldComplete[resultType]],
		listRecursionValue[parts, HoldComplete[], HoldComplete[resultType], HoldComplete[resultType]]
	},
	_ :> {}
}]

listRecursionValue[parts_, elementBinders_HoldComplete, elementTypeHeld_HoldComplete, resultTypeHeld_HoldComplete] := Replace[
	{parts["Empty"], parts["Prepend"], parts["Head"], parts["Rest"], elementBinders, elementTypeHeld, resultTypeHeld},
	{HoldComplete[empty_], HoldComplete[prepend_], HoldComplete[head_], HoldComplete[rest_], HoldComplete[binders___], HoldComplete[a_], HoldComplete[b_]} :> HoldComplete[
		Function[{binders, Typed[listArgument, {a}]},
			InductiveRecursor[List][
				Function[{Typed[list, {a}]}, b],
				empty,
				Function[{Typed[rest, {a}], Typed[head, a], Typed[recursionResult, b]}, prepend],
				listArgument
			]
		]
	]
]

(* each argument bound once, at its own position, its type a head the patterns give *)
definitionBinders[instructions_List] := With[
	{
		arity = FirstCase[instructions, coreForm["Length"][{}, n_Integer] :> n, Throw[None, untranslatable]],
		binds = Association[Cases[instructions, coreForm["Bind"][source_String, local_String, {position_Integer}] :> position -> <|"Source" -> source, "Local" -> local|>]],
		heads = Association[Cases[instructions, coreForm["HeadIs"][{position_Integer}, head_String] :> position -> head]]
	},
	If[ ! AllTrue[instructions, MatchQ[coreForm["Length"][{}, _] | coreForm["Bind"][_, _, {_Integer}] | coreForm["HeadIs"][{_Integer}, _String]]] ||
			Sort[Keys[binds]] =!= Range[arity],
		Throw[None, untranslatable]
	];
	Function[position, Join[binds[position], <|"Symbol" -> ToExpression[binds[position]["Source"], InputForm, HoldComplete], "Type" -> headType[Lookup[heads, position, None]]|>]] /@ Range[arity]
]

headType[None] := None
headType["System`Integer"] := HoldComplete[Integers]
headType["System`Rational"] := HoldComplete[Rationals]
headType[_] := Throw[None, untranslatable]

binderSyntax[binder_] := Replace[{binder["Symbol"], binder["Type"]}, {
	{HoldComplete[symbol_], None} :> HoldComplete[symbol],
	{HoldComplete[symbol_], HoldComplete[type_]} :> HoldComplete[Typed[symbol, type]]
}]

(* the heads a body may call that TypeTheory reads itself: its arithmetic, overloaded, and list literals *)
$surfaceHeads = {"System`Plus", "System`Times", "System`Power", "System`Subtract", "System`Minus", "System`Equal", "System`Unequal", "System`Less",
	"System`LessEqual", "System`Greater", "System`GreaterEqual", "System`And", "System`Or", "System`Not", "System`List"}

(* under a recursion on a list, f[{rest}] is the recursion's result and {rest} the rest of the list; rest alone is a
   sequence, which has no counterpart *)
translatedCore[coreForm["Call"][self_String, {coreForm["Call"]["System`List", {coreForm["Local"][rest_String]}]}], _] /; self === $recursion["Self"] && rest === $recursion["Rest"] :=
	HoldComplete[recursionResult]
translatedCore[coreForm["Call"]["System`List", {coreForm["Local"][rest_String]}], _] /; rest === $recursion["Rest"] := $recursion["RestSymbol"]
(* under a recursion on a natural number n, f[n - 1] is the recursion's result and n is predecessor + 1 *)
translatedCore[coreForm["Call"][self_String, arguments_List], _] /; self === $naturalRecursion["Self"] && naturalRecursiveCallQ[arguments] := HoldComplete[recursionResult]
translatedCore[coreForm["Local"][local_String], _] /; local === $naturalRecursion["Local"] := HoldComplete[predecessor + 1]

(* a call on n - 1 at the recursion's position, and on each other argument as it is *)
naturalRecursiveCallQ[arguments_List] := And[
	Length[arguments] === Length[$naturalRecursion["Others"]] + 1,
	MatchQ[arguments[[$naturalRecursion["Position"]]], coreForm["Call"]["System`Plus", {coreForm["Local"][$naturalRecursion["Local"]], coreForm["Constant"][-1]}]],
	AllTrue[Normal[$naturalRecursion["Others"]], Function[other, MatchQ[arguments[[First[other]]], coreForm["Local"][Last[other]] | coreForm["Evaluated"][coreForm["Local"][Last[other]]]]]]
]

(* If in a body, its branches the last value of their steps *)
translatedCore[coreForm["If"][condition_, then_, otherwise_, ___], locals_] := (
	Sow[HoldComplete[If], untranslatedCall];
	Replace[Function[part, translatedCore[part, locals]] /@ {condition, then, otherwise}, {HoldComplete[c_], HoldComplete[a_], HoldComplete[b_]} :> HoldComplete[If[c, a, b]]]
)
translatedCore[coreForm["Steps"][{coreForm["Rewritten"][] ..., last_}], locals_] := translatedCore[last, locals]
translatedCore[coreForm["Evaluated"][core_], locals_] := translatedCore[core, locals]
translatedCore[coreForm["Local"][local_String], locals_] := Lookup[locals, local, Throw[None, untranslatable]]
translatedCore[coreForm["Constant"][constant_Integer], _] := HoldComplete[constant]
translatedCore[coreForm["Constant"][constant_Rational], _] := HoldComplete[constant]
translatedCore[coreForm["Level"][_, core_], locals_] := translatedCore[core, locals]
translatedCore[coreForm["Call"][callee_String, arguments_List], locals_] := With[{head = ToExpression[callee, InputForm, HoldComplete]},
	If[! MemberQ[$surfaceHeads, callee], Sow[head, untranslatedCall]];
	Replace[Join[head, Join @@ (Function[argument, translatedCore[argument, locals]] /@ arguments)], HoldComplete[function_, parts___] :> HoldComplete[function[parts]]]
]
translatedCore[_, _] := Throw[None, untranslatable]


(* ::Subsection:: *)
(*Signatures of built-ins*)


(* Expressions, the type of any Wolfram Language expression, into which the numbers of the environment go by coercions *)
(* none where the environment has Expressions already, as TypeTheoryEnvironment["WolframLanguage"] does, with its coercion *)
expressionsDeclarations[environment_] /; constantDeclaredQ[environment, HoldComplete[Expressions]] := {}
expressionsDeclarations[environment_] := Join[
	{
		TypeTheoryAxiom[Expressions, TypeUniverse[1]],
		TypeTheoryAxiom["expressionOfNatural", NonNegativeIntegers -> Expressions, "Implementation" -> Identity],
		TypeTheoryDefinition["ExpressionOfNaturalCoercion", Function[{Typed[n, NonNegativeIntegers]}, "expressionOfNatural"[n]], "Coercion" -> True]
	},
	If[ constantDeclaredQ[environment, HoldComplete[Integers]],
		{
			TypeTheoryAxiom["expressionOfInteger", Integers -> Expressions, "Implementation" -> Identity],
			TypeTheoryDefinition["ExpressionOfIntegerCoercion", Function[{Typed[n, Integers]}, "expressionOfInteger"[n]], "Coercion" -> True]
		},
		{}
	],
	If[ constantDeclaredQ[environment, HoldComplete[Rationals]],
		{
			TypeTheoryAxiom["expressionOfRational", Rationals -> Expressions, "Implementation" -> Identity],
			TypeTheoryDefinition["ExpressionOfRationalCoercion", Function[{Typed[q, Rationals]}, "expressionOfRational"[q]], "Coercion" -> True]
		},
		{}
	]
]

signatures[symbols_HoldComplete, type_HoldComplete] := Association[Function[held, held -> Replace[{held, type}, {HoldComplete[symbol_], HoldComplete[signature_]} :>
	TypeTheoryAxiom[symbol, signature, "Implementation" -> symbol]]] /@ Replace[symbols, HoldComplete[each___] :> (HoldComplete /@ Unevaluated[{each}])]]

(* If[condition, a, b] by the decision of the condition, which elaboration finds as an instance of Decidable; a
   definition, which the kernel checks and computes where the decision does *)
$ifDeclaration = TypeTheoryDefinition[
	If,
	Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[condition, TypeUniverse[0]], Annotation[Typed[decision, Decidable[condition]], "InstanceImplicit"], Typed[a, A], Typed[b, A]},
		InductiveRecursor[Decidable][Function[{Typed[d, Decidable[condition]]}, A], Function[{Typed[h, Not[condition]]}, b], Function[{Typed[h, condition]}, a], decision]
	]
]

(* precise where the built-in allows, over Expressions otherwise; Wolfram computes each, the kernel never does *)
$wolframSignatures = Join[
	<|HoldComplete[If] -> $ifDeclaration|>,
	signatures[HoldComplete[Simplify, FullSimplify, Expand, ExpandAll, Factor, Together, Apart, Cancel], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> A]]],
	signatures[HoldComplete[SameQ, UnsameQ], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> A -> Booleans]]],
	signatures[
		HoldComplete[ListQ, IntegerQ, AtomQ, NumericQ, NumberQ, BooleanQ, TrueQ, StringQ, AssociationQ, VectorQ, MatrixQ, MissingQ],
		HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> Booleans]]
	],
	signatures[HoldComplete[D, ReplaceAll, Dot, Solve, Integrate, Coefficient, Limit, Series], HoldComplete[Expressions -> Expressions -> Expressions]],
	signatures[HoldComplete[Sqrt, Exp, Log, Sin, Cos, Tan, Abs, N, Det, Transpose, Normal, Inverse, Tr], HoldComplete[Expressions -> Expressions]],
	(* total on lists, so typed by their elements *)
	signatures[HoldComplete[Range], HoldComplete[NonNegativeIntegers -> {NonNegativeIntegers}]],
	signatures[HoldComplete[Sort, DeleteDuplicates], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> {A}]]],
	signatures[HoldComplete[MemberQ], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> A -> Booleans]]],
	signatures[HoldComplete[AllTrue, AnyTrue, NoneTrue], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> (A -> Booleans) -> Booleans]]],
	signatures[HoldComplete[Select], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> (A -> Booleans) -> {A}]]],
	signatures[HoldComplete[Total], HoldComplete[{Expressions} -> Expressions]],
	(* partial, as First of an empty list, or of any expression, so over Expressions *)
	signatures[HoldComplete[First, Last, Rest, Most, Flatten, Missing, Association, Head, Keys, Values], HoldComplete[Expressions -> Expressions]],
	signatures[HoldComplete[Part, Extract, Apply, Rule, Lookup, KeyExistsQ, FreeQ, Count, Take, Drop, Coefficient, Mod, Quotient], HoldComplete[Expressions -> Expressions -> Expressions]]
]
