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
	an axiom           otherwise, of the type "Type" gives, or of the type "Expressions" -> ... -> "Expressions" its
	                   arguments take, with "Implementation" -> symbol: Wolfram computes it, the kernel never does

A built-in that a body calls gets its signature from $wolframSignatures, declared only where it is used and not
declared already: precise where the built-in allows, as Simplify : A -> A, and over "Expressions", the type of any
Wolfram Language expression, otherwise. No equation about a built-in is assumed, so nothing more is trusted.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryFormalize]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[lowerDefinitions]
PackageScoped[loadKernelCompiler]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryFormalize::usage = "TypeTheoryFormalize[symbol] gives the declarations that make the Wolfram Language function symbol a constant of the default environment: a definition read off its definitions where they translate, typed by elaboration, and otherwise an axiom that symbol computes. TypeTheoryFormalize[symbol, environment] makes them for environment. The option \"Type\" -> type gives the type the constant must have."
lowerDefinitions::usage = "lowerDefinitions[HoldComplete[symbol]] gives the Core`Program of the definitions of symbol, by the compiler's ToCore, or a Failure."
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

TypeTheoryFormalize[symbol_Symbol, options : OptionsPattern[]] := catchKernelFailure[formalize[defaultEnvironment[], HoldComplete[symbol], formalizeType[Hold[options]]]]
TypeTheoryFormalize[symbol_Symbol, environment_, options : OptionsPattern[]] /; environmentQ[environment] :=
	catchKernelFailure[formalize[environment, HoldComplete[symbol], formalizeType[Hold[options]]]]

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
	{value_HoldComplete, calls_List} :> candidateDeclarations[environment, held, type, definitions, calls, Function[extended, {value}]],
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

definitionOf[HoldComplete[symbol_], HoldComplete[value_], None] := TypeTheoryDefinition[symbol, value]
definitionOf[HoldComplete[symbol_], HoldComplete[value_], HoldComplete[type_]] := TypeTheoryDefinition[symbol, Typed[value, type]]

(* the axiom that the symbol computes, of the type given, or of the type "Expressions" -> ... -> "Expressions" its
   arguments take *)
fallbackDeclarations[environment_, held_, None, definitions_] := Replace[definitionArities[definitions], {
	{arity_Integer} :> Append[missingDeclarations[environment, expressionsDeclarations[environment]], implementedAxiom[held, expressionsType[arity]]],
	_ :> kernelFailure["Unformalizable", "The definitions of `1` do not take one number of arguments: give its type with \"Type\".", {HoldForm @@ held}]
}]
fallbackDeclarations[_, held_, type_HoldComplete, _] := {implementedAxiom[held, type]}

implementedAxiom[HoldComplete[symbol_], HoldComplete[type_]] := TypeTheoryAxiom[symbol, type, "Implementation" -> symbol]

definitionArities[definitions_] := Union[Cases[definitions, coreForm["Definition"][_, coreForm["Program"][{___, coreForm["Length"][{}, arity_Integer], ___}], ___] :> arity]]

expressionsType[arity_Integer] := HoldComplete @@ {Fold[Function[{codomain, domain}, domain -> codomain], "Expressions", ConstantArray["Expressions", arity]]}

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
		missingDeclarations[environment, Append[If[FreeQ[$wolframSignatures[call], "Expressions"], {}, expressionsDeclarations[environment]], $wolframSignatures[call]]],
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
translatedDefinitions[held_, definitions : {_, _}] := Catch[
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

emptyListDefinitionQ[coreForm["Definition"][_, coreForm["Program"][{coreForm["Length"][{}, 1], coreForm["Same"][{1}, HoldComplete[{}]]}], ___]] := True
emptyListDefinitionQ[_] := False

(* the recursion a prepend case is translated under: the symbol itself, and the rest of the list, bound as a sequence *)
$recursion = <||>

(* the candidate values of a definition by recursion on a list: its types from "Type" where given, Lists[a] -> b, and
   otherwise of the type the empty case has, its elements of any type first and of that type then *)
listRecursionCandidates[environment_, HoldComplete[Lists[elementType_] -> resultType_], parts_] :=
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
		Function[{binders, Typed[listArgument, Lists[a]]},
			InductiveRecursor[Lists][
				Function[{Typed[list, Lists[a]]}, b],
				empty,
				Function[{Typed[head, a], Typed[rest, Lists[a]], Typed[recursionResult, b]}, prepend],
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


(* "Expressions", the type of any Wolfram Language expression, into which the numbers of the environment go by coercions *)
expressionsDeclarations[environment_] := Join[
	{
		TypeTheoryAxiom["Expressions", TypeUniverse[1]],
		TypeTheoryAxiom["expressionOfNatural", NonNegativeIntegers -> "Expressions", "Implementation" -> Identity],
		TypeTheoryDefinition["ExpressionOfNaturalCoercion", Function[{Typed[n, NonNegativeIntegers]}, "expressionOfNatural"[n]], "Coercion" -> True]
	},
	If[ constantDeclaredQ[environment, HoldComplete[Integers]],
		{
			TypeTheoryAxiom["expressionOfInteger", Integers -> "Expressions", "Implementation" -> Identity],
			TypeTheoryDefinition["ExpressionOfIntegerCoercion", Function[{Typed[n, Integers]}, "expressionOfInteger"[n]], "Coercion" -> True]
		},
		{}
	],
	If[ constantDeclaredQ[environment, HoldComplete[Rationals]],
		{
			TypeTheoryAxiom["expressionOfRational", Rationals -> "Expressions", "Implementation" -> Identity],
			TypeTheoryDefinition["ExpressionOfRationalCoercion", Function[{Typed[q, Rationals]}, "expressionOfRational"[q]], "Coercion" -> True]
		},
		{}
	]
]

signatures[symbols_HoldComplete, type_HoldComplete] := Association[Function[held, held -> Replace[{held, type}, {HoldComplete[symbol_], HoldComplete[signature_]} :>
	TypeTheoryAxiom[symbol, signature, "Implementation" -> symbol]]] /@ Replace[symbols, HoldComplete[each___] :> (HoldComplete /@ Unevaluated[{each}])]]

(* precise where the built-in allows, over "Expressions" otherwise; Wolfram computes each, the kernel never does *)
$wolframSignatures = Join[
	signatures[HoldComplete[Simplify, FullSimplify, Expand, ExpandAll, Factor, Together, Apart, Cancel], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> A]]],
	signatures[HoldComplete[SameQ, UnsameQ], HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> A -> Booleans]]],
	signatures[
		HoldComplete[ListQ, IntegerQ, AtomQ, NumericQ, NumberQ, BooleanQ, TrueQ, StringQ, AssociationQ, VectorQ, MatrixQ, MissingQ],
		HoldComplete[ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> Booleans]]
	],
	signatures[HoldComplete[D, ReplaceAll, Dot, Solve, Integrate, Coefficient, Limit, Series], HoldComplete["Expressions" -> "Expressions" -> "Expressions"]],
	signatures[HoldComplete[Sqrt, Exp, Log, Sin, Cos, Tan, Abs, N, Det, Transpose, Normal, Inverse, Tr], HoldComplete["Expressions" -> "Expressions"]]
]
