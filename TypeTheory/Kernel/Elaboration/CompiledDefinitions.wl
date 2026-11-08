(* ::Package:: *)

(*
CompiledDefinitions: the meaning of a Wolfram Language function as the compiler's typed entry runs it, in an environment
of the machine integers, TypeTheoryEnvironment["Machine"].

The compiler of the WolframKernel project, the paclet Wolfram/KernelCompiler, gives a function that computes on machine
numbers a typed entry: its TypedSignatures gives the types of the parameters and the result, and the body in
administrative normal form, one statement for each step the C takes. Each step is read as what the machine computes:

	t = Plus[a, b], Times[a, b]     the machine result of the exact sum or product, "machineResult"[a + b], the leave
	                                Failure["IntegerOverflow", <||>] out of range; more arguments combine pairwise, in
	                                order, each step a result of its own, as the C combines them
	t = Less[a, b], Equal[a, b]     the Boolean of the integers' order or equality, which never leaves
	If[test, then, else]            "machineIf" of the test, each branch a block of its own
	t = g[a, ...]                   a call of another function with a typed entry, formalized first

A step that may leave continues by "confirmBind", so that the function leaves where any step does: its value is of
"Integer64" | Failure, and where it is the failure the generic code of the Wolfram Language computes the call instead,
exactly. The meaning is the value of the typed code where it does not leave. The checks of the recursion level, which
depend on the caller and not on the arguments, are not part of it, and a function that calls itself is not formalized
yet.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[compiledDeclarations]
PackageScoped[machineEnvironmentQ]


(* ::Section:: *)
(*Usage Messages*)


compiledDeclarations::usage = "compiledDeclarations[environment, HoldComplete[symbol]] gives the definitions of symbol and the functions it calls as the compiler's typed entries compute them, in an environment of the machine integers."
machineEnvironmentQ::usage = "machineEnvironmentQ[environment] is True if environment declares the machine integers of TypeTheoryEnvironment[\"Machine\"]."


(* ::Section:: *)
(*Function Definitions*)


machineEnvironmentQ[environment_] := constantDeclaredQ[environment, HoldComplete["machineResult"]]

(* the context of the variables the steps bind, named as the compiler names its temporaries *)
$compiledContext = "WolframInstitute`TypeTheory`Compiled`"

compiledDeclarations[environment_, held : HoldComplete[symbol_Symbol]] := Which[
	! machineEnvironmentQ[environment],
		kernelFailure["NoMachineIntegers", "The compiled meaning of `1` needs the machine integers: formalize it in TypeTheoryEnvironment[\"Machine\"].", {HoldForm[symbol]}],
	True,
		Replace[loadKernelCompiler[], {
			failure_Failure :> failure,
			True :> compiledProgramDeclarations[environment, held, typedSignaturesOf[held]]
		}]
]

(* the compiler's typed signatures of the symbol and the functions it calls, for machine integers as the arguments' patterns
   say *)
typedSignaturesOf[held : HoldComplete[symbol_Symbol]] := With[
	{types = argumentTypes[held], name = fullName[symbol]},
	Replace[
		Quiet[kernelCompilerSymbol["TypedSignatures"][Language`ExtendedFullDefinition[symbol], <|name -> types|>]],
		{
			signatures_Association /; KeyExistsQ[signatures, name] :> coreNormal[signatures],
			_ :> kernelFailure["NoTypedEntry", "The compiler gives `1` no typed entry: it computes on more than machine integers, or its definitions are more than one.", {HoldForm[symbol]}]
		}
	]
]

(* "MachineInteger" for each argument x_Integer of the one definition, the patterns matched as written *)
argumentTypes[HoldComplete[symbol_Symbol]] := Replace[Map[definitionArguments, definitionStatements[symbol]], {
	{arguments : HoldComplete[Verbatim[Pattern][_Symbol, Verbatim[Blank][Integer]]...]} :> ConstantArray["MachineInteger", Length[arguments]],
	_ :> kernelFailure["NoTypedEntry", "The compiled meaning of `1` needs one definition whose arguments are each x_Integer, as the compiler types it.", {HoldForm[symbol]}]
}]

(* the definitions of the functions that the symbol reaches, each after the ones it calls, and the symbol's last *)
compiledProgramDeclarations[environment_, HoldComplete[symbol_Symbol], signatures_Association] := Fold[
	Function[{declarations, name}, Join[declarations, compiledFunctionDeclarations[TypeTheoryEnvironment[environment, declarations], name, signatures]]],
	{},
	callOrder[fullName[symbol], signatures, {}]
]

(* the names in the order they are declared: each function after those it calls *)
callOrder[name_String, signatures_Association, seen_List] := Which[
	MemberQ[Join[signatures[name]["Calls"], signatures[name]["Reached"]], name],
		kernelFailure["Recursive", "The typed code of `1` calls itself: recursion is not formalized for the machine yet.", {ToExpression[name, InputForm, HoldForm]}],
	True,
		DeleteDuplicates[Append[
			Catenate[Map[Function[callee, callOrder[callee, signatures, Append[seen, name]]], Select[signatures[name]["Calls"], Function[callee, ! MemberQ[seen, callee]]]]],
			name
		]]
]

compiledFunctionDeclarations[environment_, name_String, signatures_Association] := With[
	{held = ToExpression[name, InputForm, HoldComplete]},
	If[constantDeclaredQ[environment, held], {}, {compiledDefinition[held, signatures[name], signatures]}]
]

(* the definition: a function of the parameters, of their machine types, to the result or its leave *)
compiledDefinition[held : HoldComplete[symbol_Symbol], signature_Association, signatures_Association] := With[
	{parameters = parameterTerms[held, signature["Parameters"]]},
	definitionDeclaration[
		held,
		functionTerm[Map[Function[parameter, {First[parameter], machineType[Last[parameter]]}], parameters], blockTerm[signature["Body"], parameterScope[signature["Parameters"], parameters], signature, signatures]],
		functionType[Map[Function[parameter, machineType[Last[parameter]]], parameters], resultType[signature["Result"]]]
	]
]

definitionDeclaration[HoldComplete[symbol_], HoldComplete[value_], HoldComplete[type_]] := TypeTheoryDefinition[symbol, Typed[value, type]]

(* each parameter's symbol, from the pattern at its position, and its machine type *)
parameterTerms[HoldComplete[symbol_Symbol], parameters_List] := With[
	{names = Replace[Map[definitionArguments, definitionStatements[symbol]], {{arguments_HoldComplete} :> List @@ Map[patternName, arguments], _ :> {}}]},
	Map[
		Function[parameter, Replace[parameter, {
			{position_Integer, _, type_String} /; position <= Length[names] :> {Extract[names, position], type},
			_ :> kernelFailure["NoTypedEntry", "The typed entry of `1` has a parameter its definition does not name.", {HoldForm[symbol]}]
		}]],
		parameters
	]
]

(* the arguments of a definition's left side, held, whose head DownValues keep in HoldPattern *)
definitionArguments[HoldComplete[SetDelayed[Verbatim[HoldPattern][_[arguments___]], _]]] := HoldComplete[arguments]
definitionArguments[HoldComplete[SetDelayed[_[arguments___], _]]] := HoldComplete[arguments]
definitionArguments[_] := None

SetAttributes[patternName, HoldAllComplete]
patternName[Verbatim[Pattern][name_Symbol, _]] := HoldComplete[name]

parameterScope[parameters_List, terms_List] := Association[MapThread[
	Function[{parameter, term}, {"L", Extract[parameter, 2]} -> {First[term], Last[term]}],
	{parameters, terms}
]]

machineType["Int64"] := HoldComplete["Integer64"]
machineType["Bool"] := HoldComplete["Boolean"]
machineType[type_] := kernelFailure["UnmodeledType", "The typed code computes on `1`, which the machine model does not have yet: it has \"Int64\" and \"Bool\".", {type}]

resultType[type_String] := Replace[machineType[type], HoldComplete[machine_] :> HoldComplete[machine | Failure]]

functionTerm[{}, HoldComplete[body_]] := HoldComplete[body]
functionTerm[parameters_List, body_HoldComplete] := Replace[
	Map[Function[parameter, Replace[parameter, {HoldComplete[name_], HoldComplete[type_]} :> HoldComplete[Typed[name, type]]]], parameters],
	binders_ :> Replace[Thread[binders, HoldComplete], HoldComplete[{typed___}] :> Replace[body, HoldComplete[term_] :> HoldComplete[Function[{typed}, term]]]]
]

functionType[domains_List, HoldComplete[codomain_]] := Fold[
	Function[{range, domain}, Replace[{domain, range}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete[a -> b]]],
	HoldComplete[codomain],
	Reverse[domains]
]


(* ::Subsection:: *)
(*Blocks and steps*)


(* a block's statements in turn, then its value, a term of the result type; the scope gives each variable so far its term
   and its kind: "Int64" a machine integer, "Bool" a Boolean, "Integer" an exact integer the code has as a constant *)
blockTerm[coreForm["StatementBlock"][statements_List, value_], scope_Association, signature_Association, signatures_Association] :=
	statementsTerm[expandedStatements[statements], value, scope, signature, signatures]
blockTerm[other_, _, _, _] := unmodeled[other]

statementsTerm[{}, value_, scope_, signature_, _] := valueTerm[atomTerm[value, scope], signature["Result"]]
statementsTerm[{(coreForm["CheckLevel"] | coreForm["SetLevel"])[___], rest___}, value_, scope_, signature_, signatures_] :=
	statementsTerm[{rest}, value, scope, signature, signatures]
statementsTerm[{coreForm["SetTemporary"][t_String, coreForm["Copy"][atom_]], rest___}, value_, scope_, signature_, signatures_] :=
	statementsTerm[{rest}, value, Append[scope, {"T", t} -> atomTerm[atom, scope]], signature, signatures]
statementsTerm[{coreForm["SetTemporary"][t_String, step_], rest___}, value_, scope_, signature_, signatures_] := Replace[stepTerm[step, scope, signature, signatures], {
	{"Pure", term_HoldComplete, kind_String} :> statementsTerm[{rest}, value, Append[scope, {"T", t} -> {term, kind}], signature, signatures],
	{"Result", term_HoldComplete, kind_String} :> boundTerm[term, t, kind, {rest}, value, scope, signature, signatures]
}]
statementsTerm[{coreForm["If"][t_String, test_, then_, else_, ___], rest___}, value_, scope_, signature_, signatures_] := With[
	{kind = Lookup[signature["Variables"], Key[{"T", t}], "Fail"], condition = atomTerm[test, scope]},
	boundTerm[
		Replace[
			{First[condition], blockTerm[then, scope, Append[signature, "Result" -> kind], signatures], blockTerm[else, scope, Append[signature, "Result" -> kind], signatures]},
			{HoldComplete[b_], HoldComplete[x_], HoldComplete[y_]} :> HoldComplete["machineIf"[b, x, y]]
		],
		t, kind, {rest}, value, scope, signature, signatures
	] /; Last[condition] === "Bool"
]
statementsTerm[{other_, ___}, _, _, _, _] := unmodeled[other]

(* the rest of the block continues with the value of a step that may leave, by "confirmBind"; the step itself where the
   block's value is the step's *)
boundTerm[term_HoldComplete, t_String, kind_String, {}, coreForm["Temporary"][t_String], _, _, _] := term
boundTerm[HoldComplete[step_], t_String, kind_String, rest_List, value_, scope_, signature_, signatures_] := With[
	{variable = ToExpression[$compiledContext <> t, InputForm, HoldComplete]},
	Replace[
		{variable, machineType[kind], statementsTerm[rest, value, Append[scope, {"T", t} -> {variable, kind}], signature, signatures]},
		{HoldComplete[name_], HoldComplete[type_], HoldComplete[body_]} :> HoldComplete["confirmBind"[step, Function[{Typed[name, type]}, body]]]
	]
]

(* a call of more than two numbers is the pairwise steps the C takes, each a temporary of its own; a call of a function
   takes machine integers, so a constant argument is first made one *)
expandedStatements[statements_List] := Catenate[Map[expandedStatement, statements]]

expandedStatement[coreForm["SetTemporary"][t_String, coreForm["Call"][operation : "System`Plus" | "System`Times", {first_, second_, more__}]]] :=
	expandedPairwise[t, operation, first, {second, more}]
expandedStatement[statement_] := {statement}

(* Plus[a, b, c] as p1 = Plus[a, b] and t = Plus[p1, c] *)
expandedPairwise[t_String, operation_String, first_, rest_List] := With[
	{names = Append[Table[StringJoin[t, "p", ToString[k]], {k, Length[rest] - 1}], t]},
	MapThread[
		Function[{name, previous, argument}, coreForm["SetTemporary"][name, coreForm["Call"][operation, {previous, argument}]]],
		{names, Prepend[Map[coreForm["Temporary"], Most[names]], first], rest}
	]
]

(* a step's term, {"Pure", term, kind} for a value that never leaves, {"Result", term, kind} for a machine result *)
stepTerm[coreForm["Call"][operation : "System`Plus" | "System`Times", {a_, b_}], scope_, _, _] :=
	Replace[{integerTerm[atomTerm[a, scope]], integerTerm[atomTerm[b, scope]]}, {
		{HoldComplete[x_], HoldComplete[y_]} /; operation === "System`Plus" :> {"Result", HoldComplete["machineResult"[x + y]], "Int64"},
		{HoldComplete[x_], HoldComplete[y_]} :> {"Result", HoldComplete["machineResult"[x y]], "Int64"}
	}]
stepTerm[coreForm["Call"][operation_String, {a_, b_}], scope_, _, _] /; KeyExistsQ[$machineComparisons, operation] :=
	{"Pure", $machineComparisons[operation][integerTerm[atomTerm[a, scope]], integerTerm[atomTerm[b, scope]]], "Bool"}
stepTerm[coreForm["Call"]["System`Not", {a_}], scope_, _, _] :=
	Replace[atomTerm[a, scope], {{HoldComplete[b_], "Bool"} :> {"Pure", HoldComplete["not"[b]], "Bool"}, _ :> unmodeled["System`Not"]}]
stepTerm[coreForm["Call"][name_String, arguments_List], scope_, _, signatures_] /; KeyExistsQ[signatures, name] :=
	{"Result", callTerm[ToExpression[name, InputForm, HoldComplete], Map[Function[argument, machineTerm[atomTerm[argument, scope]]], arguments]], signatures[name]["Result"]}
stepTerm[coreForm["Call"][name_String, _], _, _, _] := unmodeled[name]
stepTerm[other_, _, _, _] := unmodeled[other]

callTerm[HoldComplete[function_], arguments_List] := Replace[Thread[arguments, HoldComplete], HoldComplete[{values___}] :> HoldComplete[function[values]]]

(* the Boolean comparisons of machine integers, by the integers' order and equality *)
$machineComparisons = <|
	"System`LessEqual" -> Function[{x, y}, Replace[{x, y}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete["integerLessEqualQ"[a, b]]]],
	"System`GreaterEqual" -> Function[{x, y}, Replace[{x, y}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete["integerLessEqualQ"[b, a]]]],
	"System`Less" -> Function[{x, y}, Replace[{x, y}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete["not"["integerLessEqualQ"[b, a]]]]],
	"System`Greater" -> Function[{x, y}, Replace[{x, y}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete["not"["integerLessEqualQ"[a, b]]]]],
	"System`Equal" -> Function[{x, y}, Replace[{x, y}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete["integerEqual"[a, b]]]],
	"System`Unequal" -> Function[{x, y}, Replace[{x, y}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete["not"["integerEqual"[a, b]]]]]
|>


(* ::Subsection:: *)
(*Atoms*)


(* an atom's term and kind: a variable's from the scope, a constant's by its value *)
atomTerm[coreForm["Local"][name_String], scope_] := Lookup[scope, Key[{"L", name}], unmodeled[coreForm["Local"][name]]]
atomTerm[coreForm["Temporary"][name_String], scope_] := Lookup[scope, Key[{"T", name}], unmodeled[coreForm["Temporary"][name]]]
(* a constant is written bare: where the machine takes it, an integer is expected *)
atomTerm[coreForm["Constant"][value_Integer], _] := {HoldComplete[value], "Integer"}
atomTerm[coreForm["Constant"][True], _] := {HoldComplete["true"], "Bool"}
atomTerm[coreForm["Constant"][False], _] := {HoldComplete["false"], "Bool"}
atomTerm[other_, _] := unmodeled[other]

(* the exact integer of a machine integer or a constant *)
integerTerm[{HoldComplete[x_], "Int64"}] := HoldComplete[x[[1]]]
integerTerm[{term_HoldComplete, "Integer"}] := term
integerTerm[{_, kind_}] := unmodeled[kind]

(* a machine integer or a Boolean as a value, a constant by the machine integer it is *)
machineTerm[{term_HoldComplete, "Int64" | "Bool"}] := term
machineTerm[{HoldComplete[x_], "Integer"}] := HoldComplete["machineResult"[x]]

(* the block's value as a result: a machine integer or a Boolean that never left, or a constant's machine result *)
valueTerm[{HoldComplete[x_], "Int64"}, "Int64"] := HoldComplete[Typed["left"[x], "Integer64" | Failure]]
valueTerm[{HoldComplete[x_], "Bool"}, "Bool"] := HoldComplete[Typed["left"[x], "Boolean" | Failure]]
valueTerm[{HoldComplete[x_], "Integer"}, "Int64"] := HoldComplete["machineResult"[x]]
valueTerm[{_, kind_}, result_] := unmodeled[{kind, result}]

unmodeled[form_] := kernelFailure["UnmodeledOperation", "The typed code has `1`, which the machine model does not have yet.", {Short[form, 2]}]
