(* ::Package:: *)

(*
CompiledDefinitions: the meaning of a Wolfram Language function as the compiler's typed entry runs it, in an environment
of the machine integers, TypeTheoryEnvironment["Machine"].

The compiler of the WolframKernel project, the paclet Wolfram/KernelCompiler, gives a function that computes on machine
numbers a typed entry: its TypedSignatures gives the types of the parameters and the result, and the body in
administrative normal form, one statement for each step the C takes. Each step is read as what the machine computes:

	t = Plus[a, b], Times[a, b]     "machinePlus" and "machineTimes" of the integers of a and b, a[["integer"]] for a machine
	                                integer a: the machine result of the exact sum or product, the leave
	                                Failure["IntegerOverflow", <||>] out of range; more arguments combine pairwise, in
	                                order, each step a result of its own, as the C combines them
	t = Quotient[a, b], Mod[a, b]   "machineQuotient" and "machineMod", rounded down as the integers' and leaving
	                                with Failure["DivideByZero", <||>] by 0, as the C does
	t = Less[a, b], Equal[a, b]     the Boolean of the integers' order or equality, which never leaves
	If[test, then, else]            "machineIf" of the test, each branch a block of its own
	t = g[a, ...]                   a call of another function with a typed entry, formalized first

A step that may leave continues by "confirmBind", so that the function leaves where any step does: its value is of
"Integer64" | Failure, and where it is the failure the generic code of the Wolfram Language computes the call instead,
exactly. The meaning is the value of the typed code where it does not leave. The checks of the recursion level, which
depend on the caller and not on the arguments, are not part of it; but a function that calls itself takes first the
levels its recursion may use, a natural number, each call of itself one, and leaves with Failure["RecursionLimit", <||>]
where none is left, as a typed entry leaves where its recursion passes its bound. Functions that call each other are
not formalized yet.

A While of typed code has no bound, and a definition must end: a function with a loop takes fuel, a natural number
after the levels, the iterations each of its loops may take, and a loop out of fuel gives Failure["OutOfFuel", <||>],
which is no value of the typed entry but the meaning given too little: a theorem about a loop holds of all fuel from
some on, and of a run that nothing aborts. A local set in straight code is its new value from there on; the locals a
loop sets are its state.
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
			signatures_Association /; KeyExistsQ[signatures, name] :> standardTypeNames[coreNormal[signatures]],
			_ :> kernelFailure["NoTypedEntry", "The compiler gives `1` no typed entry: it computes on more than machine integers, or its definitions are more than one.", {HoldForm[symbol]}]
		}
	]
]

(* The compiler writes its types "Int64" and "Bool". From here on they go by their standard names, "Integer64" and
   "Boolean", the names of the environment's types: the type of each parameter, of each variable and of the result. *)
standardTypeNames[signatures_Association] := Map[
	Function[signature, Join[signature, <|
		"Parameters" -> Replace[signature["Parameters"], {position_, middle_, type_String} :> {position, middle, standardTypeName[type]}, {1}],
		"Variables" -> Map[standardTypeName, signature["Variables"]],
		"Result" -> standardTypeName[signature["Result"]]
	|>]],
	signatures
]

standardTypeName["Int64"] := "Integer64"
standardTypeName["Bool"] := "Boolean"
standardTypeName[type_] := type

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
	mutuallyRecursiveQ[name, signatures],
		kernelFailure["Recursive", "The typed code of `1` calls itself through another function: mutual recursion is not formalized for the machine yet.", {ToExpression[name, InputForm, HoldForm]}],
	True,
		DeleteDuplicates[Append[
			Catenate[Map[Function[callee, callOrder[callee, signatures, Append[seen, name]]], Select[signatures[name]["Calls"], Function[callee, ! MemberQ[Append[seen, name], callee]]]]],
			name
		]]
]

(* a function that calls itself, directly *)
selfRecursiveQ[name_String, signatures_Association] := MemberQ[signatures[name]["Calls"], name]

(* a function that a function it calls reaches back to *)
mutuallyRecursiveQ[name_String, signatures_Association] := AnyTrue[
	DeleteCases[signatures[name]["Calls"], name],
	Function[callee, MemberQ[Join[signatures[callee]["Calls"], signatures[callee]["Reached"]], name]]
]

(* a function whose meaning takes the levels its recursion may use: one that calls itself, or calls one that does *)
leveledQ[name_String, signatures_Association] := selfRecursiveQ[name, signatures] || AnyTrue[DeleteCases[signatures[name]["Calls"], name], Function[callee, leveledQ[callee, signatures]]]

(* a function whose meaning takes fuel, the iterations its loops may take: one with a While, or one that calls one with
   fuel *)
fueledQ[name_String, signatures_Association] := ! FreeQ[signatures[name]["Body"], coreForm["While"]] || AnyTrue[DeleteCases[signatures[name]["Calls"], name], Function[callee, fueledQ[callee, signatures]]]

compiledSymbol[name_String] := ToExpression[$compiledContext <> name, InputForm, HoldComplete]

compiledFunctionDeclarations[environment_, name_String, signatures_Association] := With[
	{held = ToExpression[name, InputForm, HoldComplete]},
	If[constantDeclaredQ[environment, held], {}, compiledDefinitions[held, signatures[name], signatures]]
]

(* the function's definition after those of its loops, which its translation sows as it meets them *)
$loopTag = "CompiledLoop"
$loopCount = 0

compiledDefinitions[held_HoldComplete, signature_Association, signatures_Association] := Block[{$loopCount = 0},
	Replace[Reap[compiledDefinition[held, signature, signatures], $loopTag], {definition_, loops_List} :> Append[Catenate[loops], definition]]
]

(* the definition: a function of the parameters, of their machine types, to the result or its leave. Two budgets come
   first, each a natural number, where the function needs them. The levels are the compiler's: a typed entry leaves where
   its recursion is deeper than its bound, so a function that calls itself is defined by recursion on the levels left,
   each call of itself a level, and leaves with Failure["RecursionLimit", <||>] where none is left; a function that calls
   such a function passes its levels on. The fuel is the proof's: a loop of typed code has no bound, so a While is
   defined by recursion on the fuel, the iterations it may take, and gives Failure["OutOfFuel", <||>] where none is left,
   which is no value of the typed entry but the meaning given too few iterations; a call passes the fuel on, and a
   theorem holds of all fuel from some on *)
compiledDefinition[held : HoldComplete[symbol_Symbol], signature_Association, signatures_Association] := With[
	{
		parameters = parameterTerms[held, signature["Parameters"]],
		name = fullName[symbol],
		levels = compiledSymbol["levels"],
		levelsLeft = compiledSymbol["levelsLeft"],
		fuel = compiledSymbol["fuel"],
		recursion = compiledSymbol["recursion"]
	},
	With[
		{
			binders = Map[Function[parameter, {First[parameter], machineType[Last[parameter]]}], parameters],
			ownType = functionType[Map[Function[parameter, machineType[Last[parameter]]], parameters], resultType[signature["Result"]]],
			scope = parameterScope[signature["Parameters"], parameters],
			budgets = Join[
				If[leveledQ[name, signatures], {{levels, HoldComplete[NonNegativeIntegers]}}, {}],
				If[fueledQ[name, signatures], {{fuel, HoldComplete[NonNegativeIntegers]}}, {}]
			],
			context = Join[signature, <|
				"Name" -> name,
				"Symbol" -> SymbolName[Unevaluated[symbol]],
				"Levels" -> Which[selfRecursiveQ[name, signatures], levelsLeft, leveledQ[name, signatures], levels, True, None],
				"Fuel" -> If[fueledQ[name, signatures], fuel, None],
				"Recursion" -> If[selfRecursiveQ[name, signatures], recursion, None]
			|>]
		},
		With[{body = blockTerm[signature["Body"], scope, context, signatures]},
			definitionDeclaration[
				held,
				functionTerm[
					Join[budgets, binders],
					If[selfRecursiveQ[name, signatures], recursionTerm[levels, levelsLeft, recursion, binders, ownType, body, signature["Result"]], body]
				],
				functionType[Map[Last, budgets], ownType]
			]
		]
	]
]

(* recursion on the levels: with none, the leave; with one more than levelsLeft, the body, whose calls of itself are
   recursion, the function at levelsLeft; then applied to the parameters *)
recursionTerm[HoldComplete[levels_], HoldComplete[levelsLeft_], HoldComplete[recursion_], binders_List, HoldComplete[type_], body_HoldComplete, result_String] := With[
	{leave = functionTerm[binders, Replace[resultType[result], HoldComplete[r_] :> HoldComplete[Typed["right"[Failure["RecursionLimit", <||>]], r]]]], step = functionTerm[binders, body]},
	Replace[{leave, step, callTerm[HoldComplete[Null], Map[First, binders]]}, {HoldComplete[l_], HoldComplete[f_], HoldComplete[Null[arguments___]]} :>
		HoldComplete[InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[WolframInstitute`TypeTheory`Compiled`j, NonNegativeIntegers]}, type],
			l,
			Function[{Typed[levelsLeft, NonNegativeIntegers], Typed[recursion, type]}, f],
			levels
		][arguments]]
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

machineType[type : "Integer64" | "Boolean"] := HoldComplete[type]
machineType[type_] := kernelFailure["UnmodeledType", "The typed code computes on `1`, which the machine model does not have yet: it has \"Integer64\" and \"Boolean\".", {type}]

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


(* a block's statements in turn, then its ending; the scope gives each variable so far its term and its kind: "Integer64" a
   machine integer, "Boolean" a Boolean, "Integer" an exact integer the code has as a constant. A block ends with its value,
   valueEnding[atom], a term of the result type, or goes on as continuationEnding[f] says of the scope it ends with, as
   the test and the body of a loop do *)
blockTerm[coreForm["StatementBlock"][statements_List, value_], scope_Association, signature_Association, signatures_Association] :=
	statementsTerm[expandedStatements[statements], valueEnding[value], scope, signature, signatures]
blockTerm[other_, _, _, _] := unmodeled[other]

endingTerm[valueEnding[atom_], scope_, signature_] := valueTerm[atomTerm[atom, scope], signature["Result"]]
endingTerm[continuationEnding[continuation_], scope_, _] := continuation[scope]

statementsTerm[{}, ending_, scope_, signature_, _] := endingTerm[ending, scope, signature]
statementsTerm[{(coreForm["CheckLevel"] | coreForm["SetLevel"])[___], rest___}, ending_, scope_, signature_, signatures_] :=
	statementsTerm[{rest}, ending, scope, signature, signatures]
statementsTerm[{coreForm["SetTemporary"][t_String, coreForm["Copy"][atom_]], rest___}, ending_, scope_, signature_, signatures_] :=
	statementsTerm[{rest}, ending, Append[scope, {"T", t} -> atomTerm[atom, scope]], signature, signatures]
statementsTerm[{coreForm["SetTemporary"][t_String, step_], rest___}, ending_, scope_, signature_, signatures_] := Replace[stepTerm[step, scope, signature, signatures], {
	{"Pure", term_HoldComplete, kind_String} :> statementsTerm[{rest}, ending, Append[scope, {"T", t} -> {term, kind}], signature, signatures],
	{"Result", term_HoldComplete, kind_String} :> boundTerm[term, {"T", t}, compiledSymbol[t], kind, {rest}, ending, scope, signature, signatures]
}]
(* a local set to a value is that value from here on; set to a constant, the machine integer of it, a step of its own *)
statementsTerm[{coreForm["SetLocal"][v_String, atom_], rest___}, ending_, scope_, signature_, signatures_] := Replace[atomTerm[atom, scope], {
	{HoldComplete[constant_], "Integer"} :> boundTerm[HoldComplete["machineResult"[constant]], {"L", v}, localSymbol[v], "Integer64", {rest}, ending, scope, signature, signatures],
	entry_ :> statementsTerm[{rest}, ending, Append[scope, {"L", v} -> entry], signature, signatures]
}]
(* a branch that sets a local would have to give the local back with its value: not yet *)
statementsTerm[{coreForm["If"][_, _, then_, else_, ___], ___}, _, _, _, _] /; ! FreeQ[{then, else}, coreForm["SetLocal"] | coreForm["While"]] :=
	unmodeled["an If whose branch sets a local"]
statementsTerm[{coreForm["If"][t_String, test_, then_, else_, ___], rest___}, ending_, scope_, signature_, signatures_] := With[
	{kind = Lookup[signature["Variables"], Key[{"T", t}], "Fail"], condition = atomTerm[test, scope]},
	boundTerm[
		Replace[
			{First[condition], blockTerm[then, scope, Append[signature, "Result" -> kind], signatures], blockTerm[else, scope, Append[signature, "Result" -> kind], signatures]},
			{HoldComplete[b_], HoldComplete[x_], HoldComplete[y_]} :> HoldComplete["machineIf"[b, x, y]]
		],
		{"T", t}, compiledSymbol[t], kind, {rest}, ending, scope, signature, signatures
	] /; Last[condition] === "Boolean"
]
statementsTerm[{coreForm["While"][test_, body_], rest___}, ending_, scope_, signature_, signatures_] :=
	loopTerm[test, body, {rest}, ending, scope, signature, signatures, ++$loopCount]
statementsTerm[{other_, ___}, _, _, _, _] := unmodeled[other]

(* the rest of the block continues with the value of a step that may leave, by "confirmBind", the value bound to a
   variable under the key of the scope; the step itself where the block's value is the step's *)
boundTerm[term_HoldComplete, {"T", t_String}, _, _, {}, valueEnding[coreForm["Temporary"][t_String]], _, _, _] := term
boundTerm[HoldComplete[step_], key_List, variable_HoldComplete, kind_String, rest_List, ending_, scope_, signature_, signatures_] :=
	Replace[
		{variable, machineType[kind], statementsTerm[rest, ending, Append[scope, key -> {variable, kind}], signature, signatures]},
		{HoldComplete[name_], HoldComplete[type_], HoldComplete[body_]} :> HoldComplete["confirmBind"[step, Function[{Typed[name, type]}, body]]]
	]

(* the variable of a local: its name in the source and its number in the code, s2 for the compiler's vs_2 *)
localSymbol[v_String] := compiledSymbol[StringReplace[v, {StartOfString ~~ "v" -> "", "_" -> ""}]]


(* ::Subsection:: *)
(*Loops*)


(* A While is a constant of its own, "While[f]" for the first of the function f and "While[f, k]" for the k-th, so that a
   proof can state what it keeps. Its state is the locals that its test or its body set, of those set before it, in the
   order they are first set: each is an argument of its own, after the locals the loop only reads, and its value is their
   nested pair. It is the recursion on the fuel: with none, Failure["OutOfFuel", <||>]; with one more than fuelLeft, the
   test, then where it is true the body and the loop at fuelLeft on the locals as the body leaves them, and where it is
   false the pair of the locals as the test leaves them. A step of the test or the body that leaves is the function's
   leave. The function goes on with the loop's value, the locals as its parts. The locals are arguments, not one pair,
   so that each is a variable whose value a round reads at once: a part of a part of a pair would carry the pair along. *)
loopTerm[test : coreForm["StatementBlock"][_List, _], body : coreForm["StatementBlock"][_List, _], rest_List, ending_, scope_, signature_, signatures_, index_Integer] := With[
	{
		assigned = Select[DeleteDuplicates[Cases[{test, body}, coreForm["SetLocal"][v_String, _] :> v, Infinity]], Function[v, KeyExistsQ[scope, {"L", v}]]],
		name = loopName[signature["Symbol"], index],
		stateOut = compiledSymbol["state" <> ToString[index]]
	},
	With[
		{
			read = Select[DeleteDuplicates[Cases[{test, body}, coreForm["Local"][v_String] :> v, Infinity]], Function[v, KeyExistsQ[scope, {"L", v}] && ! MemberQ[assigned, v]]],
			kinds = Map[Function[v, Last[scope[{"L", v}]]], assigned]
		},
		Which[
			assigned === {},
				unmodeled["a While that sets no local"],
			signature["Fuel"] === None,
				unmodeled["a While without fuel"],
			True,
				loopBound[
					Sow[loopDeclaration[name, assigned, kinds, read, test, body, scope, signature, signatures], $loopTag],
					callTerm[HoldComplete[name], Join[
						If[signature["Levels"] === None, {}, {signature["Levels"]}],
						{signature["Fuel"]},
						Map[Function[v, First[scope[{"L", v}]]], read],
						Map[Function[v, First[scope[{"L", v}]]], assigned]
					]],
					stateOut,
					tupleType[Map[machineType, kinds]],
					statementsTerm[rest, ending, Join[scope, stateScope[assigned, kinds, stateOut]], signature, signatures]
				]
		]
	]
]
loopTerm[test_, _, _, _, _, _, _, _] := unmodeled[test]

loopBound[_, HoldComplete[call_], HoldComplete[out_], HoldComplete[type_], HoldComplete[after_]] := HoldComplete["confirmBind"[call, Function[{Typed[out, type]}, after]]]

loopName[symbol_String, 1] := "While[" <> symbol <> "]"
loopName[symbol_String, index_Integer] := "While[" <> symbol <> ", " <> ToString[index] <> "]"

(* the locals of a state as the parts of the term that holds it *)
stateScope[assigned_List, kinds_List, state_HoldComplete] := Association[MapThread[
	Function[{v, kind, part}, {"L", v} -> {part, kind}],
	{assigned, kinds, projectionTerms[state, Length[assigned]]}
]]

loopDeclaration[name_String, assigned_List, kinds_List, read_List, coreForm["StatementBlock"][testStatements_List, testValue_], coreForm["StatementBlock"][bodyStatements_List, _], scope_, signature_, signatures_] := With[
	{
		loop = compiledSymbol["loop"],
		fuel = compiledSymbol["fuel"],
		fuelLeft = compiledSymbol["fuelLeft"],
		levels = compiledSymbol["levels"],
		stateType = tupleType[Map[machineType, kinds]],
		readBinders = Map[Function[v, {localSymbol[v], machineType[Last[scope[{"L", v}]]]}], read],
		stateBinders = MapThread[Function[{v, kind}, {localSymbol[v], machineType[kind]}], {assigned, kinds}]
	},
	With[
		{
			(* in the loop each local is a variable of its own: the ones it reads its arguments, the ones it sets the
			   arguments of each round *)
			inner = Association[Join[
				Map[Function[v, {"L", v} -> {localSymbol[v], Last[scope[{"L", v}]]}], read],
				MapThread[Function[{v, kind}, {"L", v} -> {localSymbol[v], kind}], {assigned, kinds}]
			]],
			(* the levels and the fuel are the loop's own arguments, and the function's recursion is out of reach *)
			context = Join[signature, <|"Levels" -> If[signature["Levels"] === None, None, levels], "Fuel" -> fuel, "Recursion" -> None|>],
			stateTerms = Function[ended, Map[Function[v, First[ended[{"L", v}]]], assigned]],
			budgets = Join[If[signature["Levels"] === None, {}, {{levels, HoldComplete[NonNegativeIntegers]}}], {{fuel, HoldComplete[NonNegativeIntegers]}}],
			roundType = functionType[Map[Last, stateBinders], Replace[stateType, HoldComplete[type_] :> HoldComplete[type | Failure]]]
		},
		With[
			{
				step = statementsTerm[
					expandedStatements[testStatements],
					continuationEnding[Function[tested, Replace[
						{
							atomTerm[testValue, tested],
							statementsTerm[
								expandedStatements[bodyStatements],
								continuationEnding[Function[ended, callTerm[loop, stateTerms[ended]]]],
								tested, context, signatures
							],
							tupleTerm[stateTerms[tested]],
							stateType
						},
						{
							{{HoldComplete[b_], "Boolean"}, HoldComplete[continue_], HoldComplete[tuple_], HoldComplete[type_]} :> HoldComplete["machineIf"[b, continue, Typed["left"[tuple], type | Failure]]],
							_ :> unmodeled["a While whose test is no Boolean"]
						}
					]]],
					inner, context, signatures
				],
				outOfFuel = Replace[stateType, HoldComplete[type_] :> HoldComplete[Typed["right"[Failure["OutOfFuel", <||>]], type | Failure]]]
			},
			definitionDeclaration[
				HoldComplete[name],
				functionTerm[
					Join[budgets, readBinders, stateBinders],
					Replace[
						{fuel, fuelLeft, loop, roundType, functionTerm[stateBinders, outOfFuel], functionTerm[stateBinders, step], callTerm[HoldComplete[Null], Map[First, stateBinders]]},
						{HoldComplete[f_], HoldComplete[g_], HoldComplete[l_], HoldComplete[type_], HoldComplete[none_], HoldComplete[round_], HoldComplete[Null[arguments___]]} :>
							HoldComplete[InductiveRecursor[NonNegativeIntegers][
								Function[{Typed[WolframInstitute`TypeTheory`Compiled`j, NonNegativeIntegers]}, type],
								none,
								Function[{Typed[g, NonNegativeIntegers], Typed[l, type]}, round],
								f
							][arguments]]
					]
				],
				functionType[Join[Map[Last, budgets], Map[Last, readBinders], Map[Last, stateBinders]], Replace[stateType, HoldComplete[type_] :> HoldComplete[type | Failure]]]
			]
		]
	]
]

(* a state of several locals is a pair of the first and the state of the others *)
tupleTerm[{term_HoldComplete}] := term
tupleTerm[{HoldComplete[first_], rest__}] := Replace[tupleTerm[{rest}], HoldComplete[others_] :> HoldComplete["pair"[first, others]]]

tupleType[{type_HoldComplete}] := type
tupleType[{HoldComplete[first_], rest__}] := Replace[tupleType[{rest}], HoldComplete[others_] :> HoldComplete[CartesianProductType[first, others]]]

projectionTerms[state_HoldComplete, 1] := {state}
projectionTerms[HoldComplete[state_], count_Integer] := Prepend[projectionTerms[HoldComplete[state[["second"]]], count - 1], HoldComplete[state[["first"]]]]

(* a call of more than two numbers is the pairwise steps the C takes, each a temporary of its own; a call of a function
   takes machine integers, so a constant argument is first made one *)
expandedStatements[statements_List] := Catenate[Map[expandedStatement, statements]]

expandedStatement[coreForm["SetTemporary"][t_String, coreForm["Call"][operation : "System`Plus" | "System`Times", {first_, second_, more__}]]] :=
	expandedPairwise[t, operation, first, {second, more}]
(* a constant argument of a call of another function is first a machine integer of its own, bound as a step *)
expandedStatement[coreForm["SetTemporary"][t_String, coreForm["Call"][name_String, arguments_List]]] /;
	! StringStartsQ[name, "System`"] && ! FreeQ[arguments, coreForm["Constant"][_Integer]] :=
	With[{constants = MapIndexed[Function[{argument, position}, If[MatchQ[argument, coreForm["Constant"][_Integer]], {StringJoin[t, "c", ToString[First[position]]], argument}, None]], arguments]},
		Append[
			Map[Function[constant, coreForm["SetTemporary"][First[constant], Last[constant]]], DeleteCases[constants, None]],
			coreForm["SetTemporary"][t, coreForm["Call"][name, MapThread[Function[{argument, constant}, If[constant === None, argument, coreForm["Temporary"][First[constant]]]], {arguments, constants}]]]
		]
	]
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
		{HoldComplete[x_], HoldComplete[y_]} /; operation === "System`Plus" :> {"Result", HoldComplete["machinePlus"[x, y]], "Integer64"},
		{HoldComplete[x_], HoldComplete[y_]} :> {"Result", HoldComplete["machineTimes"[x, y]], "Integer64"}
	}]
stepTerm[coreForm["Call"][operation : "System`Quotient" | "System`Mod", {a_, b_}], scope_, _, _] :=
	Replace[{integerTerm[atomTerm[a, scope]], integerTerm[atomTerm[b, scope]]}, {
		{HoldComplete[x_], HoldComplete[y_]} /; operation === "System`Quotient" :> {"Result", HoldComplete["machineQuotient"[x, y]], "Integer64"},
		{HoldComplete[x_], HoldComplete[y_]} :> {"Result", HoldComplete["machineMod"[x, y]], "Integer64"}
	}]
stepTerm[coreForm["Constant"][value_Integer], _, _, _] := {"Result", HoldComplete["machineResult"[value]], "Integer64"}
stepTerm[coreForm["Call"][operation_String, {a_, b_}], scope_, _, _] /; KeyExistsQ[$machineComparisons, operation] :=
	{"Pure", $machineComparisons[operation][integerTerm[atomTerm[a, scope]], integerTerm[atomTerm[b, scope]]], "Boolean"}
stepTerm[coreForm["Call"]["System`Not", {a_}], scope_, _, _] :=
	Replace[atomTerm[a, scope], {{HoldComplete[b_], "Boolean"} :> {"Pure", HoldComplete["not"[b]], "Boolean"}, _ :> unmodeled["System`Not"]}]
(* a call of the function itself is its recursion, at a level less; a call of another function gives it this function's
   levels and fuel, where it takes them *)
stepTerm[coreForm["Call"][name_String, arguments_List], scope_, signature_, signatures_] /; KeyExistsQ[signatures, name] := With[
	{values = Map[Function[argument, machineTerm[atomTerm[argument, scope]]], arguments]},
	{
		"Result",
		Which[
			name === signature["Name"] && signature["Recursion"] === None,
				unmodeled["a call of the function itself in its loop"],
			name === signature["Name"],
				callTerm[signature["Recursion"], values],
			True,
				callTerm[ToExpression[name, InputForm, HoldComplete], Join[
					If[leveledQ[name, signatures], {budgetTerm[signature, "Levels"]}, {}],
					If[fueledQ[name, signatures], {budgetTerm[signature, "Fuel"]}, {}],
					values
				]]
		],
		signatures[name]["Result"]
	}
]

budgetTerm[signature_, key_String] := Replace[signature[key], None :> unmodeled[key]]
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
atomTerm[coreForm["Constant"][True], _] := {HoldComplete["true"], "Boolean"}
atomTerm[coreForm["Constant"][False], _] := {HoldComplete["false"], "Boolean"}
atomTerm[other_, _] := unmodeled[other]

(* the exact integer of a machine integer or a constant *)
integerTerm[{HoldComplete[x_], "Integer64"}] := HoldComplete[x[["integer"]]]
integerTerm[{term_HoldComplete, "Integer"}] := term
integerTerm[{_, kind_}] := unmodeled[kind]

(* a machine integer or a Boolean as a value; a constant was bound as a machine integer before the call *)
machineTerm[{term_HoldComplete, "Integer64" | "Boolean"}] := term
machineTerm[{_, kind_}] := unmodeled[kind]

(* the block's value as a result: a machine integer or a Boolean that never left, or a constant's machine result *)
valueTerm[{HoldComplete[x_], "Integer64"}, "Integer64"] := HoldComplete[Typed["left"[x], "Integer64" | Failure]]
valueTerm[{HoldComplete[x_], "Boolean"}, "Boolean"] := HoldComplete[Typed["left"[x], "Boolean" | Failure]]
valueTerm[{HoldComplete[x_], "Integer"}, "Integer64"] := HoldComplete["machineResult"[x]]
valueTerm[{_, kind_}, result_] := unmodeled[{kind, result}]

unmodeled[form_] := kernelFailure["UnmodeledOperation", "The typed code has `1`, which the machine model does not have yet.", {Short[form, 2]}]
