(* ::Package:: *)

(* Tests for Checking/CompiledKernel.wl: the compiled kernel, with which TypeTheoryCheck checks an environment, and
   which checks a list of declarations at once with Method -> "Compiled". It is the algorithm of TypeChecking.wl, so
   each test asks both kernels and expects the same answer. Where the paclet has no library for this platform and
   version (scripts/compile_kernel.wls builds it), Method -> "Compiled" is answered by the kernel of TypeChecking.wl
   in these tests. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

available = WolframInstitute`TypeTheory`PackageScope`compiledKernelAvailableQ[]

compiledMethod = If[available, "Compiled", "Symbolic"]

constantReference = Symbol["WolframInstitute`TypeTheory`PackageScope`constantReference"]
naturalLiteral = Symbol["WolframInstitute`TypeTheory`PackageScope`naturalLiteral"]

(* a copy of the environment's store with one record changed by hand *)
forge[TypeTheoryEnvironment[store_Symbol], name_HoldComplete, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy["Records"] = MapAt[change, copy["Records"], Key[name]];
	TypeTheoryEnvironment[copy]
]

(* the tag TypeTheoryCheck gives with each kernel *)
bothKernels[environment_] := {First @ TypeTheoryCheck[environment, Method -> "Symbolic"], First @ TypeTheoryCheck[environment, Method -> compiledMethod]}


VerificationTest[
	bothKernels /@ {prelude, TypeTheoryEnvironment["Integers"], TypeTheoryEnvironment["Rationals"]},
	ConstantArray[{"EnvironmentChecked", "EnvironmentChecked"}, 3],
	TestID -> "Both-kernels-check-the-library-environments"
]

VerificationTest[
	{
		bothKernels[forge[prelude, HoldComplete["falseElimination"], Function[record, Association[record, "Type" -> constantReference[HoldComplete[False], {}]]]]],
		bothKernels[forge[prelude, HoldComplete["additionZeroLeft"], Function[record, Association[record, "Value" -> naturalLiteral[0]]]]]
	},
	{{"TypeMismatch", "TypeMismatch"}, {"TypeMismatch", "TypeMismatch"}},
	TestID -> "Both-kernels-catch-a-forged-statement-and-a-forged-proof"
]

(* The matrix of forged records. From 0.16.0 to 0.42.1 TypeTheoryCheck accepted a record of a theorem, an opaque
   constant or a definition without its value: the compiled program takes 0 for no value and then checks nothing of the
   constant, so a theorem without a proof was declared, of a falsehood as well. Here each kind of record has each of
   its fields that holds a term forged in each way: the field absent, a number in its place, a part of it that is no
   term, a loose bound variable, a constant that is not declared, and another term that is well formed. Every forgery
   is refused by Automatic, by "Compiled" and by "Symbolic", but one that is none: an axiom with another well-formed
   statement is another axiom. Where the compiled kernel does not take the environment, asked for it alone the check
   says so, and Automatic gives the answer of the kernel of TypeChecking.wl. A record that an inductive type's
   declaration makes and the compiled kernel refuses is compared with the one made first, as the kernel of
   TypeChecking.wl compares it, so a recursor's type or rule with a loose bound variable is a mismatch to every method.
   The two kernels name one refusal differently, a loose bound variable in a constructor's type, which the compiled
   kernel refuses as a constructor whose parameters do not match.

   A value is replaced in its place: Append would move its key to the end, and records are compared with the order of
   their keys, so a record with nothing wrong but that order is a mismatch to the kernel of TypeChecking.wl. *)
application = Symbol["WolframInstitute`TypeTheory`PackageScope`application"]
boundVariable = Symbol["WolframInstitute`TypeTheory`PackageScope`boundVariable"]

matrixEnvironment = TypeTheoryEnvironment[prelude, {
	TypeTheoryAxiom["assumed", 1 + 1 == 2],
	TypeTheoryAxiom["falsehood", 2 + 2 == 5],
	TypeTheoryDefinition["two", Typed[2, NonNegativeIntegers]],
	TypeTheoryTheorem["honest", 2 + 2 == 4, "equalityReflexivity"[4]],
	TypeTheoryDefinition["secret", Typed[5, NonNegativeIntegers], "Opaque" -> True],
	TypeTheoryTheorem["usesTwo", "two" == 2, "equalityReflexivity"[2]]
}, Method -> "Symbolic"]

matrixRecords = First[matrixEnvironment]["Records"]

(* the forgeries of a field that holds a term, each a function of the term the record has, or None for the field absent *)
termForgeries[wrong_] := {
	None,
	Function[old, 0],
	Function[old, -1],
	Function[old, application[old, 0]],
	Function[old, boundVariable[7]],
	Function[old, constantReference[HoldComplete["nowhere"], {}]],
	Function[old, wrong]
}

fieldForged[field_String, None] := Function[record, KeyDrop[record, field]]
fieldForged[field_String, change_] := Function[record, Association[record, field -> change[record[field]]]]

(* the right-hand side of a recursor's first rule *)
ruleForged[None] := Function[record, Association[record, "Rules" -> MapAt[Function[rule, KeyDrop[rule, "RightHandSide"]], record["Rules"], 1]]]
ruleForged[change_] := Function[record, Association[record, "Rules" -> MapAt[Function[rule, Association[rule, "RightHandSide" -> change[rule["RightHandSide"]]]], record["Rules"], 1]]]

(* the tags of TypeTheoryCheck by Automatic, by the compiled kernel alone and by the kernel of TypeChecking.wl *)
threeMethods[environment_] := Function[method, First @ TypeTheoryCheck[environment, Method -> method]] /@ {Automatic, compiledMethod, "Symbolic"}

matrixRow[name_HoldComplete, field_String, wrong_] := Function[change,
	threeMethods[forge[matrixEnvironment, name, If[field === "Rule", ruleForged[change], fieldForged[field, change]]]]
] /@ termForgeries[wrong]

(* what a row of the matrix gives where the compiled kernel has its library: the compiled kernel does not take a record
   whose field is absent, a number, has a part that is no term or names an undeclared constant, and it refuses a loose
   bound variable and a wrong term itself; without the library all three methods are the kernel of TypeChecking.wl *)
refusals[wrong_String] := refusals[wrong, "LooseBoundVariable", "LooseBoundVariable"]
refusals[wrong_String, looseCompiled_String, looseSymbolic_String] := With[{declined = "CompiledKernelUnavailable"},
	{
		{"IllFormedTerm", declined, "IllFormedTerm"},
		{"IllFormedTerm", declined, "IllFormedTerm"},
		{"IllFormedTerm", declined, "IllFormedTerm"},
		{"FunctionExpected", declined, "FunctionExpected"},
		{looseCompiled, looseCompiled, looseSymbolic},
		{"UnknownConstant", declined, "UnknownConstant"},
		{wrong, wrong, wrong}
	}
]

mismatches[] := With[{declined = "CompiledKernelUnavailable", mismatch = "DeclarationMismatch"},
	{
		{mismatch, declined, mismatch},
		{mismatch, declined, mismatch},
		{mismatch, declined, mismatch},
		{mismatch, declined, mismatch},
		{mismatch, mismatch, mismatch},
		{mismatch, declined, mismatch},
		{mismatch, mismatch, mismatch}
	}
]

withoutLibrary[rows_List] := Map[Function[cell, ConstantArray[Last[cell], 3]], rows, {2}]

VerificationTest[
	With[
		{
			falsehood = matrixRecords[HoldComplete["falsehood"]]["Type"],
			false = constantReference[HoldComplete[False], {}],
			constructor = First[matrixRecords[HoldComplete[Or]]["Constructors"]]
		},
		{
			threeMethods[matrixEnvironment],
			matrixRow[HoldComplete["assumed"], "Type", falsehood],
			matrixRow[HoldComplete["two"], "Type", false],
			matrixRow[HoldComplete["two"], "Value", naturalLiteral[3]],
			matrixRow[HoldComplete["honest"], "Type", falsehood],
			matrixRow[HoldComplete["honest"], "Value", naturalLiteral[0]],
			matrixRow[HoldComplete["secret"], "Type", false],
			matrixRow[HoldComplete["secret"], "Value", false],
			matrixRow[HoldComplete[Or], "Type", false],
			matrixRow[constructor, "Type", false],
			matrixRow[HoldComplete[InductiveRecursor[Or]], "Type", false],
			matrixRow[HoldComplete[InductiveRecursor[Or]], "Rule", naturalLiteral[0]]
		}
	],
	Prepend[
		If[available, Identity, withoutLibrary][{
			refusals["EnvironmentChecked"],
			refusals["TypeMismatch"],
			refusals["TypeMismatch"],
			refusals["TypeMismatch"],
			refusals["TypeMismatch"],
			refusals["TypeMismatch"],
			refusals["TypeMismatch"],
			refusals["InductiveParameters"],
			refusals["ConstructorParameters", "ConstructorParameters", "LooseBoundVariable"],
			mismatches[],
			mismatches[]
		}],
		{"EnvironmentChecked", "EnvironmentChecked", "EnvironmentChecked"}
	],
	TimeConstraint -> 3600,
	TestID -> "Every-forged-field-of-every-kind-of-record-is-refused-by-the-three-methods"
]

(* The rows of an input forged one reference at a time. The compiled program is run only on an input that programInputQ
   takes, at the one place that calls it: a part of a term that is 0, negative, past the end, the term itself or a row
   after it, a constant or a level that is none, an unknown tag or kind, a type, a value or universe parameters that
   are no rows, a rule with no right-hand side or no constructor, an entry of the order or of the flat table out of
   range, each is answered None without the program, for which the other kernel checks the environment. A theorem that
   the order takes as given may have no value, and is the one row with a 0 that goes to the program. *)
compiledPrivate[name_String] := Symbol["WolframInstitute`TypeTheory`Checking`CompiledKernel`Private`" <> name]

forgedInputs[input_] := Module[
	{
		nodes = Normal[input["Nodes"]], levels = Normal[input["Levels"]], constants = Normal[input["Constants"]], flat = Normal[input["Flat"]], order = Normal[input["Order"]],
		settings = Normal[input["Settings"]], with, at, last, first, nodeCount, levelCount, constantCount, flatCount, applied, named, sort, projected, variable, successor, pair,
		theorem, definition, axiom, recursor, inductive, ruleStart, constructorStart
	},
	{nodeCount, levelCount, constantCount, flatCount} = Length /@ {nodes, levels, constants, flat};
	with[key_String, value_] := Append[input, key -> Developer`ToPackedArray[value]];
	at[name_] := First[FirstPosition[input["Names"], name]];
	last[rows_, tag_] := Last[Flatten[Position[rows[[All, 1]], tag]]];
	first[rows_, tag_] := First[Flatten[Position[rows[[All, 1]], tag]]];
	applied = last[nodes, 4]; named = last[nodes, 3]; sort = last[nodes, 2]; projected = last[nodes, 9]; variable = first[nodes, 1];
	successor = first[levels, 3]; pair = first[levels, 6];
	theorem = at[HoldComplete["honest"]]; definition = at[HoldComplete["two"]]; axiom = at[HoldComplete["assumed"]];
	recursor = at[HoldComplete[InductiveRecursor[Or]]]; inductive = at[HoldComplete[Or]];
	ruleStart = constants[[recursor, 16]]; constructorStart = constants[[inductive, 11]];
	Join[
		Function[value, {"an application's function", value} -> with["Nodes", ReplacePart[nodes, {applied, 2} -> value]]] /@ {0, -1, nodeCount + 1, applied, applied + 1},
		Function[value, {"an application's argument", value} -> with["Nodes", ReplacePart[nodes, {applied, 3} -> value]]] /@ {0, -1, nodeCount + 1},
		Function[value, {"a constant's number", value} -> with["Nodes", ReplacePart[nodes, {named, 2} -> value]]] /@ {0, -1, constantCount + 1},
		Function[value, {"a constant's levels", value} -> with["Nodes", ReplacePart[nodes, {named, 3} -> value]]] /@ {0, -1, levelCount + 1},
		Function[value, {"a sort's level", value} -> with["Nodes", ReplacePart[nodes, {sort, 2} -> value]]] /@ {0, -1, levelCount + 1},
		Function[value, {"a node's tag", value} -> with["Nodes", ReplacePart[nodes, {applied, 1} -> value]]] /@ {0, -1, 10, 12},
		Function[value, {"a projection's term", value} -> with["Nodes", ReplacePart[nodes, {projected, 4} -> value]]] /@ {0, nodeCount + 1},
		Function[value, {"a projection's structure", value} -> with["Nodes", ReplacePart[nodes, {projected, 2} -> value]]] /@ {0, constantCount + 1},
		{{"a bound variable's index", -1} -> with["Nodes", ReplacePart[nodes, {variable, 2} -> -1]]},
		Function[value, {"a level successor's level", value} -> with["Levels", ReplacePart[levels, {successor, 2} -> value]]] /@ {0, levelCount + 1, successor},
		Function[value, {"a list of levels' rest", value} -> with["Levels", ReplacePart[levels, {pair, 3} -> value]]] /@ {0, levelCount + 1},
		{{"a level's tag", 9} -> with["Levels", ReplacePart[levels, {1, 1} -> 9]]},
		Function[value, {"a theorem's type", value} -> with["Constants", ReplacePart[constants, {theorem, 2} -> value]]] /@ {0, -1, nodeCount + 1},
		Function[value, {"a theorem's value", value} -> with["Constants", ReplacePart[constants, {theorem, 3} -> value]]] /@ {0, -1, nodeCount + 1},
		Function[value, {"a definition's value", value} -> with["Constants", ReplacePart[constants, {definition, 3} -> value]]] /@ {0, -1, nodeCount + 1},
		Function[value, {"an axiom's value", value} -> with["Constants", ReplacePart[constants, {axiom, 3} -> value]]] /@ {-1, 1, nodeCount + 1},
		{{"a given definition's value", 0} -> Append[with["Constants", ReplacePart[constants, {definition, 3} -> 0]], "Order" -> Developer`ToPackedArray[order /. definition -> -definition]]},
		Function[value, {"a constant's universe parameters", value} -> with["Constants", ReplacePart[constants, {theorem, 4} -> value]]] /@ {0, levelCount + 1},
		Function[value, {"a constant's kind", value} -> with["Constants", ReplacePart[constants, {theorem, 1} -> value]]] /@ {0, 10},
		Function[value, {"a rule's right-hand side", value} -> with["Flat", ReplacePart[flat, ruleStart + 3 -> value]]] /@ {0, 5, -(nodeCount + 1)},
		Function[value, {"a rule's constructor", value} -> with["Flat", ReplacePart[flat, ruleStart -> value]]] /@ {0, constantCount + 1},
		{{"a recursor's rules start", flatCount} -> with["Constants", ReplacePart[constants, {recursor, 16} -> flatCount]]},
		Function[value, {"a recursor's type", value} -> with["Constants", ReplacePart[constants, {recursor, 8} -> value]]] /@ {0, constantCount + 1},
		Function[value, {"an inductive type's constructor", value} -> with["Flat", ReplacePart[flat, constructorStart -> value]]] /@ {0, constantCount + 1},
		Function[value, {"an entry of the order", value} -> with["Order", ReplacePart[order, 5 -> value]]] /@ {0, constantCount + 1, -(constantCount + 1)},
		(* a constant named twice, and so another left out, which would be neither checked nor declared *)
		{{"an entry of the order", "the entry after it"} -> with["Order", ReplacePart[order, 5 -> Extract[order, 6]]]},
		{{"the mark at the end of the flat table", 1} -> with["Flat", ReplacePart[flat, flatCount -> 1]]},
		{{"the natural numbers' type", constantCount + 1} -> with["Settings", ReplacePart[settings, 4 -> constantCount + 1]]},
		{{"a negative entry of the flat table", -(nodeCount + 1)} -> with["Flat", ReplacePart[flat, flatCount -> -(nodeCount + 1)]]},
		(* a field that the kind of a row does not use *)
		{
			{"an application's third number", 1} -> with["Nodes", ReplacePart[nodes, {applied, 4} -> 1]],
			{"a constant's third number", 1} -> with["Nodes", ReplacePart[nodes, {named, 4} -> 1]],
			{"a bound variable's second number", 1} -> with["Nodes", ReplacePart[nodes, {variable, 3} -> 1]],
			{"a sort's second number", 1} -> with["Nodes", ReplacePart[nodes, {sort, 3} -> 1]],
			{"a level number's second number", 1} -> with["Levels", ReplacePart[levels, {first[levels, 1], 3} -> 1]],
			{"a theorem's height", 1} -> with["Constants", ReplacePart[constants, {theorem, 6} -> 1]],
			{"a theorem's column of an inductive type", 1} -> with["Constants", ReplacePart[constants, {theorem, 9} -> 1]],
			{"a theorem's mark as declared", 1} -> with["Constants", ReplacePart[constants, {theorem, 20} -> 1]],
			{"a Boolean of a constant that compares nothing", 1} -> with["Constants", ReplacePart[constants, {theorem, 18} -> 1]],
			{"a recursor's flag", 2} -> with["Constants", ReplacePart[constants, {recursor, 13} -> 2]]
		}
	]
]

(* the nodes as a list that is no packed array: the guard does not take it, and the compiled function packs it, so it
   is no forgery of what the program reads *)
unpackedInput[input_] := Append[input, "Nodes" -> Developer`FromPackedArray[input["Nodes"]]]

givenWithoutValue[input_, name_HoldComplete] := With[{position = First[FirstPosition[input["Names"], name]]},
	Append[input, {
		"Constants" -> Developer`ToPackedArray[ReplacePart[Normal[input["Constants"]], {position, 3} -> 0]],
		"Order" -> Developer`ToPackedArray[Normal[input["Order"]] /. position -> -position]
	}]
]

VerificationTest[
	With[
		{
			input = compiledPrivate["environmentInput"][matrixEnvironment, 0, 0, 1],
			guard = compiledPrivate["programInputQ"],
			check = Function[forged, Replace[compiledPrivate["compiledCheckWith"][compiledPrivate["compiledKernelFunction"][], forged, 1], _Success -> "accepted"]]
		},
		{
			guard[input],
			If[available, check[input], "accepted"],
			Length[forgedInputs[input]],
			DeleteCases[KeyValueMap[Function[{label, forged}, {label, guard[forged], check[forged]}], Association[forgedInputs[input]]], {_, False, None}],
			guard[givenWithoutValue[input, HoldComplete["honest"]]],
			If[available, check[givenWithoutValue[input, HoldComplete["honest"]]], "accepted"],
			{guard[unpackedInput[input]], check[unpackedInput[input]]}
		}
	],
	{True, "accepted", 76, {}, True, "accepted", {False, None}},
	TestID -> "The-compiled-program-is-not-run-on-an-input-with-a-reference-that-is-none"
]

(* The program's own refusals: the compiled function called with the six arrays, with no guard before it. Where the
   paclet has no library for this platform there is no program to call, and the tests say so by their values.

   Every forged input ends with a status: no node is a failure where it is first met, a declaration is refused where
   a column it needs is absent, a constant is declared only on a success that its check returns, and the loader reads
   every row as the guard does. So the guard is a second line, and the program does not rest on it. *)
programStatus[input_] := Replace[
	compiledPrivate["compiledKernelFunction"][][input["Nodes"], input["Levels"], input["Constants"], input["Flat"], input["Order"], input["Settings"]],
	{{status_Integer, ___} :> status, _ -> "declined"}
]

VerificationTest[
	If[ available,
		With[{input = compiledPrivate["environmentInput"][matrixEnvironment, 0, 0, 1]},
			{
				programStatus[input],
				programStatus[givenWithoutValue[input, HoldComplete["honest"]]],
				Keys[Select[Association[Function[case, First[case] -> programStatus[Last[case]]] /@ forgedInputs[input]], Function[status, status === 0]]]
			}
		],
		{0, 0, {}}
	],
	{0, 0, {}},
	TestID -> "The-compiled-program-itself-refuses-each-forged-input"
]

(* Capacities too small for the pass, the nodes', the levels', the depth, the stack and the contexts', at 0 and at 1:
   each ends with a status and the kernel goes on. Settings 1, 2, 3, 10 and 11 hold them. *)
VerificationTest[
	If[ available,
		With[{input = compiledPrivate["environmentInput"][matrixEnvironment, 0, 0, 1]},
			Function[setting, Function[value, programStatus[Append[input, "Settings" -> Developer`ToPackedArray[ReplacePart[Normal[input["Settings"]], setting -> value]]]] =!= 0] /@ {0, 1}] /@ {1, 2, 3, 10, 11}
		],
		ConstantArray[True, {5, 2}]
	],
	ConstantArray[True, {5, 2}],
	TestID -> "A-capacity-too-small-ends-the-pass-with-a-status"
]

(* Single cells changed, 150 of them drawn with a seed from the nodes, the levels, the constants, the flat table and
   the order: the program accepts none that the guard refuses. What both take is another input and not a forgery of
   this one: an entry of the order made "given", which is the caller's statement, and a column of a generated record,
   which the replay of the inductive types refuses (the test of the two kernels on records, below). *)
cellChanged[input_] := With[{key = RandomChoice[{4, 1, 3, 1, 1} -> {"Nodes", "Levels", "Constants", "Flat", "Order"}]},
	With[{array = Normal[input[key]]},
		With[{position = If[ArrayDepth[array] == 2, {RandomInteger[{1, Length[array]}], RandomInteger[{1, Last[Dimensions[array]]}]}, {RandomInteger[{1, Length[array]}]}]},
			With[{old = Extract[array, position]},
				{key, position, old} -> Append[input, key -> Developer`ToPackedArray[ReplacePart[array, position -> RandomChoice[{0, -1, old + 1, old - 1, RandomInteger[{1, 300}], RandomInteger[{1, 6000}], 10^6, -old}]]]]
			]
		]
	]
]

VerificationTest[
	If[ available,
		With[{input = compiledPrivate["environmentInput"][matrixEnvironment, 0, 0, 1], guard = compiledPrivate["programInputQ"]},
			BlockRandom[
				SeedRandom[20261112];
				Cases[Table[cellChanged[input], {150}], (label_ -> changed_) /; ! guard[changed] && programStatus[changed] === 0 :> label]
			]
		],
		{}
	],
	{},
	TestID -> "The-compiled-program-accepts-no-changed-cell-that-the-guard-refuses"
]

(* a definition's height and hint are the kernel's to give: the compiled kernel works them out from the value too *)
VerificationTest[
	{
		bothKernels[forge[prelude, HoldComplete[Plus], Function[record, Association[record, "Height" -> 7]]]],
		bothKernels[forge[prelude, HoldComplete[Plus], Function[record, Association[record, "Hint" -> "Abbreviation"]]]]
	},
	{{"DeclarationMismatch", "DeclarationMismatch"}, {"DeclarationMismatch", "DeclarationMismatch"}},
	TestID -> "Both-kernels-catch-a-forged-height-and-hint"
]

(* the compiled kernel takes a recursor as it is, and the inductive types are declared again after it *)
VerificationTest[
	bothKernels[forge[prelude, HoldComplete[InductiveRecursor[Or]], Function[record, Association[record, "EliminationUniverse" -> True]]]],
	{"DeclarationMismatch", "DeclarationMismatch"},
	TestID -> "Both-kernels-catch-a-forged-recursor"
]

(* rules without Prop are not the compiled kernel's: TypeTheoryCheck checks with the other kernel, unless asked for this one *)
VerificationTest[
	With[{homotopy = TypeTheoryEnvironment["HomotopyTypeTheory"]},
		{First @ TypeTheoryCheck[homotopy], If[available, First @ TypeTheoryCheck[homotopy, Method -> "Compiled"], "CompiledKernelUnavailable"]}
	],
	{"EnvironmentChecked", "CompiledKernelUnavailable"},
	TestID -> "An-environment-the-compiled-kernel-does-not-handle-is-checked-by-the-other"
]

(* a literal from 2^62 on is not the compiled kernel's: the environment is checked by the other kernel *)
VerificationTest[
	First @ TypeTheoryCheck[Append[prelude, TypeTheoryTheorem[Large, 2^70 + 1 == 2^70 + 1, "equalityReflexivity"[2^70 + 1]]], Method -> Automatic],
	"EnvironmentChecked",
	TestID -> "A-literal-too-large-for-the-compiled-kernel-is-checked-by-the-other"
]

VerificationTest[
	With[
		{
			declarations = {
				TypeTheoryDefinition[Twice, Function[{Typed[n, NonNegativeIntegers]}, n + n]],
				TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]],
				TypeTheoryTheorem[TwiceTwo, Twice[2] == 4, "equalityReflexivity"[4]]
			}
		},
		With[{sequential = TypeTheoryEnvironment[prelude, declarations], batch = TypeTheoryEnvironment[prelude, declarations, Method -> compiledMethod]},
			{Keys[batch] === Keys[sequential], AllTrue[Keys[sequential], Function[name, First[batch]["Records"][HoldComplete @@ {name}] === First[sequential]["Records"][HoldComplete @@ {name}]]]}
		]
	],
	{True, True},
	TestID -> "A-batch-of-declarations-checked-at-once-gives-the-same-environment"
]

VerificationTest[
	With[{declarations = {TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]], TypeTheoryTheorem[TwoPlusTwoFive, 2 + 2 == 5, "equalityReflexivity"[4]]}},
		{First @ TypeTheoryEnvironment[prelude, declarations], First @ TypeTheoryEnvironment[prelude, declarations, Method -> compiledMethod]}
	],
	{"TypeMismatch", "TypeMismatch"},
	TestID -> "A-batch-with-a-declaration-that-does-not-check-fails-at-it"
]

(* inductive types in a batch: the compiled kernel checks that each constructor takes its type's parameters first and
   that its fields live in universes no larger than its type's *)
inductiveDeclarations = {
	TypeTheoryInductiveType[
		PolymorphicList,
		ForAll[{Typed[A, TypeUniverse[u + 1]]}, TypeUniverse[u + 1]],
		{
			PolymorphicEmpty -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, PolymorphicList[A]],
			PolymorphicCons -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[h, A], Typed[t, PolymorphicList[A]]}, PolymorphicList[A]]
		}
	],
	TypeTheoryInductiveType[
		NaturalVector,
		ForAll[{Typed[n, NonNegativeIntegers]}, TypeUniverse[1]],
		{VectorEmpty -> NaturalVector[0], VectorCons -> ForAll[{TypedImplicit[n, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[t, NaturalVector[n]]}, NaturalVector[n + 1]]}
	],
	TypeTheoryInductiveType[Box, TypeUniverse[2], {BoxIntroduction -> ForAll[{Typed[t, TypeUniverse[1]]}, Box]}]
}

VerificationTest[
	With[{sequential = TypeTheoryEnvironment[prelude, inductiveDeclarations], batch = TypeTheoryEnvironment[prelude, inductiveDeclarations, Method -> compiledMethod]},
		{Keys[batch] === Keys[sequential], First[batch]["Records"] === First[sequential]["Records"]}
	],
	{True, True},
	TestID -> "A-batch-of-inductive-types-gives-the-same-environment"
]

VerificationTest[
	With[{declarations = {TypeTheoryInductiveType[Big, TypeUniverse[1], {BigIntroduction -> ForAll[{Typed[t, TypeUniverse[1]]}, Big]}]}},
		{First @ TypeTheoryEnvironment[prelude, declarations], First @ TypeTheoryEnvironment[prelude, declarations, Method -> compiledMethod]}
	],
	{"UniverseTooLarge", "UniverseTooLarge"},
	TestID -> "A-batch-with-a-field-in-a-larger-universe-fails-at-it"
]

(* Box made a type of the smaller universe its field's type lives in, its record otherwise as it was, keys in order *)
VerificationTest[
	With[{boxes = Append[prelude, Last[inductiveDeclarations]], smaller = Append[prelude, TypeTheoryInductiveType[Box, TypeUniverse[1], {BoxIntroduction -> Box}]]},
		bothKernels[forge[boxes, HoldComplete[Box], Function[record, ReplacePart[record, Key["Type"] -> First[smaller]["Records"][HoldComplete[Box]]["Type"]]]]]
	],
	{"UniverseTooLarge", "UniverseTooLarge"},
	TestID -> "Both-kernels-catch-a-forged-universe-of-an-inductive-type"
]

(* A natural number literal of 2^62 or more is no row of the compiled kernel's. It is an opaque constant there, one for
   each distinct value, and a record that the compiled kernel then does not accept is checked by the kernel of
   TypeChecking.wl. Each case is a batch of declarations given as core terms, as an import gives them: a theorem
   left == right proved by the reflexivity of right, which holds where left computes to right. A case gives what the
   batch gives with the compiled kernel, the constants it left to the other kernel, and what the declarations give one
   at a time, which is the same verdict in every case. *)
application = Symbol["WolframInstitute`TypeTheory`PackageScope`application"]

literalBase = TypeTheoryEnvironment[prelude, {
	TypeTheoryDefinition["doubled", Function[{Typed[n, NonNegativeIntegers]}, n + n]],
	TypeTheoryDefinition["squared", Function[{Typed[n, NonNegativeIntegers]}, n n]],
	TypeTheoryDefinition["powerOfTwo", Function[{Typed[n, NonNegativeIntegers]}, 2^n]],
	TypeTheoryDefinition["difference", Function[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, n - k]]
}, Method -> "Symbolic"]

(* the statement is an axiom's type and the proof an honest theorem's value, taken from their records *)
SetAttributes[claim, HoldRest]
claim[name_String, left_, right_] := claimOver[literalBase, name, left, right]

(* the same over an environment that declares what the statement names *)
SetAttributes[claimOver, HoldRest]
claimOver[base_, name_String, left_, right_] := With[
	{records = First[TypeTheoryEnvironment[base, {
		TypeTheoryAxiom["claimed", left == right],
		TypeTheoryTheorem["honest", right == right, "equalityReflexivity"[right]]
	}, Method -> "Symbolic"]]["Records"]},
	TypeTheoryTheorem[name, #1, #2, "UniverseParameters" -> {}] &[records[HoldComplete["claimed"]]["Type"], records[HoldComplete["honest"]]["Value"]]
]

SetAttributes[namedNumber, HoldRest]
namedNumber[name_String, value_] := With[
	{record = First[TypeTheoryEnvironment[literalBase, {TypeTheoryDefinition["defined", Typed[value, NonNegativeIntegers]]}, Method -> "Symbolic"]]["Records"][HoldComplete["defined"]]},
	TypeTheoryDefinition[name, Typed[#1, #2], "UniverseParameters" -> {}] &[record["Value"], record["Type"]]
]

literalVerdict[result_] := Which[FailureQ[result], First[result], Head[result] === TypeTheoryEnvironment, "accepted", True, result]

(* without a library for this platform the other kernel answers the batch, and no record is left to it *)
literalBatch[declarations_List] := With[{compiled = TypeTheoryEnvironment[literalBase, declarations, Method -> compiledMethod]},
	{
		literalVerdict[compiled],
		If[available, Function[name, First[name]] /@ WolframInstitute`TypeTheory`PackageScope`$recheckedConstants, "no library"],
		literalVerdict[TypeTheoryEnvironment[literalBase, declarations, Method -> "Symbolic"]]
	}
]

rechecked[names___String] := If[available, {names}, "no library"]

VerificationTest[
	With[{big = 2^64, other = 2^64 + 1},
		{
			literalBatch[{namedNumber["big", big], claim["t", "big", "big"]}],
			literalBatch[{claim["t", big, big]}],
			literalBatch[{claim["t", big, other]}]
		}
	],
	{{"accepted", rechecked[], "accepted"}, {"accepted", rechecked[], "accepted"}, {"TypeMismatch", rechecked["t"], "TypeMismatch"}},
	TestID -> "A-large-literal-is-an-opaque-constant-of-the-compiled-kernel-one-for-each-value"
]

VerificationTest[
	With[{big = 2^64, other = 2^64 + 1, limit = 2^62, half = 2^61, root = 2^32},
		{
			literalBatch[{claim["t", "squared"[root], big]}],
			literalBatch[{claim["t", "squared"[root], other]}],
			literalBatch[{claim["t", "doubled"[half], limit]}],
			literalBatch[{claim["t", "powerOfTwo"[64], big]}],
			literalBatch[{claim["t", "difference"[big, big], 0]}],
			literalBatch[{claim["t", "difference"[big, other], 1]}]
		}
	],
	{
		{"accepted", rechecked["t"], "accepted"},
		{"TypeMismatch", rechecked["t"], "TypeMismatch"},
		{"accepted", rechecked["t"], "accepted"},
		{"accepted", rechecked["t"], "accepted"},
		{"accepted", rechecked["t"], "accepted"},
		{"TypeMismatch", rechecked["t"], "TypeMismatch"}
	},
	TestID -> "A-record-that-needs-the-value-of-a-large-literal-is-checked-by-the-other-kernel"
]

(* A forged proof about a made-up constant past the limit is refused alike on both paths: the constant is 2^63, and the
   theorem says it is 2^63 + 1, with the reflexivity of 2^63 + 1 for its proof. The compiled kernel leaves the record
   undecided, the kernel of TypeChecking.wl refuses it, and the failure a batch reports is the one the declarations give
   one at a time, by its tag and by its message. *)
VerificationTest[
	With[{made = 2^63, wrong = 2^63 + 1},
		With[{withMade = TypeTheoryEnvironment[literalBase, {namedNumber["madeUp", made]}, Method -> "Symbolic"]},
			With[{declarations = {namedNumber["madeUp", made], claimOver[withMade, "forged", "madeUp", wrong]}},
				With[{compiled = TypeTheoryEnvironment[literalBase, declarations, Method -> compiledMethod]},
					With[{left = If[available, Function[name, First[name]] /@ WolframInstitute`TypeTheory`PackageScope`$recheckedConstants, "no library"]},
						With[{single = TypeTheoryEnvironment[literalBase, declarations, Method -> "Symbolic"]},
							{
								Head[withMade],
								literalVerdict[compiled],
								left,
								literalVerdict[single],
								FailureQ[compiled] && FailureQ[single] && ToString[compiled["Message"]] === ToString[single["Message"]]
							}
						]
					]
				]
			]
		]
	],
	{TypeTheoryEnvironment, "TypeMismatch", rechecked["forged"], "TypeMismatch", True},
	TestID -> "A-forged-proof-about-a-made-up-large-constant-is-refused-alike-on-both-paths"
]

(* The compiled kernel computes no literal past 2^62 and never wraps: 2^61 + 2^61, 2^31 2^31 and 2^62 are computed and
   are not 0; 2^62 - 1 doubled, 2^32 squared and 2^64 are past the limit, where 64 bits would give 0 or a small number.
   With a large literal in the batch such a record goes to the other kernel, and without one the whole batch does. *)
VerificationTest[
	With[{big = 2^64, half = 2^61, most = 2^62 - 1, root = 2^31, larger = 2^32},
		{
			literalBatch[{namedNumber["big", big], claim["t", "doubled"[half], 0]}],
			literalBatch[{namedNumber["big", big], claim["t", "doubled"[most], 0]}],
			literalBatch[{namedNumber["big", big], claim["t", "squared"[root], 0]}],
			literalBatch[{namedNumber["big", big], claim["t", "squared"[larger], 0]}],
			literalBatch[{namedNumber["big", big], claim["t", "powerOfTwo"[62], 0]}],
			literalBatch[{namedNumber["big", big], claim["t", "powerOfTwo"[64], 0]}],
			literalBatch[{namedNumber["big", big], claim["t", "difference"[3, 5], 1]}],
			literalBatch[{claim["t", "doubled"[half], 0]}],
			literalBatch[{claim["t", "squared"[larger], 0]}],
			literalBatch[{claim["t", "powerOfTwo"[64], 0]}],
			literalBatch[{claim["t", "difference"[3, 5], 1]}]
		}
	],
	Join[ConstantArray[{"TypeMismatch", rechecked["t"], "TypeMismatch"}, 7], ConstantArray[{"TypeMismatch", rechecked[], "TypeMismatch"}, 4]],
	TestID -> "The-compiled-kernel-does-not-wrap-a-literal-past-its-limit"
]

(* The other kernel is asked about a record only in an environment with a large literal: without one, a record the
   compiled kernel does not accept is refused by that, and a batch on which a literal passes the limit goes to the other
   kernel whole, as before. With one, the compiled kernel goes on after a record checked by the other kernel: a later
   theorem is accepted or refused on its own, and two records may be checked. *)
VerificationTest[
	With[{big = 2^64, root = 2^32, over = 2^61 + 1},
		{
			literalBatch[{claim["t", "doubled"[3], 6]}],
			literalBatch[{claim["t", "doubled"[3], 7]}],
			literalBatch[{claim["t", "difference"["doubled"[over], "doubled"[over]], 0]}],
			literalBatch[{claim["t", "squared"[root], big], claim["u", "doubled"[2], 4]}],
			literalBatch[{claim["t", "squared"[root], big], claim["u", "doubled"[2], 5]}],
			literalBatch[{claim["t", "squared"[root], big], claim["u", "powerOfTwo"[64], big], claim["v", "doubled"[2], 4]}]
		}
	],
	{
		{"accepted", rechecked[], "accepted"},
		{"TypeMismatch", rechecked[], "TypeMismatch"},
		{"accepted", rechecked[], "accepted"},
		{"accepted", rechecked["t"], "accepted"},
		{"TypeMismatch", rechecked["t", "u"], "TypeMismatch"},
		{"accepted", rechecked["t", "u"], "accepted"}
	},
	TestID -> "Only-an-environment-with-a-large-literal-has-records-checked-by-the-other-kernel"
]

(* Without a recheck the compiled kernel answers None where it leaves a record undecided, and the other kernel checks
   the environment. The rules of a recursor are checked after every declaration, which a pass that ends at an undecided
   record does not reach: with a recheck that accepts that record alone, a recursor before it whose rule is forged is
   still caught, where taking every constant before the record as it is would have let it pass. *)
VerificationTest[
	If[ ! available,
		{True, None, True},
		With[{big = 2^64, root = 2^32},
			{
				named = TypeTheoryEnvironment[literalBase, {namedNumber["big", big], claim["t", "big", "big"]}, Method -> "Symbolic"],
				valued = TypeTheoryEnvironment[literalBase, {claim["t", "squared"[root], big]}, Method -> "Symbolic"]
			},
			With[
				{
					check = WolframInstitute`TypeTheory`PackageScope`compiledKernelCheck,
					position = Length[valued],
					forged = forge[valued, HoldComplete[InductiveRecursor[Or]], Function[record,
						ReplacePart[record, {Key["Rules"], 1, Key["RightHandSide"]} -> application[naturalLiteral[0], naturalLiteral[0]]]
					]]
				},
				{
					MatchQ[check[named], _Success],
					check[valued],
					And[
						MatchQ[check[valued, 0, 0, Function[at, If[at === position, at, Failure["NotTheRecord", <|"Position" -> at|>]]]], _Success],
						FailureQ[check[forged, 0, 0, Function[at, If[at === position, at, Failure["NotTheRecord", <|"Position" -> at|>]]]]]
					]
				}
			]
		]
	],
	{True, None, True},
	TestID -> "An-undecided-record-without-a-recheck-is-None-and-a-recursor-before-it-stays-checked"
]


(* The seed an import gives, a table of terms with the rows their codes and parts make, is used only where each of its
   composite terms is the term its row describes. A theorem of 2 + 2 == 4 declared by the batch path at core level with
   the proof of 5 == 5 is refused under a seed that gives that proof the row of the proof of 4 == 4, as without a seed:
   a message names the seed's position that does not match, 5, and the records' terms are read instead. The honest
   theorem is taken under the honest seed, which passes. Where the paclet has no library there is no program to give
   the seed to, and the test gives the message the program's input gives. *)
seedMismatch = compiledPrivate["seedMismatch"]

VerificationTest[
	Module[{honest, record, proofOfFour, proofOfFive, function, literal, seedOf, declared},
		honest = TypeTheoryEnvironment[prelude, {TypeTheoryTheorem["honest", 2 + 2 == 4, "equalityReflexivity"[4]]}];
		record = First[honest]["Records"][HoldComplete["honest"]];
		proofOfFour = record["Value"];
		proofOfFive = proofOfFour /. naturalLiteral[4] -> naturalLiteral[5];
		function = First[proofOfFour];
		literal = Last[proofOfFour];
		seedOf[proof_] := <|
			"Terms" -> {First[function], Last[function], literal, function, proof},
			"Codes" -> {0, 0, 0, 4, 4},
			"Parts" -> {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {1, 2, 0}, {4, 3, 0}},
			"Starts" -> {1, 3},
			"Roots" -> {5}
		|>;
		(* the declaration holds its arguments, so the core terms are put in with With *)
		declared[proof_, seed_] := With[{statement = record["Type"]}, Block[{WolframInstitute`TypeTheory`PackageScope`$compiledKernelSeed = seed},
			Replace[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem["seeded", statement, proof, "UniverseParameters" -> {}]}, Method -> "Compiled"], {
				failure_Failure :> failure["Tag"],
				_ -> "accepted"
			}]
		]];
		If[! available, Message[WolframInstitute`TypeTheory`PackageScope`$compiledKernelSeed::mismatch, 5]];
		{
			declared[proofOfFive, None],
			declared[proofOfFive, seedOf[proofOfFive]],
			declared[proofOfFour, seedOf[proofOfFour]],
			seedMismatch[seedOf[proofOfFive]],
			seedMismatch[seedOf[proofOfFour]]
		}
	],
	{"TypeMismatch", "TypeMismatch", "accepted", 5, None},
	{WolframInstitute`TypeTheory`PackageScope`$compiledKernelSeed::mismatch},
	TestID -> "A-seed-whose-row-describes-another-term-is-named-and-not-used"
]


(* TypeTheoryCheck rechecks a record the compiled program leaves undecided, as the batch path does: the records before
   it are declared again as the replay declares them, each compared whole, and the record itself with every check of
   the kernel of TypeChecking.wl; the program then goes on after it. Each case gives TypeTheoryCheck's verdict, the
   constants rechecked, and the verdict of the kernel of TypeChecking.wl alone:
   - two records that need the value of a large literal, each rechecked, and the environment checked;
   - a forged proof just after an undecided record: the program leaves it undecided too, as it does every record it
     does not accept in an environment with a large literal, and its recheck refuses it;
   - a definition just before an undecided record with a flag turned, which the program does not read: the recheck
     declares it again and compares it whole, and refuses it. *)
recheckBase[declarations_List] := TypeTheoryEnvironment[literalBase, declarations, Method -> "Symbolic"]

recheckVerdict[result_] := If[MatchQ[result, _Success], "accepted", First[result]]

checkedAndRechecked[environment_] := {
	recheckVerdict[TypeTheoryCheck[environment]],
	If[available, Function[name, First[name]] /@ WolframInstitute`TypeTheory`PackageScope`$recheckedConstants, "no library"],
	recheckVerdict[TypeTheoryCheck[environment, Method -> "Symbolic"]]
}

VerificationTest[
	With[{big = 2^64, limit = 2^62, half = 2^61, root = 2^32},
		With[
			{
				honest = recheckBase[{claim["t", "squared"[root], big], claim["u", "doubled"[half], limit]}],
				after = recheckBase[{claim["t", "squared"[root], big], claim["w", "doubled"[2], 4]}],
				before = recheckBase[{namedNumber["v", 5], claim["t", "squared"[root], big]}]
			},
			{
				checkedAndRechecked[honest],
				(* w's proof made t's, a proof of another statement *)
				checkedAndRechecked[forge[after, HoldComplete["w"], Function[record, Association[record, "Value" -> First[after]["Records"][HoldComplete["t"]]["Value"]]]]],
				(* v's flag "Instance" turned off where a declaration gives none *)
				checkedAndRechecked[forge[before, HoldComplete["v"], Function[record, Association[record, "Instance" -> False]]]]
			}
		]
	],
	{
		{"accepted", rechecked["t", "u"], "accepted"},
		{"TypeMismatch", rechecked["t"], "TypeMismatch"},
		{"DeclarationMismatch", rechecked[], "DeclarationMismatch"}
	},
	TestID -> "TypeTheoryCheck-rechecks-a-record-left-undecided-and-the-records-on-both-sides-of-it"
]

(* What the rechecks declare is kept from one to the next, and leaves what declaring the records one at a time leaves:
   the store after the rechecks of t and u is the one the replay with full checks makes through u. *)
queriesPrivate[name_String] := Symbol["WolframInstitute`TypeTheory`Checking`Queries`Private`" <> name]

recheckStore[TypeTheoryEnvironment[store_Symbol]] := Function[key, store[key]] /@ {"Records", "Names", "NaturalNumbers", "RewriteRuleIndex", "OverloadIndex", "Library"}

VerificationTest[
	With[{environment = recheckBase[{claim["t", "squared"[2^32], 2^64], claim["u", "doubled"[2^61], 2^62]}]},
		With[
			{
				names = WolframInstitute`TypeTheory`PackageScope`environmentNames[environment],
				empty = WolframInstitute`TypeTheory`PackageScope`emptyEnvironmentOf[WolframInstitute`TypeTheory`PackageScope`environmentRules[environment]]
			},
			With[{t = First[FirstPosition[names, HoldComplete["t"]]], u = First[FirstPosition[names, HoldComplete["u"]]]},
				WolframInstitute`TypeTheory`PackageScope`withStoreCleanup[SameQ[
					recheckStore[queriesPrivate["recheckedPrefix"][environment, queriesPrivate["recheckedPrefix"][environment, empty, 0, t], t, u]],
					recheckStore[queriesPrivate["replayNames"][environment, Take[names, u], Function[{partial, name, record}, queriesPrivate["replayDeclaration"][environment, partial, name -> record]]]]
				]]
			]
		]
	],
	True,
	TestID -> "The-rechecks-leave-what-declaring-the-records-one-at-a-time-leaves"
]
