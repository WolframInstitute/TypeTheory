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
		bothKernels[forge[prelude, HoldComplete["falseElimination"], Function[record, Append[record, "Type" -> constantReference[HoldComplete[False], {}]]]]],
		bothKernels[forge[prelude, HoldComplete["additionZeroLeft"], Function[record, Append[record, "Value" -> naturalLiteral[0]]]]]
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
   says so, and Automatic gives the answer of the kernel of TypeChecking.wl. The two kernels name three refusals
   differently, a loose bound variable in a constructor's type, in a recursor's type and in a recursor's rule: the
   compiled kernel checks the terms of the records before the inductive types are declared again, and the other
   kernel declares them again first.

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

mismatches[loose_String] := With[{declined = "CompiledKernelUnavailable", mismatch = "DeclarationMismatch"},
	{
		{mismatch, declined, mismatch},
		{mismatch, declined, mismatch},
		{mismatch, declined, mismatch},
		{mismatch, declined, mismatch},
		{loose, loose, mismatch},
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
			mismatches["LooseBoundVariable"],
			mismatches["LooseBoundVariable"]
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
		Function[value, {"an axiom's value", value} -> with["Constants", ReplacePart[constants, {axiom, 3} -> value]]] /@ {-1, nodeCount + 1},
		{{"a given definition's value", 0} -> Append[with["Constants", ReplacePart[constants, {definition, 3} -> 0]], "Order" -> Developer`ToPackedArray[order /. definition -> -definition]]},
		Function[value, {"a constant's universe parameters", value} -> with["Constants", ReplacePart[constants, {theorem, 4} -> value]]] /@ {0, levelCount + 1},
		Function[value, {"a constant's kind", value} -> with["Constants", ReplacePart[constants, {theorem, 1} -> value]]] /@ {0, 10},
		Function[value, {"a rule's right-hand side", value} -> with["Flat", ReplacePart[flat, ruleStart + 3 -> value]]] /@ {0, 5, -(nodeCount + 1)},
		Function[value, {"a rule's constructor", value} -> with["Flat", ReplacePart[flat, ruleStart -> value]]] /@ {0, constantCount + 1},
		{{"a recursor's rules start", flatCount} -> with["Constants", ReplacePart[constants, {recursor, 16} -> flatCount]]},
		Function[value, {"a recursor's type", value} -> with["Constants", ReplacePart[constants, {recursor, 8} -> value]]] /@ {0, constantCount + 1},
		Function[value, {"an inductive type's constructor", value} -> with["Flat", ReplacePart[flat, constructorStart -> value]]] /@ {0, constantCount + 1},
		Function[value, {"an entry of the order", value} -> with["Order", ReplacePart[order, 5 -> value]]] /@ {0, constantCount + 1, -(constantCount + 1)},
		{{"the natural numbers' type", constantCount + 1} -> with["Settings", ReplacePart[settings, 4 -> constantCount + 1]]},
		{{"a negative entry of the flat table", -(nodeCount + 1)} -> with["Flat", ReplacePart[flat, flatCount -> -(nodeCount + 1)]]},
		{{"the nodes", "no packed array"} -> Append[input, "Nodes" -> Developer`FromPackedArray[input["Nodes"]]]}
	]
]

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
			If[available, check[givenWithoutValue[input, HoldComplete["honest"]]], "accepted"]
		}
	],
	{True, "accepted", 64, {}, True, "accepted"},
	TestID -> "The-compiled-program-is-not-run-on-an-input-with-a-reference-that-is-none"
]

(* a definition's height and hint are the kernel's to give: the compiled kernel works them out from the value too *)
VerificationTest[
	{
		bothKernels[forge[prelude, HoldComplete[Plus], Function[record, Append[record, "Height" -> 7]]]],
		bothKernels[forge[prelude, HoldComplete[Plus], Function[record, Append[record, "Hint" -> "Abbreviation"]]]]
	},
	{{"DeclarationMismatch", "DeclarationMismatch"}, {"DeclarationMismatch", "DeclarationMismatch"}},
	TestID -> "Both-kernels-catch-a-forged-height-and-hint"
]

(* the compiled kernel takes a recursor as it is, and the inductive types are declared again after it *)
VerificationTest[
	bothKernels[forge[prelude, HoldComplete[InductiveRecursor[Or]], Function[record, Append[record, "EliminationUniverse" -> True]]]],
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
