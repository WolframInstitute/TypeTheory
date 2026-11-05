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
