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

