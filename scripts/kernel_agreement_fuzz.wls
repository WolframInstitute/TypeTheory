#!/usr/bin/env wolframscript
(* ::Package:: *)

(* The two kernels on records changed one at a time (scripts/kernel_agreement.wl). An environment of the prelude with a
   few declarations has one record or its registration of the natural numbers changed, and TypeTheoryCheck checks it
   with Method Automatic and with Method -> "Symbolic": both accept each change, or both refuse it. A change that one
   accepts and the other refuses is printed, and the script exits with status 1.

       wolframscript -f scripts/kernel_agreement_fuzz.wls [count] [seed]

   The changes are drawn with SeedRandom[seed], 1,000 of them with the seed 20261112 by default, so a run is repeated
   by its two numbers. *)

PacletDirectoryLoad[FileNameJoin[{ParentDirectory[DirectoryName[$InputFileName]], "TypeTheory"}]]

Needs["WolframInstitute`TypeTheory`"]

Get[FileNameJoin[{DirectoryName[$InputFileName], "kernel_agreement.wl"}]]

arguments = Rest[$ScriptCommandLine]
count = If[Length[arguments] >= 1, ToExpression[First[arguments]], 1000]
seed = If[Length[arguments] >= 2, ToExpression[Extract[arguments, 2]], 20261112]

environment = TypeTheoryEnvironment[TypeTheoryEnvironment["Prelude"], {
	TypeTheoryAxiom["assumed", 1 + 1 == 2],
	TypeTheoryAxiom["falsehood", 2 + 2 == 5],
	TypeTheoryDefinition["two", Typed[2, NonNegativeIntegers]],
	TypeTheoryTheorem["honest", 2 + 2 == 4, "equalityReflexivity"[4]],
	TypeTheoryDefinition["secret", Typed[5, NonNegativeIntegers], "Opaque" -> True],
	TypeTheoryTheorem["usesTwo", "two" == 2, "equalityReflexivity"[2]]
}, Method -> "Symbolic"]

Print["TypeTheory ", PacletObject["WolframInstitute/TypeTheory"]["Version"], "; ", Length[environment], " records; ", count, " changes, seed ", seed, "; the compiled kernel ",
	If[Symbol["WolframInstitute`TypeTheory`PackageScope`compiledKernelAvailableQ"][], "has its library", "has no library: both methods are the kernel of TypeChecking.wl"]]

results = KernelAgreement`kernelAgreement[environment, count, seed]

Print["by kind of record: ", KeySort[Counts[Lookup[results, "Kind"]]]]
Print["changes that left the environment as it was: ", Count[results, KeyValuePattern["Unchanged" -> True]]]
Print["by the two verdicts' classes (Automatic, Symbolic): ", KeySort[Counts[Function[result, KernelAgreement`agreementClass /@ Lookup[result, {"Automatic", "Symbolic"}]] /@ results]]]
Print["by the two tags: ", Reverse[SortBy[Normal[Counts[Function[result, Lookup[result, {"Automatic", "Symbolic"}]] /@ results]], Last]]]

disagreements = KernelAgreement`agreementDisagreements[results]
Print["disagreements: ", Length[disagreements]]
Scan[Function[result, Print["  ", result["Kind"], " ", result["Name"], ", ", result["Change"], ": Automatic ", result["Automatic"], ", Symbolic ", result["Symbolic"]]], disagreements]

Exit[If[disagreements === {}, 0, 1]]
