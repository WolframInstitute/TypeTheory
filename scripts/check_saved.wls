#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Time TypeTheory's kernel alone on saved environments: each file is read, without checking, and then checked
   again from its declarations with TypeTheoryCheck, as lean4checker replays an environment, n times (3 by default).
   This is the checking half of an import, the half Lean's kernel does, and needs neither LeanLink nor Lean, so every
   engine that runs TypeTheory can time it; LeanLink's typetheory_benchmark.wls --save writes its Mathlib cones as
   such files.

       wl -f scripts/check_saved.wls file.wxf ... [--runs n] [--profile] [--method Compiled|Symbolic]

   --profile adds a run that times the kernel's main functions: calls, exclusive time without the profiled functions
   they call, and the inclusive time of their outermost calls, each less the instrumentation's own cost, measured
   first. The table gives the first check of each file, which fills the kernel's caches of the run, and the minimum
   and median of the n checks after it. *)

$RecursionLimit = 20000

$repositoryDirectory = ParentDirectory[DirectoryName[$InputFileName]]

PacletDirectoryLoad[FileNameJoin[{$repositoryDirectory, "TypeTheory"}]]

Needs["WolframInstitute`TypeTheory`"]

arguments = Rest[$ScriptCommandLine]

runs = Replace[SequencePosition[arguments, {"--runs", _}], {{{position_, _}, ___} :> ToExpression[arguments[[position + 1]]], _ -> 3}]

files = ExpandFileName /@ Select[arguments, StringEndsQ[".wxf"]]

profileQ = MemberQ[arguments, "--profile"]

method = Replace[SequencePosition[arguments, {"--method", _}], {{{position_, _}, ___} :> arguments[[position + 1]], _ -> Automatic}]

(* the kernel's functions that --profile times, by name in any of TypeTheory's contexts *)
$profiled = {
	"declareAxiom",
	"declareDefinition",
	"declareTheorem",
	"declareInductiveTypes",
	"inferType",
	"inferTypeOf",
	"spineType",
	"spineTypeFrom",
	"applicationType",
	"checkHasType",
	"lambdaType",
	"functionTypeSort",
	"constantType",
	"constantRecord",
	"projectionType",
	"weakHeadNormalForm",
	"reduceHead",
	"reducedHead",
	"reducedHeadWithoutUnfolding",
	"reduceConstant",
	"reduceRecursor",
	"reduceProjection",
	"unfoldedHead",
	"unfoldDefinition",
	"definitionallyEqualQ",
	"definitionallyEqualCases",
	"reducedEqualQ",
	"lazyDeltaEqualQ",
	"lazyDeltaStep",
	"argumentsEqualQ",
	"sameHeadArgumentsEqualQ",
	"spinesEqualQ",
	"normalFormsEqualQ",
	"proofIrrelevance",
	"propositionQ",
	"etaEqualQ",
	"structureEtaQ",
	"levelEquivalentQ",
	"instantiateBoundVariables",
	"instantiateUniverseParameters",
	"liftBoundVariables",
	"abstractFreeVariable",
	"looseBoundRange",
	"looseBoundRangeOf",
	"applicationSpine"
}

(* Every call of each profiled function is timed: its exclusive time, without the time of the profiled functions it
   calls, and the inclusive time of its outermost calls. The function's definitions move to another symbol, which the
   timed definition calls, so the calls it makes in turn are timed too. Functions that hold their arguments, and
   SubValues and UpValues, are left alone, so their time lands on their callers. *)
profiledSymbol[short_String] := SelectFirst[
	Names["WolframInstitute`TypeTheory`*`" <> short],
	Function[name, DownValues[name] =!= {} && FreeQ[Attributes[name], HoldAll | HoldFirst | HoldRest | HoldAllComplete]],
	None
]

$childSeconds = 0.

SetAttributes[timedCall, HoldRest]

timedCall[short_, call_] := With[
	{
		timed = WithCleanup[
			$calls[short] += 1;
			$nesting[short] += 1
			,
			Block[{$childSeconds = 0.},
				With[{inner = AbsoluteTiming[call]},
					$exclusive[short] += First[inner] - $childSeconds;
					inner
				]
			]
			,
			$nesting[short] -= 1
		]
	},
	$childSeconds += First[timed];
	If[$nesting[short] === 0, $outermost[short] += First[timed]];
	Last[timed]
]

instrument[short_String] := With[{name = profiledSymbol[short]},
	If[ StringQ[name],
		With[{function = Symbol[name], moved = Symbol["profiled`" <> short]},
			$calls[short] = 0;
			$nesting[short] = 0;
			$exclusive[short] = 0.;
			$outermost[short] = 0.;
			DownValues[moved] = Map[Function[rule, MapAt[Function[left, left /. function -> moved], rule, {1}]], DownValues[function]];
			DownValues[function] = {HoldPattern[function[parts___]] :> timedCall[short, moved[parts]]};
			True
		],
		False
	]
]

calibrationSeconds[] := Block[{$calls, $nesting, $exclusive, $outermost, $childSeconds = 0., trivial, n = 100000},
	$calls["trivial"] = 0;
	$nesting["trivial"] = 0;
	$exclusive["trivial"] = 0.;
	$outermost["trivial"] = 0.;
	trivial[x_] := x;
	With[{plain = First[AbsoluteTiming[Do[trivial[i], {i, n}]]], timed = First[AbsoluteTiming[Do[timedCall["trivial", trivial[i]], {i, n}]]]},
		(timed - plain) / n
	]
]

timedCheck[environment_] := With[{timed = AbsoluteTiming[TypeTheoryCheck[environment, Method -> method]]},
	If[! MatchQ[Last[timed], _Success], Print["FATAL: the check failed: ", Short[Last[timed], 5]]; Exit[1]];
	First[timed]
]

commit = Quiet[Check[StringTrim[RunProcess[{"git", "-C", $repositoryDirectory, "rev-parse", "--short", "HEAD"}, "StandardOutput"]], "?"]]

Print[$Version, "; TypeTheory ", commit, "; Method -> ", method, "; ", runs, " runs after the first"]

results = Function[file,
	Block[{read, environment, first, checks},
		(* a file another kernel wrote reads only with a check *)
		read = First[AbsoluteTiming[environment = Replace[TypeTheoryEnvironment[File[file]], failure_Failure /; failure["Tag"] === "SavedByAnotherKernel" :> TypeTheoryEnvironment[File[file], "Check" -> True]]]];
		If[FailureQ[environment], Print["FATAL: ", file, " does not read: ", environment]; Exit[1]];
		first = timedCheck[environment];
		checks = Table[timedCheck[environment], runs];
		<|"File" -> FileBaseName[file], "Constants" -> Length[environment], "Read" -> read, "First" -> first, "Min" -> Min[checks], "Median" -> Median[checks], "Environment" -> environment|>
	]
] /@ files

Print[StringPadRight["file", 24], StringPadLeft["constants", 10], StringPadLeft["read s", 9], StringPadLeft["first s", 9], StringPadLeft["min s", 9], StringPadLeft["median s", 10]]

Scan[
	Function[result,
		Print[
			StringPadRight[result["File"], 24],
			StringPadLeft[ToString[result["Constants"]], 10],
			StringPadLeft[ToString[Round[result["Read"], 0.01]], 9],
			StringPadLeft[ToString[Round[result["First"], 0.01]], 9],
			StringPadLeft[ToString[Round[result["Min"], 0.01]], 9],
			StringPadLeft[ToString[Round[result["Median"], 0.01]], 10]
		]
	],
	results
]

If[ profileQ,
	Block[{overhead = calibrationSeconds[], skipped},
		skipped = Select[$profiled, ! instrument[#]&];
		Scan[
			Function[result,
				Scan[Function[short, $calls[short] = 0; $nesting[short] = 0; $exclusive[short] = 0.; $outermost[short] = 0.], Complement[$profiled, skipped]];
				With[{seconds = timedCheck[result["Environment"]]},
					Print["profile of ", result["File"], " (", Round[seconds, 0.1], " s profiled, less ", Round[10^6 overhead, 0.1], " us a call): calls, exclusive seconds, seconds in outermost calls"];
					Scan[
						Function[row, Print["  ", StringPadRight[row[[1]], 32], StringPadLeft[ToString[row[[2]]], 10], StringPadLeft[ToString[row[[3]]], 10], StringPadLeft[ToString[row[[4]]], 10]]],
						ReverseSortBy[
							Function[short, {short, $calls[short], Round[$exclusive[short] - $calls[short] overhead, 0.01], Round[$outermost[short], 0.01]}] /@ Complement[$profiled, skipped],
							#[[3]]&
						]
					]
				]
			],
			results
		];
		If[skipped =!= {}, Print["  not profiled (not found, or holding their arguments): ", StringRiffle[skipped, ", "]]]
	]
]
