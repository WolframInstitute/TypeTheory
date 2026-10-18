#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Run the WolframInstitute`TypeTheory` test files and report to stdout.

   Usage:
     wolframscript -f scripts/run_tests.wls             (* every test file *)
     wolframscript -f scripts/run_tests.wls a.wlt b.wlt (* the given files *)

   Each .wlt file loads the paclet from the working directory, so the runner works from the
   repository root. It prints a line per file and a summary, and exits with status 1 if any test
   fails, so it can run in CI. *)

repositoryRoot = ParentDirectory[DirectoryName[$InputFileName]]

pacletDirectory = FileNameJoin[{repositoryRoot, "TypeTheory"}]

testsDirectory = FileNameJoin[{pacletDirectory, "Tests"}]

SetDirectory[repositoryRoot]

PacletDirectoryLoad[pacletDirectory]

testFiles = If[ Length[$ScriptCommandLine] > 1,
	Rest[$ScriptCommandLine],
	FileNames["*.wlt", testsDirectory, Infinity]
]

If[ testFiles === {},
	Print["no .wlt files found under ", testsDirectory];
	Exit[1]
]

(* Global` bindings a file leaves behind are cleared before the next file, so files stay independent.
   The runner's own symbols are the ones that exist when the first file runs, by which time the line
   that runs them has created every symbol the runner needs. *)
runTestFile[file_String] := Module[{report, failures},
	If[ ! ListQ[$runnerSymbols], $runnerSymbols = Names["Global`*"]];
	Quiet[ClearAll @@ Complement[Names["Global`*"], $runnerSymbols]];
	report = TestReport[file];
	failures = Cases[
		Values[report["TestResults"]],
		result_ /; result["Outcome"] =!= "Success" :> result /@ {"TestID", "ActualOutput", "ExpectedOutput", "ActualMessages"}
	];
	<|"File" -> file, "Passed" -> report["TestsSucceededCount"], "Failed" -> report["TestsFailedCount"], "Failures" -> failures|>
]

results = runTestFile /@ testFiles

Scan[
	Function[result,
		Print[
			If[result["Failed"] === 0, "  ok    ", "  FAIL  "],
			FileNameDrop[result["File"], FileNameDepth[testsDirectory]],
			"  (", result["Passed"], "/", result["Passed"] + result["Failed"], ")"
		];
		Scan[
			Function[failure,
				Print[
					"          failed: ", First[failure],
					"\n          actual: ", InputForm[failure[[2]]],
					"\n        expected: ", InputForm[failure[[3]]],
					"\n        messages: ", InputForm[Last[failure]]
				]
			],
			result["Failures"]
		]
	],
	results
]

totalPassed = Total[Lookup[results, "Passed"]]

totalFailed = Total[Lookup[results, "Failed"]]

Print[""]
Print[If[totalFailed === 0, "PASS", "FAIL"], "  ", totalPassed, "/", totalPassed + totalFailed, " tests passed across ", Length[testFiles], " files"]

Exit[If[totalFailed === 0, 0, 1]]
