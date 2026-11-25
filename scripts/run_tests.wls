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

(* the tests read the boxes a notebook shows, which a kernel with no front end gives only when asked *)
SetEnvironment["TYPETHEORY_NOTEBOOK_BOXES" -> "True"]

PacletDirectoryLoad[pacletDirectory]

(* Each test file loads the paclet with Needs, which takes the highest version the paclet manager knows: an installed
   release newer than this checkout would be tested in its place. The checkout's own code is loaded first, so each
   file's Needs finds the context loaded, and the paclet finds its libraries and saved environments beside that code. *)
Get[FileNameJoin[{pacletDirectory, "Kernel", "TypeTheory.wl"}]]

Print["TypeTheory ", PacletObject[File[pacletDirectory]]["Version"], " from ", pacletDirectory]

(* a file given relative to the repository root is made absolute, so that its line names it under the tests *)
testFiles = If[ Length[$ScriptCommandLine] > 1,
	Map[ExpandFileName, Rest[$ScriptCommandLine]],
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
	report = If[ Environment["TT_TEST_PROGRESS"] === "1",
		TestReport[file, HandlerFunctions -> <|"TestEvaluated" -> testProgress|>],
		TestReport[file]
	];
	failures = Cases[
		Values[report["TestResults"]],
		result_ /; result["Outcome"] =!= "Success" :> result /@ {"TestID", "ActualOutput", "ExpectedOutput", "ActualMessages"}
	];
	<|"File" -> file, "Passed" -> report["TestsSucceededCount"], "Failed" -> report["TestsFailedCount"], "Failures" -> failures|>
]

(* with TT_TEST_PROGRESS=1, a line as each test ends, so that a file stopped at its time limit names the last test that
   ended *)
testProgress[event_Association] := Print["  test  ", Lookup[event, "TestObject", Missing[]]["TestID"]]

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
