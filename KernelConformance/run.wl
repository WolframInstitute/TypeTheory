(* ::Package:: *)

(* Runs the conformance corpus on a Wolfram Language kernel and prints each case whose result differs
   from Wolfram 15's. It uses only plain WL, so that a young kernel can run it.

   Usage:
     kernel run.wl [Corpus.wl] [first]

   Corpus.wl next to this file is the default; first is the number of the case to start from. *)

(* the script's own path is in $ScriptCommandLine too, at a place that differs between kernels *)
arguments = Select[$ScriptCommandLine, ! StringEndsQ[#, "run.wl"] &]

corpusFile = Replace[
	Select[arguments, StringEndsQ[#, ".wl"] &],
	{{file_, ___} :> file, {} :> FileNameJoin[{DirectoryName[$InputFileName], "Corpus.wl"}]}
]

firstCase = Replace[Select[arguments, StringMatchQ[#, DigitCharacter ..] &], {{n_, ___} :> ToExpression[n], {} :> 1}]

cases = Get[corpusFile]

code[HoldComplete[expr_]] := ToString[Unevaluated[expr], InputForm]

(* a case's call evaluated here, held; a Throw that nothing catches is caught and shown *)
actualResult[call_HoldComplete] := Catch[HoldComplete @@ {ReleaseHold[call]}, _, uncaught]

differing = Select[
	Take[cases, {firstCase, Length[cases]}],
	Function[case,
		With[{actual = actualResult[case[[2]]]},
			If[ actual === case[[3]],
				False,
				Print[
					case[[1]],
					"\n  input:    ", code[case[[2]]],
					"\n  expected: ", code[case[[3]]],
					"\n  actual:   ", If[MatchQ[actual, _HoldComplete], code[actual], ToString[actual, InputForm]]
				];
				True
			]
		]
	]
]

Print[Length[differing], " of ", Length[cases] - firstCase + 1, " cases differ"]
