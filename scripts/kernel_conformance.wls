#!/usr/bin/env wolframscript
(* ::Package:: *)

(* A conformance corpus for other Wolfram Language kernels: the System` calls TypeTheory makes, each with
   Wolfram 15's result.

   Usage:
     wolframscript -f scripts/kernel_conformance.wls

   It loads TypeTheory, traces every System` call that building the prelude and running the tests make, and
   keeps, for each System` function, the smallest call of each shape of arguments that can be replayed on its
   own: no symbol in the call or its result has definitions or attributes outside System`, and none is a
   Module variable. A fresh kernel, without TypeTheory, then replays each call, and the calls that give the
   same result there make the corpus, in KernelConformance/:

     Corpus.wlt   VerificationTest[call, result, TestID -> "Function-n"], for TestReport
     Corpus.wl    {{"Function-n", HoldComplete[call], HoldComplete[result]}, ...}, for KernelConformance/run.wl
     Calls.tsv    every System` function TypeTheory calls, with how often

   The second step runs as wolframscript -f scripts/kernel_conformance.wls write trace.wxf. *)

repositoryRoot = ParentDirectory[DirectoryName[$InputFileName]]

corpusDirectory = FileNameJoin[{repositoryRoot, "KernelConformance"}]


(* ::Section:: *)
(*Tracing*)


(* calls with side effects, or whose result depends on the session, are counted but never kept *)
$excludedHeads = Alternatives @@ {
	Print, Message, Set, SetDelayed, Unset, AppendTo, PrependTo, AssociateTo, KeyDropFrom, Increment, Decrement,
	PreIncrement, PreDecrement, AddTo, SubtractFrom, TimesBy, Clear, ClearAll, SetAttributes, ClearAttributes,
	Protect, Unprotect, Needs, Get, BeginPackage, Begin, End, EndPackage, Module, Block, With, Unique, Symbol,
	AbsoluteTime, SessionTime, TimeUsed, AbsoluteTiming, Timing, RandomInteger, RandomReal, RandomSample,
	RandomChoice, CreateDataStructure, Throw, Catch, Check, Quiet, CompoundExpression, Return, Sow, Reap, Abort,
	Names, Contexts, Remove, Off, On, Information, Definition, DownValues, UpValues, OwnValues, SubValues,
	FileNames, Import, OpenRead, OpenWrite, OpenAppend, Read, ReadList, Close, Streams, StringToStream,
	InputStream, OutputStream, Directory, SetDirectory, ResetDirectory, PacletDirectoryLoad, PacletFind,
	PacletObject, MemoryInUse, MaxMemoryUsed, Share, ClearSystemCache, Hold, HoldComplete, HoldForm, Unevaluated,
	Function, Condition, Pattern, Blank, BlankSequence, BlankNullSequence, Alternatives, PatternTest, Verbatim,
	HoldPattern, Rule, RuleDelayed, RuleCondition, List, VerificationTest, TestReport, MessageName, StringForm,
	ToString, ToExpression, ToBoxes, MakeBoxes, Format, Interpretation, Enclose, Confirm, ConfirmBy, ConfirmMatch,
	ConfirmQuiet, Exit, Quit, Pause, CheckAbort, AbortProtect, WithCleanup, Failure, Missing, EvaluationData,
	Context, Stack, Trace, TraceScan, Echo, EchoFunction, Assert, TimeConstrained, MemoryConstrained, Evaluate,
	Options, SetOptions, OptionValue, Attributes, Messages, Dynamic, Refresh, Short, Shallow, CreateUUID, Hash,
	DateObject, DateString, Now, Today
}

SetAttributes[{systemSymbolQ, tracedHeadQ, sessionSymbolQ, moduleSymbolQ, argumentKind}, HoldAllComplete]

systemSymbolQ[symbol_Symbol] := Context[Unevaluated[symbol]] === "System`"
systemSymbolQ[_] := False

tracedHeadQ[head_Symbol] := systemSymbolQ[head] && ! MatchQ[Unevaluated[head], $excludedHeads]
tracedHeadQ[_] := False

(* a symbol outside System` with definitions or attributes means something only to this session *)
sessionSymbolQ[symbol_Symbol] := sessionSymbolQ[symbol] = ! systemSymbolQ[symbol] && Or[
	DownValues[symbol] =!= {},
	OwnValues[symbol] =!= {},
	SubValues[symbol] =!= {},
	UpValues[symbol] =!= {},
	FormatValues[symbol] =!= {},
	NValues[symbol] =!= {},
	DefaultValues[symbol] =!= {},
	Attributes[symbol] =!= {}
]

moduleSymbolQ[symbol_Symbol] := StringMatchQ[SymbolName[Unevaluated[symbol]], __ ~~ "$" ~~ DigitCharacter ..]

replayableQ[held_HoldComplete] := FreeQ[held, symbol_Symbol /; sessionSymbolQ[symbol] || moduleSymbolQ[symbol], {0, Infinity}, Heads -> True]

(* The kind of an argument, coarse enough that each function has few shapes: the identity of a symbol
   counts only for a few, and the name of an option only for a System` symbol. *)
$namedSymbols = HoldComplete[True, False, None, All, Automatic, Infinity, Null]

$patternHeads = Alternatives @@ {
	Blank, BlankSequence, BlankNullSequence, Pattern, Alternatives, Condition, PatternTest, Verbatim, HoldPattern,
	Except, Repeated, RepeatedNull, KeyValuePattern, OptionsPattern, PatternSequence, OrderlessPatternSequence,
	Longest, Shortest
}

argumentKind[_String] := String
argumentKind[_Integer] := Integer
argumentKind[_Real] := Real
argumentKind[_Rational] := Rational
argumentKind[_Complex] := Complex
argumentKind[symbol_Symbol] := If[MemberQ[$namedSymbols, Unevaluated[symbol]], HoldComplete[symbol], Symbol]
argumentKind[association_Association] /; AssociationQ[Unevaluated[association]] := Association
argumentKind[{}] := "EmptyList"
argumentKind[_List] := List
argumentKind[(rule : Rule | RuleDelayed)[name_Symbol, _]] /; systemSymbolQ[name] := {rule, HoldComplete[name]}
argumentKind[(Rule | RuleDelayed)[_, _]] := Rule
argumentKind[(head_Symbol)[___]] /; MatchQ[Unevaluated[head], $patternHeads] := "Pattern"
argumentKind[_Function] := Function
argumentKind[(Hold | HoldComplete | HoldForm)[___]] := "Held"
argumentKind[_] := Expression

(* the shape of a call: its function, how many arguments it has, the kinds of the first three, and its options *)
callShape[HoldComplete[head_[arguments___]]] := {
	HoldComplete[head],
	Min[Length[HoldComplete[arguments]], 6],
	Take[List @@ (argumentKind /@ HoldComplete[arguments]), UpTo[3]],
	Cases[HoldComplete[arguments], (Rule | RuleDelayed)[name_Symbol, _] /; systemSymbolQ[name] :> HoldComplete[name]]
}

$maximumShapes = 24

$maximumLeafCount = 400

(* every call, counted by function *)
$callCounts = <||>

(* function -> <|shape -> {leafCount, HoldComplete[call], HoldComplete[result]}, ...|>, the smallest call of each shape *)
$samples = <||>

beforeCall[HoldCompleteForm[head_Symbol[___]]] := ($callCounts[HoldComplete[head]] = Lookup[$callCounts, Key[HoldComplete[head]], 0] + 1)
beforeCall[_] := Null

(* an association applied to a key is traced too, but has no function to file it under *)
afterCall[HoldCompleteForm[call_], result_] := Module[{held = HoldComplete[call], head, shape, leafCount, shapes},
	leafCount = LeafCount[held];
	head = Extract[held, {1, 0}, HoldComplete];
	If[ leafCount <= $maximumLeafCount && MatchQ[head, HoldComplete[symbol_Symbol /; tracedHeadQ[symbol]]],
		shape = callShape[held];
		shapes = Lookup[$samples, Key[head], <||>];
		If[ And[
				If[KeyExistsQ[shapes, Key[shape]], leafCount < First[shapes[Key[shape]]], Length[shapes] < $maximumShapes],
				LeafCount[HoldComplete[result]] <= $maximumLeafCount,
				replayableQ[held],
				replayableQ[HoldComplete[result]]
			],
			$samples[head] = Append[shapes, shape -> {leafCount, held, HoldComplete[result]}]
		]
	]
]

SetAttributes[{beforeCall, afterCall}, HoldAllComplete]

traced[expr_] := TraceScan[beforeCall, expr, head_Symbol[___] /; tracedHeadQ[head], afterCall]

SetAttributes[traced, HoldAllComplete]

(* a test file's statements one at a time, tracing each test's input and expected output, not MUnit *)
traceTestFile[file_String] := Scan[
	Replace[{
		HoldComplete[VerificationTest[input_, expected_, ___]] :> (traced[input]; traced[expected]),
		HoldComplete[VerificationTest[input_]] :> traced[input],
		HoldComplete[statement_] :> traced[statement]
	}],
	ReadList[file, HoldComplete[Expression]]
]

report[label_String, start_] := Print[
	label, ": ", Round[AbsoluteTime[] - start], " s, ", Total[$callCounts], " calls so far, ",
	Total[Length /@ $samples], " shapes of ", Length[$samples], " functions"
]

trace[] := Module[{scoped, start, constructive, testFiles, traceFile},
	PacletDirectoryLoad[FileNameJoin[{repositoryRoot, "TypeTheory"}]];
	SetDirectory[repositoryRoot];
	Needs["WolframInstitute`TypeTheory`"];
	scoped = Function[name, Symbol["WolframInstitute`TypeTheory`PackageScope`" <> name]];
	(* the prelude is built afresh, as loading built it, since Get is not traced *)
	start = AbsoluteTime[];
	constructive = traced[TypeTheoryEnvironment[scoped["$emptyEnvironment"], scoped["$constructiveDeclarations"]]];
	traced[TypeTheoryEnvironment[constructive, scoped["$classicalDeclarations"]]];
	report["prelude", start];
	testFiles = FileNames["*.wlt", FileNameJoin[{repositoryRoot, "TypeTheory", "Tests"}], Infinity];
	Scan[
		Function[file,
			start = AbsoluteTime[];
			traceTestFile[file];
			report[FileNameDrop[file, FileNameDepth[repositoryRoot] + 2], start]
		],
		testFiles
	];
	traceFile = FileNameJoin[{$TemporaryDirectory, "TypeTheoryKernelConformance.wxf"}];
	Export[traceFile, <|"CallCounts" -> ReverseSort[$callCounts], "Samples" -> $samples|>, "WXF"];
	traceFile
]


(* ::Section:: *)
(*Replaying and writing*)


(* never run these, whatever the trace kept *)
$unsafeHeads = Alternatives @@ {
	Export, Put, PutAppend, DeleteFile, CreateFile, CreateDirectory, DeleteDirectory, CopyFile, RenameFile,
	WriteString, Write, Run, RunProcess, StartProcess, URLRead, URLFetch, URLExecute, SystemOpen, CloudPut,
	CloudDeploy, LinkLaunch, Install, LibraryFunctionLoad
}

toCode[expr_] := Block[{$ContextPath = {"System`"}, $Context = "Global`"},
	ToString[Unevaluated[expr], InputForm, CharacterEncoding -> "ASCII", PageWidth -> Infinity]
]

SetAttributes[toCode, HoldAllComplete]

heldCode[HoldComplete[expr_]] := toCode[expr]

(* the call read back from its code and evaluated afresh, with the messages it gives *)
replayed[callCode_String] := With[
	{data = EvaluationData[TimeConstrained[ReleaseHold[ToExpression[callCode, InputForm, HoldComplete]], 10, $timedOut]]},
	{HoldComplete @@ {data["Result"]}, data["Messages"]}
]

(* a case is kept if its call gives the traced result again, and the result evaluates to itself, as
   VerificationTest evaluates the expected output *)
replayedCase[{_, call_HoldComplete, result_HoldComplete}] := Module[{callCode, resultCode, again, expected},
	callCode = heldCode[call];
	resultCode = heldCode[result];
	again = replayed[callCode];
	expected = ToExpression[resultCode, InputForm, HoldComplete];
	If[ First[again] === expected && ReleaseHold[expected] === ReleaseHold[First[again]] && FreeQ[again, $timedOut],
		{SymbolName @@ Extract[call, {1, 0}, HoldComplete], callCode, resultCode, Last[again]},
		Nothing
	]
]

messagesCode[{}] := ""
messagesCode[messages_List] := ",\n\t{" <> StringRiffle[Function[message, ToString[Unevaluated[message], InputForm], HoldAllComplete] /@ messages, ", "] <> "}"

testCode[{id_, callCode_, resultCode_, messages_}] := StringJoin[
	"VerificationTest[\n\t", callCode, ",\n\t", resultCode, messagesCode[messages], ",\n\tTestID -> \"", id, "\"\n]"
]

(* cases numbered within each function: Lookup-1, Lookup-2, ... *)
numbered[cases_List] := Catenate[
	MapIndexed[
		Function[{case, index}, ReplacePart[case, 1 -> First[case] <> "-" <> ToString[First[index]]]],
		#
	] & /@ GatherBy[SortBy[cases, {First, StringLength[#[[2]]] &}], First]
]

write[traceFile_String] := Module[{data, samples, replayedCases, cases},
	data = Import[traceFile, "WXF"];
	samples = Catenate[Values /@ Values[data["Samples"]]];
	replayedCases = replayedCase /@ Select[samples, Function[sample, ! MatchQ[sample[[2]], HoldComplete[$unsafeHeads[___]]]]];
	cases = numbered[replayedCases];
	Quiet[CreateDirectory[corpusDirectory]];
	Export[
		FileNameJoin[{corpusDirectory, "Corpus.wlt"}],
		StringJoin[
			"(* ::Package:: *)\n\n",
			"(* Calls of System` functions that TypeTheory makes, each with Wolfram 15's result: a conformance\n",
			"   corpus for kernels that run TypeTheory. Written by scripts/kernel_conformance.wls; do not edit. *)\n\n",
			StringRiffle[testCode /@ cases, "\n\n"],
			"\n"
		],
		"Text",
		CharacterEncoding -> "ASCII"
	];
	Export[
		FileNameJoin[{corpusDirectory, "Corpus.wl"}],
		StringJoin[
			"(* {id, HoldComplete[call], HoldComplete[Wolfram 15's result]}, the cases of Corpus.wlt.\n",
			"   Written by scripts/kernel_conformance.wls; do not edit. *)\n\n{\n",
			StringRiffle[Function[case, "\t{\"" <> case[[1]] <> "\", HoldComplete[" <> case[[2]] <> "], HoldComplete[" <> case[[3]] <> "]}"] /@ cases, ",\n"],
			"\n}\n"
		],
		"Text",
		CharacterEncoding -> "ASCII"
	];
	Export[
		FileNameJoin[{corpusDirectory, "Calls.tsv"}],
		Prepend[KeyValueMap[Function[{head, count}, {SymbolName @@ head, count}], data["CallCounts"]], {"function", "calls"}],
		"TSV"
	];
	Print[Length[cases], " cases of ", Length[GatherBy[replayedCases, First]], " functions, of ", Length[samples], " traced, in ", corpusDirectory]
]


(* ::Section:: *)
(*Main*)


Replace[Rest[$ScriptCommandLine], {
	{"write", traceFile_String} :> write[traceFile],
	{} :> With[{traceFile = trace[]},
		Print[RunProcess[{"wolframscript", "-f", $InputFileName, "write", traceFile}, "StandardOutput"]];
		DeleteFile[traceFile]
	],
	_ :> (Print["usage: wolframscript -f scripts/kernel_conformance.wls"]; Exit[2])
}]
