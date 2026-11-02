(* ::Package:: *)

(*
WolframDefinitions: reading the definitions of a Wolfram Language symbol, the first step of typing them.

The definitions are lowered by the compiler of the WolframKernel project, which the paclet Wolfram/KernelCompiler
publishes: its ToCore turns a symbol's definitions into a Core`Program, each definition a match program of the Match
IR for its left side and Core for its right side. TypeTheory loads that paclet only when definitions are read, as
LeanLink loads TypeTheory, and gives a Failure naming how to install it where it is missing. The Core`/Match` forms
are versioned by Compiler`$CoreVersion, which must be the version this file is written for.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[lowerDefinitions]
PackageScoped[loadKernelCompiler]


(* ::Section:: *)
(*Usage Messages*)


lowerDefinitions::usage = "lowerDefinitions[HoldComplete[symbol]] gives the Core`Program of the definitions of symbol, by the compiler's ToCore, or a Failure."
loadKernelCompiler::usage = "loadKernelCompiler[] loads the paclet Wolfram/KernelCompiler and gives True, or gives a Failure where it is missing or writes Core of another version."


(* ::Section:: *)
(*Function Definitions*)


$kernelCompilerResource = "https://www.wolframcloud.com/obj/nikm/DeployedResources/Paclet/Wolfram/KernelCompiler"

(* the version of the compiler's Core`/Match` forms that reading definitions is written for, and the paclet's versions
   that write it *)
$kernelCompilerCoreVersion = 1
$kernelCompilerVersions = "0.1."

$kernelCompilerLoaded = False

(* loaded once; a paclet installed after a failure is found the next time *)
loadKernelCompiler[] := Which[
	$kernelCompilerLoaded,
		True,
	! AnyTrue[PacletFind["Wolfram/KernelCompiler"], Function[paclet, StringStartsQ[paclet["Version"], $kernelCompilerVersions]]],
		Failure["KernelCompilerMissing", <|
			"MessageTemplate" -> "Reading Wolfram Language definitions needs the paclet Wolfram/KernelCompiler `1`*. Install it with `2`.",
			"MessageParameters" -> {$kernelCompilerVersions, "PacletInstall[ResourceObject[\"" <> $kernelCompilerResource <> "\"]]"}
		|>],
	True,
		Needs["Wolfram`KernelCompiler`"];
		If[ Symbol["Compiler`$CoreVersion"] === $kernelCompilerCoreVersion,
			$kernelCompilerLoaded = True,
			Failure["KernelCompilerVersion", <|
				"MessageTemplate" -> "The paclet Wolfram/KernelCompiler writes Core of version `1`, and reading definitions is written for version `2`.",
				"MessageParameters" -> {Symbol["Compiler`$CoreVersion"], $kernelCompilerCoreVersion}
			|>]
		]
]

(* the definitions as held statements, lhs := rhs, which is what ToCore takes; nothing of them evaluates *)
SetAttributes[definitionStatements, HoldAllComplete]
definitionStatements[symbol_Symbol] := Cases[DownValues[symbol], RuleDelayed[HoldPattern[lhs_], rhs_] :> HoldComplete[SetDelayed[lhs, rhs]]]

lowerDefinitions[HoldComplete[symbol_Symbol]] := Replace[loadKernelCompiler[], {
	True :> Symbol["Compiler`ToCore"][definitionStatements[symbol]],
	failure_Failure :> failure
}]
