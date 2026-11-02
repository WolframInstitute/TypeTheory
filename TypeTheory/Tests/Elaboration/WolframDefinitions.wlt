(* ::Package:: *)

(* Tests for Elaboration/WolframDefinitions.wl: reading a symbol's definitions through the compiler, or a Failure that
   names how to install it. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

(* with the compiler a Core`Program with a definition for each of the symbol's; without it a Failure naming the
   paclet *)
VerificationTest[
	Block[{size},
		size[{}] = 0;
		size[{x_, rest___}] := 1 + size[{rest}];
		Replace[WolframInstitute`TypeTheory`PackageScope`lowerDefinitions[HoldComplete[size]], {
			Failure["KernelCompilerMissing", KeyValuePattern["MessageParameters" -> {_, install_String}]] :> StringContainsQ[install, "Wolfram/KernelCompiler"],
			program_ :> Length[Catenate[Values[First[program]]]] >= 2
		}]
	],
	True,
	TestID -> "Definitions-are-lowered-by-the-compiler-or-its-install-is-named"
]
