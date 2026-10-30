#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Compile the compiled kernel's library (Kernel/Checking/CompiledKernel.wl) into TypeTheory/LibraryResources/<$SystemID>/,
   named by the engine and its version, with the hash of the program beside it, so that TypeTheoryCheck checks with it.
   Run it after changing the program, with each engine and version the paclet runs under; on Wolfram 15.1 it takes about
   five minutes and six gigabytes of memory:

       wl -f scripts/compile_kernel.wls *)

PacletDirectoryLoad[FileNameJoin[{ParentDirectory[DirectoryName[$InputFileName]], "TypeTheory"}]]

Needs["WolframInstitute`TypeTheory`"]

Block[{started = AbsoluteTime[], library = WolframInstitute`TypeTheory`PackageScope`compileKernelLibrary[]},
	If[FailureQ[library], Print[library]; Exit[1]];
	Print["compiled ", First[library], " in ", Round[AbsoluteTime[] - started], " s"];
	If[! WolframInstitute`TypeTheory`PackageScope`compiledKernelAvailableQ[], Print["FATAL: the library does not load"]; Exit[1]]
]
