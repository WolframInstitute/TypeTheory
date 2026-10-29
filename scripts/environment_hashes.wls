#!/usr/bin/env wolframscript
(* ::Package:: *)

(* The content hash of each library environment, and where this session got it: read from the paclet's saved files,
   or built from the declarations when there are none for this kernel or TYPETHEORY_SAVED_ENVIRONMENTS=0 is set. The
   hash is SHA-256 of the environment's contents as BinarySerialize writes them, the same in every session for an
   environment built the same way, so a built environment's lines match the saved files', and match on every kernel
   that builds and writes WXF as Wolfram 15 does:

       TYPETHEORY_SAVED_ENVIRONMENTS=0 wl -f scripts/environment_hashes.wls
       wl -f scripts/environment_hashes.wls *)

PacletDirectoryLoad[FileNameJoin[{ParentDirectory[DirectoryName[$InputFileName]], "TypeTheory"}]]

Needs["WolframInstitute`TypeTheory`"]

Scan[
	Function[name, With[{library = TypeTheoryEnvironment[name]},
		Print[
			StringPadRight[name, 20],
			WolframInstitute`TypeTheory`PackageScope`environmentContentHash[library],
			"  ",
			Replace[Information[library, "Provenance"]["Source"], File[file_] :> "read from " <> FileNameTake[file]]
		]
	]],
	{"Constructive", "Prelude", "Integers", "Rationals", "HomotopyTypeTheory", "Cubical"}
]
