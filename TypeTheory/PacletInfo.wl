(* ::Package:: *)

PacletObject[<|
	"Name" -> "WolframInstitute/TypeTheory",
	"PublisherID" -> "WolframInstitute",
	"Version" -> "0.16.1",
	"WolframVersion" -> "15.0+",
	"Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language",
	"Creator" -> "Nikolay Murzin",
	"License" -> "MIT",
	"Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"},
	"Categories" -> {"Mathematics"},
	"PrimaryContext" -> "WolframInstitute`TypeTheory`",
	"Extensions" -> {
		{
			"Kernel",
			"Root" -> "Kernel",
			"Context" -> {"WolframInstitute`TypeTheory`"}
		},
		{"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"},
		{"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"},
		(* PacletBuild packs only the declared extensions: the library environments the release saves, which the paclet reads
		   instead of checking them again, and the compiled kernel's library *)
		{
			"Asset",
			"Root" -> "Environments",
			"Assets" -> {
				{"Constructive", "Constructive.wxf"},
				{"Prelude", "Prelude.wxf"},
				{"Integers", "Integers.wxf"},
				{"Rationals", "Rationals.wxf"},
				{"HomotopyTypeTheory", "HomotopyTypeTheory.wxf"},
				{"Cubical", "Cubical.wxf"}
			}
		},
		{"LibraryLink", "Root" -> "LibraryResources"}
	}
|>]
