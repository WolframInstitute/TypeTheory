(* ::Package:: *)

(* Tests for Checking/Rules.wl and the rules environments carry: named rules and their settings, empty
   environments of given rules, universes and theorems without Prop, and replay under the same rules. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

martinLof = TypeTheoryRules["MartinLofTypeTheory"]

withoutProp = TypeTheoryEnvironment[martinLof]

unit = TypeTheoryEnvironment[martinLof, {TypeTheoryInductiveType[Unit, TypeUniverse[1], {UnitIntroduction -> Unit}]}]


VerificationTest[
	{TypeTheoryRules["CalculusOfInductiveConstructions"]["Prop"], martinLof["Prop"], TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True]},
	{True, False, TypeTheoryRules[<|"Name" -> "MartinLofTypeTheory", "Prop" -> False, "RewriteRules" -> True, "Quotients" -> False, "Quantities" -> False, "Cubical" -> False|>]},
	TestID -> "Named-rules-and-their-settings"
]

VerificationTest[
	{
		Information[prelude, "Rules"] === TypeTheoryRules["CalculusOfInductiveConstructions"],
		Information[TypeTheoryEnvironment[], "Rules"] === Information[prelude, "Rules"],
		Information[unit, "Rules"] === martinLof,
		TypeTheoryEnvironment[martinLof] === withoutProp
	},
	{True, True, True, True},
	TestID -> "An-environment-carries-its-rules-and-passes-them-on"
]

VerificationTest[
	First /@ {
		TypeTheoryEnvironment[withoutProp, {TypeTheoryAxiom[Proposition, TypeUniverse[0]]}],
		TypeTheoryEnvironment[withoutProp, {TypeTheoryAxiom[AnySort, TypeUniverse[u]]}]
	},
	{"NoProp", "NoProp"},
	TestID -> "Without-Prop-no-universe-may-be-Prop"
]

VerificationTest[
	{
		Keys[TypeTheoryEnvironment[withoutProp, {TypeTheoryAxiom[AnyType, TypeUniverse[u + 1]]}]],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[InductiveRecursor[Unit], unit]], TypeTheoryTerm[ForAll[{Typed[_, TypeSpecifier[{Unit} -> TypeUniverse[_Symbol + 1]]]}, _], _]]
	},
	{{AnyType}, True},
	TestID -> "Without-Prop-a-recursor-eliminates-into-Type-u"
]

VerificationTest[
	{
		Keys[TypeTheoryEnvironment[unit, {TypeTheoryTheorem[UnitInhabited, Unit, UnitIntroduction]}]],
		First @ TypeTheoryEnvironment[TypeTheoryEnvironment[], {
			TypeTheoryInductiveType[Unit, TypeUniverse[1], {UnitIntroduction -> Unit}],
			TypeTheoryTheorem[UnitInhabited, Unit, UnitIntroduction]
		}]
	},
	{{Unit, UnitIntroduction, InductiveRecursor[Unit], UnitInhabited}, "PropositionExpected"},
	TestID -> "Without-Prop-a-theorem-may-state-any-type"
]

VerificationTest[
	{MatchQ[TypeTheoryCheck[unit], _Success], Information[TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[unit]], "Rules"] === martinLof},
	{True, False},
	TestID -> "Replay-uses-the-rules-of-the-environment"
]
