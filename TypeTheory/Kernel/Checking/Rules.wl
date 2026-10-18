(* ::Package:: *)

(*
The rules of a type theory, as a value. Every environment carries the rules it was started with, and
the kernel checks each declaration and term by the rules of its environment. The declarations of an
environment are its assumptions, axioms included; the rules are what the kernel allows and computes.

	TypeTheoryRules[<|"Name" -> name, "Prop" -> True | False, "RewriteRules" -> True | False|>]

	"Prop"            TypeUniverse[0] is a universe of propositions: impredicative, with proof irrelevance,
	                  K-like reduction and elimination of subsingletons into any universe. Without it every
	                  universe is TypeUniverse[level] with level at least 1, and a theorem's statement may
	                  be any type.
	"RewriteRules"    TypeTheoryRewriteRule declarations may add computation rules to an axiom.

"CalculusOfInductiveConstructions" is the rules of the prelude, which those of Lean's kernel are.
"MartinLofTypeTheory" has no Prop, as Martin-Löf's intensional type theory, and so no rule that would
make any two equalities equal: univalence is consistent with it.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryRules]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[rulesQ]
PackageScoped[rulesSetting]
PackageScoped[$defaultRules]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryRules::usage = "TypeTheoryRules[name] gives the rules of the named type theory: \"CalculusOfInductiveConstructions\", the rules of the prelude, \
or \"MartinLofTypeTheory\", with no universe of propositions.\n\
TypeTheoryRules[name, setting -> value, ...] gives those rules with some settings changed.\n\
TypeTheoryRules[<|\"Name\" -> name, \"Prop\" -> p, \"RewriteRules\" -> r|>] is the rules with the given settings: p says whether TypeUniverse[0] is \
an impredicative universe of propositions with proof irrelevance, and r whether rewrite rules may be declared.\n\
TypeTheoryEnvironment[rules] gives an environment with no constants that follows rules; Information[environment, \"Rules\"] gives an environment's."

rulesQ::usage = "rulesQ[expr] gives True if expr is a valid TypeTheoryRules value."
rulesSetting::usage = "rulesSetting[environment, setting] gives the value of setting in the rules of environment."
$defaultRules::usage = "$defaultRules is the rules of TypeTheoryEnvironment[] and of the prelude."


(* ::Section:: *)
(*Function Definitions*)


$ruleSettings = {"Prop", "RewriteRules"}

$namedRules = <|
	"CalculusOfInductiveConstructions" -> <|"Name" -> "CalculusOfInductiveConstructions", "Prop" -> True, "RewriteRules" -> False|>,
	"MartinLofTypeTheory" -> <|"Name" -> "MartinLofTypeTheory", "Prop" -> False, "RewriteRules" -> False|>
|>

rulesQ[TypeTheoryRules[settings_Association]] := And[
	StringQ[settings["Name"]],
	Sort[Keys[settings]] === Sort[Prepend[$ruleSettings, "Name"]],
	AllTrue[Lookup[settings, $ruleSettings], BooleanQ]
]
rulesQ[_] := False

TypeTheoryRules[name_String] /; KeyExistsQ[$namedRules, name] := TypeTheoryRules[$namedRules[name]]
TypeTheoryRules[name_String, changes__Rule] /; KeyExistsQ[$namedRules, name] := TypeTheoryRules[TypeTheoryRules[name], changes]
TypeTheoryRules[rules_TypeTheoryRules?rulesQ, changes__Rule] /; SubsetQ[$ruleSettings, Keys[{changes}]] && AllTrue[Values[{changes}], BooleanQ] :=
	TypeTheoryRules[Join[First[rules], Association[{changes}]]]

(rules : TypeTheoryRules[settings_Association])[setting_String] /; rulesQ[rules] := Lookup[settings, setting, Missing["NotAvailable", setting]]

$defaultRules = TypeTheoryRules["CalculusOfInductiveConstructions"]

rulesSetting[environment_, setting_String] := First[environmentRules[environment]][setting]


TypeTheoryRules /: MakeBoxes[rules : TypeTheoryRules[settings_Association], format : StandardForm | TraditionalForm] /; rulesQ[rules] :=
	BoxForm`ArrangeSummaryBox[
		TypeTheoryRules,
		rules,
		None,
		{BoxForm`SummaryItem[{"Name: ", settings["Name"]}]},
		{
			BoxForm`SummaryItem[{"Prop: ", settings["Prop"]}],
			BoxForm`SummaryItem[{"Rewrite rules: ", settings["RewriteRules"]}]
		},
		format,
		"Interpretable" -> Automatic
	]
