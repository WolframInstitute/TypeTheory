(* ::Package:: *)

(* The two kernels on records changed one at a time, for scripts/kernel_agreement_fuzz.wls and the sample of it the
   suite runs (Tests/Checking/Queries.wlt). An environment has one record changed: a subterm of its type, of its value
   or of a rule replaced by a subterm of another record; a number it holds changed by one or set to 0; a flag turned; a
   key dropped; or its registration of the natural numbers changed, a role dropped or two roles swapped.
   TypeTheoryCheck checks the changed environment with Method Automatic, which is the compiled kernel and the replay
   of every record where the paclet has its library, and with Method -> "Symbolic", the kernel of TypeChecking.wl: the
   two must accept or refuse each change alike. A value is replaced in its place, since records are compared with the
   order of their keys. *)

BeginPackage["KernelAgreement`"]

kernelAgreement::usage = "kernelAgreement[environment, count, seed] changes count records of environment one at a time, drawn with \
SeedRandom[seed], and gives for each an association of the record's name and kind, the change, whether it left the environment as it \
was, and the verdicts of TypeTheoryCheck with Method Automatic and with Method -> \"Symbolic\"."
agreementClass::usage = "agreementClass[verdict] gives \"accepted\" for the verdict \"accepted\" and \"refused\" for a failure's tag."
agreementDisagreements::usage = "agreementDisagreements[results] gives the results of kernelAgreement whose two verdicts are of different classes."

Begin["`Private`"]

scoped[name_String] := Symbol["WolframInstitute`TypeTheory`PackageScope`" <> name]

$termHeads := scoped /@ {"application", "lambdaAbstraction", "dependentFunctionType", "constantReference", "boundVariable", "universeSort", "naturalLiteral", "localDefinition", "projection"}

termQ[term_] := MemberQ[$termHeads, Head[term]]

(* a copy of the environment's store with its records or its registration changed by hand *)
forged[WolframInstitute`TypeTheory`TypeTheoryEnvironment[store_Symbol], key_String, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy[key] = change[copy[key]];
	WolframInstitute`TypeTheory`TypeTheoryEnvironment[copy]
]

(* the positions of the terms inside a term, itself first *)
termPositions[term_] := Position[term, _?termQ, {0, Infinity}, Heads -> False]

(* a term with one of its subterms replaced by a subterm from the pool *)
subtermChanged[pool_][term_] := ReplacePart[term, RandomChoice[termPositions[term]] -> RandomChoice[pool]]

(* the changes a record admits, each {description, function of the record} *)
recordChanges[pool_, record_] := Join[
	Function[key, {{"a subterm of", key}, Function[old, Association[old, key -> subtermChanged[pool][old[key]]]]}] /@
		Select[{"Type", "Value"}, Function[key, KeyExistsQ[record, key] && termQ[record[key]]]],
	If[ AssociationQ[Lookup[record, "Rules", None]] && Length[record["Rules"]] > 0,
		{{{"a subterm of a rule"}, Function[old, With[{which = RandomInteger[{1, Length[old["Rules"]]}]},
			Association[old, "Rules" -> MapAt[Function[rule, Association[rule, "RightHandSide" -> subtermChanged[pool][rule["RightHandSide"]]]], old["Rules"], which]]
		]]}},
		{}
	],
	Function[key, {{"the number", key}, Function[old, Association[old, key -> RandomChoice[{old[key] + 1, Max[old[key] - 1, 0], 0}]]]}] /@ Keys[Select[record, IntegerQ]],
	Function[key, {{"the flag", key}, Function[old, Association[old, key -> ! old[key]]]}] /@ Keys[Select[record, BooleanQ]],
	Function[key, {{"without", key}, Function[old, KeyDrop[old, key]]}] /@ Keys[record]
]

(* the changes a registration of the natural numbers admits: a role dropped, two roles swapped *)
registrationChanges[settings_Association] /; AssociationQ[Lookup[settings, "Roles", None]] && Length[settings["Roles"]] >= 2 := {
	{{"a registration without a role"}, Function[old, Association[old, "Roles" -> KeyDrop[old["Roles"], RandomChoice[Keys[old["Roles"]]]]]]},
	{{"a registration with two roles swapped"}, Function[old, With[{two = RandomSample[Keys[old["Roles"]], 2]},
		Association[old, "Roles" -> Association[old["Roles"], First[two] -> old["Roles"][Last[two]], Last[two] -> old["Roles"][First[two]]]]
	]]}
}
registrationChanges[_] := {}

verdict[result_] := Which[MatchQ[result, _Success], "accepted", FailureQ[result], result["Tag"], True, "neither"]

agreementClass[verdict_String] := If[verdict === "accepted", "accepted", "refused"]

agreementDisagreements[results_List] := Select[results, Function[result, agreementClass[result["Automatic"]] =!= agreementClass[result["Symbolic"]]]]

kernelAgreement[environment : WolframInstitute`TypeTheory`TypeTheoryEnvironment[store_Symbol], count_Integer, seed_Integer] := With[
	{
		records = store["Records"],
		registration = registrationChanges[store["NaturalNumbers"]]
	},
	With[
		{
			names = Keys[records],
			(* every subterm of every type and value, to replace with *)
			pool = DeleteDuplicates[Catenate[Function[record, Catenate[Function[term, Extract[term, termPositions[term]]] /@ Cases[Lookup[record, {"Type", "Value"}], _?termQ]]] /@ Values[records]]]
		},
		BlockRandom[
			SeedRandom[seed];
			Table[
				If[ registration =!= {} && RandomInteger[{1, 25}] == 1,
					With[{change = RandomChoice[registration]},
						changeVerdicts[environment, "the registration", "NaturalNumbers", First[change], forged[environment, "NaturalNumbers", Last[change]]]
					],
					With[{name = RandomChoice[names]},
						With[{change = RandomChoice[recordChanges[pool, records[name]]]},
							changeVerdicts[environment, name, records[name]["Kind"], First[change], forged[environment, "Records", Function[old, MapAt[Last[change], old, Key[name]]]]]
						]
					]
				],
				{count}
			]
		]
	]
]

changeVerdicts[WolframInstitute`TypeTheory`TypeTheoryEnvironment[store_Symbol], name_, kind_, change_, changed : WolframInstitute`TypeTheory`TypeTheoryEnvironment[copy_Symbol]] := <|
	"Name" -> name,
	"Kind" -> kind,
	"Change" -> change,
	"Unchanged" -> ({copy["Records"], copy["NaturalNumbers"]} === {store["Records"], store["NaturalNumbers"]}),
	"Automatic" -> verdict[WolframInstitute`TypeTheory`TypeTheoryCheck[changed]],
	"Symbolic" -> verdict[WolframInstitute`TypeTheory`TypeTheoryCheck[changed, Method -> "Symbolic"]]
|>

End[]

EndPackage[]
