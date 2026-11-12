(* ::Package:: *)

(* Tests for rewrite rules: declared only where the rules allow them, checked, used by computation and
   definitional equality, read back by Normal and replayed by TypeTheoryCheck. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

bits = TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True], {
	TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
	TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
	TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
	TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero],
	TypeTheoryAxiom[Twice, TypeSpecifier[{TypeSpecifier[{Bit} -> Bit], Bit} -> Bit]],
	TypeTheoryRewriteRule[TwiceRule, ForAll[{Typed[h, TypeSpecifier[{Bit} -> Bit]], Typed[x, Bit]}, Twice[h, x] -> h[h[x]]]]
}]


VerificationTest[
	First @ TypeTheoryEnvironment[TypeTheoryEnvironment[], {
		TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
		TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
		TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne]
	}],
	"RewriteRulesNotAllowed",
	TestID -> "Rewrite-rules-need-rules-that-allow-them"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Flip[Flip[BitZero]], bits]],
		WeakHeadNormalForm[TypeTheoryTerm[Twice[Flip, BitOne], bits]],
		DefinitionallyEqualQ[TypeTheoryTerm[Twice[Flip, BitZero], bits], TypeTheoryTerm[BitZero, bits]]
	},
	{TypeTheoryTerm[BitZero, bits], TypeTheoryTerm[BitOne, bits], True},
	TestID -> "An-axiom-computes-by-its-rewrite-rules"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[b, Bit]}, Flip[b]], bits]],
	TypeTheoryTerm[Function[{Typed[b, Bit]}, Flip[b]], bits],
	TestID -> "An-axiom-applied-to-a-variable-stays"
]

VerificationTest[
	{MatchQ[TypeTheoryCheck[bits], _Success], Last[Normal[bits]], Information[bits, "RewriteRules"]},
	{
		True,
		TypeTheoryRewriteRule[TwiceRule, ForAll[{Typed[h, Bit -> Bit], Typed[x, Bit]}, Twice[h, x] -> h[h[x]]]],
		{FlipZero, FlipOne, TwiceRule}
	},
	TestID -> "Rewrite-rules-are-replayed-and-read-back"
]

VerificationTest[
	First /@ {
		TypeTheoryType[TypeTheoryTerm[Flip[FlipZero], bits]],
		TypeTheoryEnvironment[bits, {TypeTheoryRewriteRule[Bad, BitZero -> BitOne]}],
		TypeTheoryEnvironment[bits, {TypeTheoryRewriteRule[Bad, ForAll[{Typed[x, Bit]}, Flip[BitZero] -> x]]}],
		TypeTheoryEnvironment[bits, {TypeTheoryRewriteRule[Bad, Flip[BitZero] -> Bit]}]
	},
	{"ElaborationFailed", "RewriteRuleHead", "RewriteRuleVariable", "TypeMismatch"},
	TestID -> "A-rewrite-rule-is-not-a-term-and-must-be-a-well-typed-pattern"
]


(* === the keys of a store made from its records === *)

(* A store's names, rewrite-rule index, overload index, library and content hash are made from its records and its
   base. Each forged in a copy of the store is refused by TypeTheoryCheck with both methods, which compare them with
   the ones the replay makes: in an environment with rewrite rules, which the kernel of TypeChecking.wl checks, and in
   one of the prelude, which the compiled kernel takes. *)
keepBits = TypeTheoryEnvironment[bits, {TypeTheoryAxiom[Keep, TypeSpecifier[{Bit} -> Bit]]}]

honestPrelude = TypeTheoryEnvironment[TypeTheoryEnvironment["Prelude"], {TypeTheoryAxiom["assumed", 1 + 1 == 2]}]

storeKeyForged[TypeTheoryEnvironment[store_Symbol], key_String, value_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy[key] = value;
	TypeTheoryEnvironment[copy]
]

filedUnderKeep = Append[First[keepBits]["RewriteRuleIndex"], HoldComplete[Keep] -> {HoldComplete[FlipZero]}]

(* each forgery {key, how} -> the forged value; an index that is empty is not emptied, which would change nothing *)
derivedKeyForgeries[environment_, library_, operation_, constant_] := DeleteCases[
	{
		{"Names", "a name left out"} -> Most[First[environment]["Names"]],
		{"RewriteRuleIndex", "a constant filed as a rule of another"} -> Append[First[environment]["RewriteRuleIndex"], operation -> {constant}],
		{"RewriteRuleIndex", "emptied"} -> <||>,
		{"OverloadIndex", "a constant overloading an operation it was not declared to"} -> Append[Replace[First[environment]["OverloadIndex"], Except[_Association] -> <||>], operation -> {constant}],
		{"Library", "a library whose records are not the first"} -> library,
		{"ContentHash", "the hash of other contents"} -> StringRepeat["0", 64]
	},
	{"RewriteRuleIndex", "emptied"} -> <||> /; First[environment]["RewriteRuleIndex"] === <||>
]

checkVerdict[result_] := If[MatchQ[result, _Success], "accepted", Replace[result, failure_Failure :> failure["Tag"]]]

bothMethods[environment_] := Function[method, checkVerdict[TypeTheoryCheck[environment, Method -> method]]] /@ {Automatic, "Symbolic"}

VerificationTest[
	Function[{environment, forgeries},
		{
			bothMethods[environment],
			Function[forgery, First[forgery] -> bothMethods[storeKeyForged[environment, First[First[forgery]], Last[forgery]]]] /@ forgeries
		}
	] @@@ {
		{keepBits, derivedKeyForgeries[keepBits, First[TypeTheoryEnvironment["Prelude"]], HoldComplete[Keep], HoldComplete[FlipZero]]},
		{honestPrelude, derivedKeyForgeries[honestPrelude, First[TypeTheoryEnvironment["Integers"]], HoldComplete[Plus], HoldComplete["assumed"]]}
	},
	With[{refused = {"DeclarationMismatch", "DeclarationMismatch"}},
		{
			{
				{"accepted", "accepted"},
				{
					{"Names", "a name left out"} -> refused,
					{"RewriteRuleIndex", "a constant filed as a rule of another"} -> refused,
					{"RewriteRuleIndex", "emptied"} -> refused,
					{"OverloadIndex", "a constant overloading an operation it was not declared to"} -> refused,
					{"Library", "a library whose records are not the first"} -> refused,
					{"ContentHash", "the hash of other contents"} -> refused
				}
			},
			{
				{"accepted", "accepted"},
				{
					{"Names", "a name left out"} -> refused,
					{"RewriteRuleIndex", "a constant filed as a rule of another"} -> refused,
					{"OverloadIndex", "a constant overloading an operation it was not declared to"} -> refused,
					{"Library", "a library whose records are not the first"} -> refused,
					{"ContentHash", "the hash of other contents"} -> refused
				}
			}
		}
	],
	TestID -> "Every-key-a-store-makes-from-its-records-forged-is-refused-by-both-methods"
]

(* The kernel takes a rule only for the constant its left side's head names: with Flip's rule filed under Keep in a copy
   of the store, and nothing checked, Keep[BitZero] does not compute and Flip[BitZero] still does. *)
VerificationTest[
	With[{filed = storeKeyForged[keepBits, "RewriteRuleIndex", filedUnderKeep]},
		{
			DefinitionallyEqualQ[TypeTheoryTerm[Keep[BitZero], filed], TypeTheoryTerm[BitOne, filed]],
			DefinitionallyEqualQ[TypeTheoryTerm[Flip[BitZero], filed], TypeTheoryTerm[BitOne, filed]]
		}
	],
	{False, True},
	TestID -> "A-rule-reduces-only-the-constant-its-left-side-names"
]

(* A file's rewrite-rule index is not read: the store makes it from the records. A file whose index files Flip's rule
   under Keep reads back, checked, as the environment it was saved from. *)
VerificationTest[
	Module[{directory = CreateDirectory[], saved, forged, loaded, result},
		saved = FileNameJoin[{directory, "keep.wxf"}];
		forged = FileNameJoin[{directory, "forgedIndex.wxf"}];
		Export[saved, keepBits];
		With[{data = First[BinaryDeserialize[ReadByteArray[saved], HoldComplete]]},
			BinaryWrite[forged, BinarySerialize[Association[data, "RewriteRuleIndex" -> filedUnderKeep]]];
			Close[forged]
		];
		loaded = TypeTheoryEnvironment[File[forged], "Check" -> True];
		result = {
			Information[loaded, "Provenance"]["Checked"],
			First[loaded]["RewriteRuleIndex"] === First[keepBits]["RewriteRuleIndex"],
			DefinitionallyEqualQ[TypeTheoryTerm[Keep[BitZero], loaded], TypeTheoryTerm[BitOne, loaded]]
		};
		DeleteDirectory[directory, DeleteContents -> True];
		result
	],
	{True, True, False},
	TestID -> "A-files-rewrite-rule-index-is-not-read-the-store-makes-it-from-the-records"
]
