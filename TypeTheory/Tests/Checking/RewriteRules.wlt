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
		TypeTheoryRewriteRule[TwiceRule, ForAll[{Typed[h, TypeSpecifier[{Bit} -> Bit]], Typed[x, Bit]}, Twice[h, x] -> h[h[x]]]],
		{FlipZero, FlipOne, TwiceRule}
	},
	TestID -> "Rewrite-rules-are-replayed-and-read-back"
]

VerificationTest[
	First /@ {
		TypeTheoryCheck[TypeTheoryTerm[Flip[FlipZero], bits]],
		TypeTheoryEnvironment[bits, {TypeTheoryRewriteRule[Bad, BitZero -> BitOne]}],
		TypeTheoryEnvironment[bits, {TypeTheoryRewriteRule[Bad, ForAll[{Typed[x, Bit]}, Flip[BitZero] -> x]]}],
		TypeTheoryEnvironment[bits, {TypeTheoryRewriteRule[Bad, Flip[BitZero] -> Bit]}]
	},
	{"ElaborationFailed", "RewriteRuleHead", "RewriteRuleVariable", "TypeMismatch"},
	TestID -> "A-rewrite-rule-is-not-a-term-and-must-be-a-well-typed-pattern"
]
