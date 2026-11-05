(* ::Package::"Tags"-><|"BadSymbol" -> <|"Match" -> <|Enabled -> False|>|>|>:: *)

(* Tests for Library/WolframLanguage.wl: the expressions of the Wolfram Language as an inductive type, and the monad of
   pattern matching, the lists of results in the order they are tried, with its operations computing. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

wolfram = TypeTheoryEnvironment["WolframLanguage"]

SetAttributes[equalQ, HoldAll]
equalQ[a_, b_] := DefinitionallyEqualQ[TypeTheoryTerm[a, wolfram], TypeTheoryTerm[b, wolfram]]

VerificationTest[
	{Head[wolfram], MemberQ[Keys[wolfram], Expressions], MemberQ[Keys[wolfram], MatchBind], MemberQ[Keys[wolfram], MatchSum], Context[MatchValue]},
	{TypeTheoryEnvironment, True, True, True, "WolframInstitute`TypeTheory`"},
	TestID -> "The-Wolfram-Language-environment-checks"
]

(* the part of an expression at a position: 0 its head, k its k-th argument, no result out of range *)
VerificationTest[
	{
		equalQ[MatchPart["normal"[7, {1, 2}], 2, MatchValue], MatchValue[Typed[2, Expressions]]],
		equalQ[MatchPart["normal"[7, {1}], 0, MatchValue], MatchValue[Typed[7, Expressions]]],
		equalQ[MatchPart["normal"[7, {1}], 5, MatchValue], Typed[{}, Match[Expressions]]]
	},
	{True, True, True},
	TestID -> "The-parts-of-an-expression-are-matches"
]

(* alternatives in order, the first result the one taken, none where nothing matches; bind sequences, guard filters *)
VerificationTest[
	{
		equalQ[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], "some"[1]],
		equalQ[MatchFirst[MatchSum[Typed[{}, Match[NonNegativeIntegers]], MatchValue[3]]], "some"[3]],
		equalQ[MatchFirst[Typed[{}, Match[NonNegativeIntegers]]], Typed["none", Option[NonNegativeIntegers]]],
		equalQ[MatchBind[{1, 2}, Function[{Typed[x, NonNegativeIntegers]}, {x, x}]], {1, 1, 2, 2}],
		equalQ[Condition[MatchValue[1], "false"], Typed[{}, Match[NonNegativeIntegers]]],
		equalQ[Condition[MatchValue[1], "true"], MatchValue[1]]
	},
	{True, True, True, True, True, True},
	TestID -> "The-match-monad-tries-alternatives-in-order"
]

(* the arguments of an expression are a list; a value is one result, a sequence of values is one result written
   MatchValue[Sequence[...]], and several results are a sum *)
VerificationTest[
	{
		equalQ[Arguments["normal"[7, {1, 2}]], Typed[{1, 2}, {Expressions}]],
		TypeTheoryType[MatchValue[Sequence[1, "true"]], wolfram] === TypeTheoryTerm[Match[Sequence[NonNegativeIntegers, Booleans]], wolfram],
		equalQ[MatchFirst[MatchValue[Sequence[1, "true"]]], "some"[Sequence[1, "true"]]],
		equalQ[MatchSum[MatchValue[1], MatchValue[2]], {1, 2}]
	},
	{True, True, True, True},
	TestID -> "A-value-is-one-result-a-sequence-is-one-result-and-several-are-a-sum"
]

(* HoldForm[e] is the expression e quoted: its variables the expressions they stand for, a list of them among the
   arguments joined in, as Sequence @@ l is, and it shows so; a symbol is an atom by its name, which nothing declares; a
   string literal is a string, the list of its character codes, and an expression where one is expected; where an
   expression is expected, a symbol that names nothing stands for itself *)
VerificationTest[
	With[{quoting = TypeTheoryEnvironment["WolframLanguage"]},
		{
			DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[f[1, 2]], quoting], TypeTheoryTerm["normal"["atom"["symbolAtom"["Global`f"]], {1, 2}], quoting]],
			Head[TypeTheoryType[TypeTheoryTerm[{Typed[x, Expressions], Typed[rest, {Expressions}]} |-> HoldForm[f[x, rest, Sequence @@ rest]], quoting]]] === TypeTheoryTerm,
			DefinitionallyEqualQ[
				TypeTheoryTerm[({Typed[x, Expressions], Typed[rest, {Expressions}]} |-> HoldForm[f[x, rest]])[1, {2, 3}], quoting],
				TypeTheoryTerm[HoldForm[f[1, 2, 3]], quoting]
			],
			Cases[ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[(Typed[x, Expressions] |-> HoldForm[f[x]])[2], quoting]]], RowBox[{"\"HoldForm\"", "[", _, "]"}], Infinity] =!= {},
			First[TypeTheoryType[TypeTheoryTerm["abc", quoting]]],
			First[TypeTheoryType[TypeTheoryTerm[Typed["abc", Expressions], quoting]]],
			First[TypeTheoryType[TypeTheoryTerm[HoldForm[g[1]], quoting]]],
			DefinitionallyEqualQ[TypeTheoryTerm["abc", quoting], TypeTheoryTerm["string"[{97, 98, 99}], quoting]],
			DefinitionallyEqualQ[TypeTheoryTerm[Typed[g[1 + 1], Expressions], quoting], TypeTheoryTerm[HoldForm[g[2]], quoting]]
		}
	],
	{True, True, True, True, Strings, Expressions, Expressions, True, True},
	TestID -> "HoldForm-quotes-an-expression-and-a-string-literal-is-a-string"
]

(* rules written as a term are a function from an expression to its matches, and Replace, ReplaceList, ReplaceAll and
   ReplaceRepeated rewrite with them in the kernel, as the Wolfram Language does: an expression where one is expected
   needs no HoldForm, a symbol that names nothing standing for itself *)
VerificationTest[
	{
		equalQ[Replace[f[1, 2], f[x_, y_] :> {y, x}], HoldForm[{2, 1}]],
		equalQ[Replace[g[1, 2], f[x_, y_] :> {y, x}], HoldForm[g[1, 2]]],
		equalQ[Replace[h[1, "s"], {h[x_Integer, y_String] :> y, h[x_, y_] :> x}], HoldForm["s"]],
		equalQ[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], {HoldForm[{{1}, {2, 3}}], HoldForm[{{1, 2}, {3}}]}],
		equalQ[ReplaceAll[f[a, g[a]], a -> b], HoldForm[f[b, g[b]]]],
		equalQ[ReplaceRepeated[f[f[f[x]]], f[y_] :> y], HoldForm[x]],
		equalQ[SameQ[HoldForm[f[1, "a"]], HoldForm[f[1, "a"]]], "true"],
		equalQ[SameQ[HoldForm[f[1]], HoldForm[f[-1]]], "false"]
	},
	ConstantArray[True, 8],
	TestID -> "Replace-ReplaceList-ReplaceAll-and-ReplaceRepeated-rewrite-in-the-kernel"
]
