(* ::Package:: *)

(* Tests for Library/WolframLanguage.wl: the expressions of the Wolfram Language as an inductive type, and the monad of
   pattern matching, the lists of results in the order they are tried, with its operations computing. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

wolfram = TypeTheoryEnvironment["WolframLanguage"]

SetAttributes[equalQ, HoldAll]
equalQ[a_, b_] := DefinitionallyEqualQ[TypeTheoryTerm[a, wolfram], TypeTheoryTerm[b, wolfram]]

VerificationTest[
	{Head[wolfram], MemberQ[Keys[wolfram], Expressions], MemberQ[Keys[wolfram], MatchBind], MemberQ[Keys[wolfram], MatchSum], MemberQ[$ContextPath, "Wolfram`Patterns`"]},
	{TypeTheoryEnvironment, True, True, True, True},
	TestID -> "The-Wolfram-Language-environment-checks"
]

(* the part of an expression at a position: 0 its head, k its k-th argument, no result out of range *)
VerificationTest[
	{
		equalQ[MatchPart["normal"[7, {1, 2}], 2, MatchValues], MatchValues[Typed[2, Expressions]]],
		equalQ[MatchPart["normal"[7, {1}], 0, MatchValues], MatchValues[Typed[7, Expressions]]],
		equalQ[MatchPart["normal"[7, {1}], 5, MatchValues], Typed[{}, Match[Expressions]]]
	},
	{True, True, True},
	TestID -> "The-parts-of-an-expression-are-matches"
]

(* alternatives in order, the first result the one taken, none where nothing matches; bind sequences, guard filters *)
VerificationTest[
	{
		equalQ[MatchFirst[MatchSum[MatchValues[1], MatchValues[2]]], "some"[1]],
		equalQ[MatchFirst[MatchSum[Typed[{}, Match[NonNegativeIntegers]], MatchValues[3]]], "some"[3]],
		equalQ[MatchFirst[Typed[{}, Match[NonNegativeIntegers]]], Typed["none", Option[NonNegativeIntegers]]],
		equalQ[MatchBind[{1, 2}, Function[{Typed[x, NonNegativeIntegers]}, {x, x}]], {1, 1, 2, 2}],
		equalQ[Condition[MatchValues[1], "false"], Typed[{}, Match[NonNegativeIntegers]]],
		equalQ[Condition[MatchValues[1], "true"], MatchValues[1]]
	},
	{True, True, True, True, True, True},
	TestID -> "The-match-monad-tries-alternatives-in-order"
]

(* the arguments of an expression are a list; a product pairs every result of one match with every one of another,
   in order *)
VerificationTest[
	{
		equalQ[Arguments["normal"[7, {1, 2}]], Typed[{1, 2}, {Expressions}]],
		equalQ[MatchProduct[{1, 2}, {3}], {"pair"[1, 3], "pair"[2, 3]}]
	},
	{True, True},
	TestID -> "Arguments-are-a-sequence-and-a-product-pairs-results"
]

(* HoldForm[e] is the expression e quoted: its variables the expressions they stand for, a list of them among the
   arguments joined in, as Sequence @@ l is, and it shows so; a string literal is a constant of Strings, an expression
   where one is expected *)
VerificationTest[
	With[{quoting = TypeTheoryEnvironment[TypeTheoryEnvironment["WolframLanguage"], {TypeTheoryAxiom["Global`f", Atoms], TypeTheoryAxiom["\"abc\"", Strings]}]},
		{
			DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[f[1, 2]], quoting], TypeTheoryTerm["normal"["atom"["Global`f"], {1, 2}], quoting]],
			Head[TypeTheoryCheck[TypeTheoryTerm[{Typed[x, Expressions], Typed[rest, {Expressions}]} |-> HoldForm[f[x, rest, Sequence @@ rest]], quoting]]] === TypeTheoryTerm,
			DefinitionallyEqualQ[
				TypeTheoryTerm[({Typed[x, Expressions], Typed[rest, {Expressions}]} |-> HoldForm[f[x, rest]])[1, {2, 3}], quoting],
				TypeTheoryTerm[HoldForm[f[1, 2, 3]], quoting]
			],
			Cases[ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[(Typed[x, Expressions] |-> HoldForm[f[x]])[2], quoting]]], RowBox[{"\"HoldForm\"", "[", _, "]"}], Infinity] =!= {},
			First[TypeOf[TypeTheoryTerm["abc", quoting]]],
			First[TypeOf[TypeTheoryTerm[Typed["abc", Expressions], quoting]]],
			First[TypeTheoryCheck[TypeTheoryTerm[HoldForm[g[1]], quoting]]]
		}
	],
	{True, True, True, True, Strings, Expressions, "ElaborationFailed"},
	TestID -> "HoldForm-quotes-an-expression-and-a-string-literal-is-a-constant-of-Strings"
]
