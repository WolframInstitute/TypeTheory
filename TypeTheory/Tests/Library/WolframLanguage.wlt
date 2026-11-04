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
		equalQ[MatchPart[ExpressionNormal[7, {1, 2}], 2, MatchValues], MatchValues[Typed[2, Expressions]]],
		equalQ[MatchPart[ExpressionNormal[7, {1}], 0, MatchValues], MatchValues[Typed[7, Expressions]]],
		equalQ[MatchPart[ExpressionNormal[7, {1}], 5, MatchValues], Typed[EmptyList, Match[Expressions]]]
	},
	{True, True, True},
	TestID -> "The-parts-of-an-expression-are-matches"
]

(* alternatives in order, the first result the one taken, none where nothing matches; bind sequences, guard filters *)
VerificationTest[
	{
		equalQ[MatchFirst[MatchSum[MatchValues[1], MatchValues[2]]], OptionSome[1]],
		equalQ[MatchFirst[MatchSum[Typed[EmptyList, Match[NonNegativeIntegers]], MatchValues[3]]], OptionSome[3]],
		equalQ[MatchFirst[Typed[EmptyList, Match[NonNegativeIntegers]]], Typed[OptionNone, Option[NonNegativeIntegers]]],
		equalQ[MatchBind[{1, 2}, Function[{Typed[x, NonNegativeIntegers]}, {x, x}]], {1, 1, 2, 2}],
		equalQ[Condition[MatchValues[1], "false"], Typed[EmptyList, Match[NonNegativeIntegers]]],
		equalQ[Condition[MatchValues[1], "true"], MatchValues[1]]
	},
	{True, True, True, True, True, True},
	TestID -> "The-match-monad-tries-alternatives-in-order"
]

(* the arguments of an expression are a list; a product pairs every result of one match with every one of another,
   in order *)
VerificationTest[
	{
		equalQ[Arguments[ExpressionNormal[7, {1, 2}]], Typed[{1, 2}, {Expressions}]],
		equalQ[MatchProduct[{1, 2}, {3}], {Pair[1, 3], Pair[2, 3]}]
	},
	{True, True},
	TestID -> "Arguments-are-a-sequence-and-a-product-pairs-results"
]
