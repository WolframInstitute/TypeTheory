(* ::Package:: *)

(* Tests for Library/WolframLanguage.wl: the expressions of the Wolfram Language as an inductive type, and the monad of
   pattern matching, the lists of results in the order they are tried, with its operations computing. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

wolfram = TypeTheoryEnvironment["WolframLanguage"]

SetAttributes[equalQ, HoldAll]
equalQ[a_, b_] := DefinitionallyEqualQ[TypeTheoryTerm[a, wolfram], TypeTheoryTerm[b, wolfram]]

VerificationTest[
	{Head[wolfram], MemberQ[Keys[wolfram], "Expressions"], MemberQ[Keys[wolfram], "matchBind"]},
	{TypeTheoryEnvironment, True, True},
	TestID -> "The-Wolfram-Language-environment-checks"
]

(* the part of an expression at a position: 0 its head, k its k-th argument, no result out of range *)
VerificationTest[
	{
		equalQ["matchPart"["expressionNormal"["expressionAtom"["atomOfNatural"[7]], {"expressionAtom"["atomOfNatural"[1]], "expressionAtom"["atomOfNatural"[2]]}], 2], "matchPure"["expressionAtom"["atomOfNatural"[2]]]],
		equalQ["matchPart"["expressionNormal"["expressionAtom"["atomOfNatural"[7]], {"expressionAtom"["atomOfNatural"[1]]}], 0], "matchPure"["expressionAtom"["atomOfNatural"[7]]]],
		equalQ["matchPart"["expressionNormal"["expressionAtom"["atomOfNatural"[7]], {"expressionAtom"["atomOfNatural"[1]]}], 5], Typed["matchFailure", "Match"["Expressions"]]]
	},
	{True, True, True},
	TestID -> "The-parts-of-an-expression-are-matches"
]

(* alternatives in order, the first result the one taken, none where nothing matches; bind sequences, guard filters *)
VerificationTest[
	{
		equalQ["matchFirst"["matchAlternative"["matchPure"[1], "matchPure"[2]]], OptionSome[1]],
		equalQ["matchFirst"["matchAlternative"[Typed["matchFailure", "Match"[NonNegativeIntegers]], "matchPure"[3]]], OptionSome[3]],
		equalQ["matchFirst"[Typed["matchFailure", "Match"[NonNegativeIntegers]]], Typed[OptionNone, Option[NonNegativeIntegers]]],
		equalQ["matchBind"[{1, 2}, Function[{Typed[x, NonNegativeIntegers]}, {x, x}]], {1, 1, 2, 2}],
		equalQ["matchGuard"["false", "matchPure"[1]], Typed["matchFailure", "Match"[NonNegativeIntegers]]],
		equalQ["matchGuard"["true", "matchPure"[1]], "matchPure"[1]]
	},
	{True, True, True, True, True, True},
	TestID -> "The-match-monad-tries-alternatives-in-order"
]
