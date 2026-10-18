(* ::Package:: *)

(* Tests for Terms/CoreTerms.wl: de Bruijn substitution and abstraction, and universe levels.
   Run with: TestReport["TypeTheory/Tests/Terms/CoreTerms.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

$scope = "WolframInstitute`TypeTheory`PackageScope`"
scoped[name_String] := Symbol[$scope <> name]

boundVariable = scoped["boundVariable"]
freeVariable = scoped["freeVariable"]
application = scoped["application"]
lambdaAbstraction = scoped["lambdaAbstraction"]
universeSort = scoped["universeSort"]
levelParameter = scoped["levelParameter"]
levelSuccessor = scoped["levelSuccessor"]
levelMaximum = scoped["levelMaximum"]
levelImpredicativeMaximum = scoped["levelImpredicativeMaximum"]
normalizeLevel = scoped["normalizeLevel"]
levelLessEqualQ = scoped["levelLessEqualQ"]
instantiateBoundVariable = scoped["instantiateBoundVariable"]
abstractFreeVariable = scoped["abstractFreeVariable"]
betaNormalize = scoped["betaNormalize"]

u = levelParameter[HoldComplete[\[FormalU]]]
v = levelParameter[HoldComplete[\[FormalV]]]


(* === substitution === *)

VerificationTest[
	instantiateBoundVariable[application[boundVariable[0], boundVariable[1]], freeVariable[7]],
	application[freeVariable[7], boundVariable[0]],
	TestID -> "Instantiating-the-outer-variable-lowers-the-others"
]

VerificationTest[
	instantiateBoundVariable[lambdaAbstraction[HoldComplete[\[FormalX]], universeSort[0], application[boundVariable[1], boundVariable[0]], "Explicit"], boundVariable[3]],
	lambdaAbstraction[HoldComplete[\[FormalX]], universeSort[0], application[boundVariable[4], boundVariable[0]], "Explicit"],
	TestID -> "Substitution-under-a-binder-lifts-the-value"
]

VerificationTest[
	abstractFreeVariable[lambdaAbstraction[HoldComplete[\[FormalX]], universeSort[0], application[freeVariable[5], boundVariable[0]], "Explicit"], 5],
	lambdaAbstraction[HoldComplete[\[FormalX]], universeSort[0], application[boundVariable[1], boundVariable[0]], "Explicit"],
	TestID -> "Abstraction-counts-the-binders-it-passes"
]

VerificationTest[
	betaNormalize[application[lambdaAbstraction[HoldComplete[\[FormalX]], universeSort[1], boundVariable[0], "Explicit"], universeSort[0]]],
	universeSort[0],
	TestID -> "Beta-normalization-reduces-an-applied-function"
]


(* === universe levels === *)

VerificationTest[
	normalizeLevel[levelMaximum[levelSuccessor[u, 1], u, 0]],
	levelSuccessor[u, 1],
	TestID -> "Maximum-keeps-the-largest-offset-of-a-parameter"
]

VerificationTest[
	{normalizeLevel[levelImpredicativeMaximum[u, 0]], normalizeLevel[levelImpredicativeMaximum[u, 1]], normalizeLevel[levelImpredicativeMaximum[u, levelSuccessor[v, 1]]]},
	{0, levelMaximum[1, u], levelMaximum[u, levelSuccessor[v, 1]]},
	TestID -> "Impredicative-maximum-is-zero-into-Prop-and-the-maximum-otherwise"
]

VerificationTest[
	normalizeLevel[levelImpredicativeMaximum[u, v]],
	levelImpredicativeMaximum[u, v],
	TestID -> "Impredicative-maximum-of-two-parameters-stays"
]

VerificationTest[
	{levelLessEqualQ[u, levelSuccessor[u, 1]], levelLessEqualQ[levelSuccessor[u, 1], u], levelLessEqualQ[1, levelMaximum[u, 1]], levelLessEqualQ[u, v]},
	{True, False, True, False},
	TestID -> "Level-comparison-holds-for-every-value-of-the-parameters"
]
