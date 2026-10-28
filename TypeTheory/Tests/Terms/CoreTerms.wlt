(* ::Package:: *)

(* Tests for Terms/CoreTerms.wl: de Bruijn substitution and abstraction, and universe levels.
   Run with: TestReport["TypeTheory/Tests/Terms/CoreTerms.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

$scope = "WolframInstitute`TypeTheory`PackageScope`"
scoped[name_String] := Symbol[$scope <> name]

boundVariable = scoped["boundVariable"]
freeVariable = scoped["freeVariable"]
(* the composite heads hold their parts, so a term written here is built from its parts computed first *)
application[parts___] := Construct[scoped["application"], parts]
lambdaAbstraction[parts___] := Construct[scoped["lambdaAbstraction"], parts]
universeSort = scoped["universeSort"]
levelParameter = scoped["levelParameter"]
levelSuccessor = scoped["levelSuccessor"]
levelMaximum = scoped["levelMaximum"]
levelImpredicativeMaximum = scoped["levelImpredicativeMaximum"]
normalizeLevel = scoped["normalizeLevel"]
levelLessEqualQ = scoped["levelLessEqualQ"]
instantiateBoundVariable = scoped["instantiateBoundVariable"]
instantiateBoundVariables = scoped["instantiateBoundVariables"]
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

(* under a binder, a value is lifted past it, and a variable bound further out is lowered by the number of values *)
VerificationTest[
	With[
		{
			body = application[application[boundVariable[0], boundVariable[1]], lambdaAbstraction[HoldComplete[x], universeSort[0], application[boundVariable[3], application[boundVariable[1], boundVariable[0]]], "Explicit"]],
			values = {application[freeVariable[1], boundVariable[0]], freeVariable[2]}
		},
		instantiateBoundVariables[body, values] === instantiateBoundVariable[instantiateBoundVariable[body, Last[values]], First[values]]
	],
	True,
	TestID -> "Instantiating-several-variables-at-once-is-instantiating-them-in-turn"
]

VerificationTest[
	instantiateBoundVariable[lambdaAbstraction[HoldComplete[\[FormalX]], universeSort[0], application[boundVariable[1], boundVariable[0]], "Explicit"], boundVariable[3]],
	lambdaAbstraction[HoldComplete[\[FormalX]], universeSort[0], application[boundVariable[4], boundVariable[0]], "Explicit"],
	TestID -> "Substitution-under-a-binder-lifts-the-value"
]

(* Substitution decides what the kernel accepts, so it is checked against a plain walk on random terms: binders,
   local definitions, projections and applications over bound, loose and free variables, instantiated with one
   to three values that have loose variables of their own. The body can be a single variable, and variables
   bound further out than the values are lowered. The walk lifts a value past each binder it goes under. *)
naiveLift[term_, amount_, cutoff_] := Replace[term, {
	boundVariable[index_] :> boundVariable[If[index >= cutoff, index + amount, index]],
	scoped["application"][function_, argument_] :> Construct[scoped["application"], naiveLift[function, amount, cutoff], naiveLift[argument, amount, cutoff]],
	(head : scoped["lambdaAbstraction"] | scoped["dependentFunctionType"])[name_, domain_, body_, binder_] :>
		Construct[head, name, naiveLift[domain, amount, cutoff], naiveLift[body, amount, cutoff + 1], binder],
	scoped["localDefinition"][name_, type_, value_, body_] :>
		Construct[scoped["localDefinition"], name, naiveLift[type, amount, cutoff], naiveLift[value, amount, cutoff], naiveLift[body, amount, cutoff + 1]],
	scoped["projection"][structure_, index_, structureTerm_] :> Construct[scoped["projection"], structure, index, naiveLift[structureTerm, amount, cutoff]]
}]
naiveSubstitute[term_, values_, depth_] := Replace[term, {
	boundVariable[index_] :> Which[
		index < depth, boundVariable[index],
		index < depth + Length[values], naiveLift[values[[index - depth + 1]], depth, 0],
		True, boundVariable[index - Length[values]]
	],
	scoped["application"][function_, argument_] :> Construct[scoped["application"], naiveSubstitute[function, values, depth], naiveSubstitute[argument, values, depth]],
	(head : scoped["lambdaAbstraction"] | scoped["dependentFunctionType"])[name_, domain_, body_, binder_] :>
		Construct[head, name, naiveSubstitute[domain, values, depth], naiveSubstitute[body, values, depth + 1], binder],
	scoped["localDefinition"][name_, type_, value_, body_] :>
		Construct[scoped["localDefinition"], name, naiveSubstitute[type, values, depth], naiveSubstitute[value, values, depth], naiveSubstitute[body, values, depth + 1]],
	scoped["projection"][structure_, index_, structureTerm_] :> Construct[scoped["projection"], structure, index, naiveSubstitute[structureTerm, values, depth]]
}]
randomTerm[0] := Switch[RandomInteger[{1, 4}],
	1, boundVariable[RandomInteger[5]],
	2, freeVariable[RandomInteger[9]],
	3, scoped["constantReference"][HoldComplete[c], {}],
	_, universeSort[0]
]
randomTerm[n_] := Switch[RandomInteger[{1, 6}],
	1, application[randomTerm[n - 1], randomTerm[n - 1]],
	2, lambdaAbstraction[HoldComplete[x], randomTerm[n - 1], randomTerm[n - 1], "Explicit"],
	3, Construct[scoped["dependentFunctionType"], HoldComplete[x], randomTerm[n - 1], randomTerm[n - 1], "Explicit"],
	4, Construct[scoped["localDefinition"], HoldComplete[y], randomTerm[n - 1], randomTerm[n - 1], randomTerm[n - 1]],
	5, Construct[scoped["projection"], HoldComplete[S], 0, randomTerm[n - 1]],
	_, randomTerm[0]
]

VerificationTest[
	BlockRandom[
		SeedRandom[2026];
		Select[
			Table[{randomTerm[RandomInteger[{0, 4}]], Table[randomTerm[RandomInteger[2]], {RandomInteger[{1, 3}]}]}, {1000}],
			Function[case, instantiateBoundVariables @@ case =!= naiveSubstitute[First[case], Reverse[Last[case]], 0]]
		]
	],
	{},
	TestID -> "Substitution-agrees-with-a-plain-walk-on-random-terms"
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
