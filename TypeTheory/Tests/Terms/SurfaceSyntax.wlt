(* ::Package:: *)

(* Tests for Terms/SurfaceSyntax.wl and Terms/Formatting.wl: held syntax trees, terms that carry their
   environment, reading core terms back for display and exactly, and the notebook display. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

toSyntax = Symbol["WolframInstitute`TypeTheory`PackageScope`toSyntax"]
heldFromSyntax = Symbol["WolframInstitute`TypeTheory`PackageScope`heldFromSyntax"]

prelude = TypeTheoryEnvironment["Prelude"]


VerificationTest[
	heldFromSyntax[toSyntax[ForAll[{Typed[x, NonNegativeIntegers]}, x + 0 == x]]],
	HoldComplete[ForAll[{Typed[x, NonNegativeIntegers]}, x + 0 == x]],
	TestID -> "Syntax-trees-rebuild-the-held-expression"
]

VerificationTest[
	Block[{x = 5}, heldFromSyntax[toSyntax[x + 0 == x]]],
	HoldComplete[x + 0 == x],
	TestID -> "A-symbol-with-a-value-does-not-evaluate"
]

VerificationTest[
	MatchQ[TypeTheoryTerm[ForAll[Typed[x, NonNegativeIntegers], 1 == 1], prelude], TypeTheoryTerm[_ForAll, _TypeTheoryEnvironment]],
	True,
	TestID -> "TypeTheoryTerm-holds-its-term-and-evaluates-its-environment"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Function[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"], Typed[x, A]}, x]]],
	TypeTheoryTerm[ForAll[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"]}, TypeSpecifier[{A} -> A]], TypeTheoryEnvironment[]],
	TestID -> "Types-read-back-with-binder-names-and-implicit-binders"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p]}, h]]],
	TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], TypeTheoryEnvironment[]],
	TestID -> "A-function-type-between-propositions-reads-back-as-Implies"
]

VerificationTest[
	With[{term = TypeTheoryTerm[0 + 1 == 1]}, TypeOf[TypeTheoryTerm[Implies[term, term], prelude]]],
	TypeTheoryTerm[TypeUniverse[0], prelude],
	TestID -> "A-TypeTheoryTerm-inside-a-term-is-spliced-in"
]

VerificationTest[
	Module[{statement = TypeTheoryTerm[2 + 2 == 4]}, TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4], prelude], TypeTheoryTerm[statement]]],
	True,
	TestID -> "A-symbol-whose-value-is-a-TypeTheoryTerm-stands-for-it"
]

VerificationTest[
	Take[Normal[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]], -1],
	{TypeTheoryTheorem[TwoPlusTwo, Construct[Subscript[Equal, 1], NonNegativeIntegers, 2 + 2, 4], Construct[Subscript[EqualityReflexivity, 1], NonNegativeIntegers, 4]]},
	TestID -> "Exact-read-back-writes-every-argument-and-level"
]


(* === display === *)

VerificationTest[
	MatchQ[ToBoxes[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == x, x + 0 == x]], prelude]], InterpretationBox[_, _TypeTheoryTerm]],
	True,
	TestID -> "A-term-displays-in-an-InterpretationBox"
]

VerificationTest[
	FreeQ[ToBoxes[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == x, x + 0 == x]]]], "Typed" | "ForAll" | "Implies"],
	True,
	TestID -> "A-term-displays-in-mathematical-notation"
]

VerificationTest[
	Cases[ToBoxes[TypeTheoryTerm[{TypeUniverse[0], TypeUniverse[1], NonNegativeIntegers}]], "\"Prop\"" | "\"Type\"" | "\"\[DoubleStruckCapitalN]\"", Infinity],
	{"\"Prop\"", "\"Type\"", "\"\[DoubleStruckCapitalN]\""},
	TestID -> "Universes-and-the-natural-numbers-have-their-usual-names"
]

VerificationTest[
	FreeQ[ToBoxes[TypeTheoryTerm[TypeUniverse[u + 2]]], TemplateBox[{"\"(\"", RowBox[{"u", "+", "1"}], "\")\""}, "RowDefault"]],
	False,
	TestID -> "A-universe-at-a-sum-of-levels-shows-the-sum-in-parentheses"
]

VerificationTest[
	MatchQ[ToBoxes[prelude[EqualityCongruence]], InterpretationBox[_GridBox, _TypeTheoryTheorem]],
	True,
	TestID -> "A-declaration-displays-as-a-keyword-a-name-and-a-type"
]
