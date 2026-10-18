(* ::Package:: *)

(* Tests for Terms/SurfaceSyntax.wl and Terms/Formatting.wl: held syntax trees, reading core terms back
   as surface terms, and the notebook display. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

toSyntax = Symbol["WolframInstitute`TypeTheory`PackageScope`toSyntax"]
heldFromSyntax = Symbol["WolframInstitute`TypeTheory`PackageScope`heldFromSyntax"]


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
	TypeTheoryTerm[ForAll[Typed[x, NonNegativeIntegers], 1 == 1]],
	TypeTheoryTerm[ForAll[Typed[x, NonNegativeIntegers], 1 == 1]],
	SameTest -> MatchQ,
	TestID -> "TypeTheoryTerm-holds-its-term"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Function[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"], Typed[x, A]}, x]]],
	TypeTheoryTerm[ForAll[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"]}, TypeSpecifier[{A} -> A]]],
	TestID -> "Types-read-back-with-binder-names-and-implicit-binders"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p]}, h]]],
	TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]]],
	TestID -> "A-function-type-between-propositions-reads-back-as-Implies"
]

VerificationTest[
	With[{term = TypeTheoryTerm[0 + 1 == 1]}, TypeOf[TypeTheoryTerm[Implies[term, term]]]],
	TypeTheoryTerm[TypeUniverse[0]],
	TestID -> "A-TypeTheoryTerm-inside-a-term-is-spliced-in"
]

VerificationTest[
	Module[{statement = TypeTheoryTerm[2 + 2 == 4]}, TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]], TypeTheoryTerm[statement]]],
	True,
	TestID -> "A-symbol-whose-value-is-a-TypeTheoryTerm-stands-for-it"
]


(* === display === *)

VerificationTest[
	MatchQ[ToBoxes[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == x, x + 0 == x]]]], InterpretationBox[_, _TypeTheoryTerm]],
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
