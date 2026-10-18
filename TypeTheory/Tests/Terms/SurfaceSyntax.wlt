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
	TypeTheoryTerm[ForAll[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"]}, TypeSpecifier[{A} -> A]], prelude],
	TestID -> "Types-read-back-with-binder-names-and-implicit-binders"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p]}, h]]],
	TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], prelude],
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
	MatchQ[
		ToBoxes[TypeTheoryTerm[TypeUniverse[Max[1, u]]]],
		InterpretationBox[TemplateBox[{_, _, "\"Sort\"", TemplateBox[{"\"(\"", TemplateBox[{_, _, "\"max\"", "1", "u"}, "RowWithSeparators"], "\")\""}, "RowDefault"]}, "RowWithSeparators"], _]
	],
	True,
	TestID -> "A-universe-at-a-maximum-of-levels-shows-max-in-parentheses"
]

VerificationTest[
	MatchQ[
		ToBoxes[TypeTheoryTerm[TypeUniverse[Max[u + 1, v + 1]]]],
		InterpretationBox[TemplateBox[{_, _, "\"Type\"", TemplateBox[{"\"(\"", TemplateBox[{_, _, "\"max\"", "u", "v"}, "RowWithSeparators"], "\")\""}, "RowDefault"]}, "RowWithSeparators"], _]
	],
	True,
	TestID -> "A-universe-at-a-maximum-of-successors-shows-as-Type-of-the-maximum"
]

VerificationTest[
	MatchQ[
		ToBoxes[TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne]],
		InterpretationBox[GridBox[{{_, "FlipZero", ":", RowBox[{_, "\[LongRightArrow]", "BitOne"}]}}, ___], _TypeTheoryRewriteRule]
	],
	True,
	TestID -> "A-rewrite-rule-shows-its-sides-with-a-long-arrow"
]

VerificationTest[
	MatchQ[ToBoxes[prelude[EqualityCongruence]], InterpretationBox[_GridBox, _TypeTheoryTheorem]],
	True,
	TestID -> "A-declaration-displays-as-a-keyword-a-name-and-a-type"
]

VerificationTest[
	With[{boxes = ToBoxes[TypeOf[TypeTheoryTerm[AndIntroduction, prelude]]]},
		{FreeQ[boxes, "&&"], ! FreeQ[boxes, "\[And]"], StringFreeQ[ToString[boxes, InputForm, CharacterEncoding -> "ASCII"], "Formal"]}
	],
	{True, True, True},
	TestID -> "The-prelude-binders-show-as-plain-names-and-And-as-a-wedge"
]

VerificationTest[
	With[{boxes = ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, 0 + NaturalNumberSuccessor[k] == NaturalNumberSuccessor[NaturalNumberZero]], prelude]]},
		{FreeQ[boxes, "NaturalNumberZero" | "NaturalNumberSuccessor"], ! FreeQ[boxes, RowBox[{"k", "+", "1"}]], ! FreeQ[boxes, RowBox[{"0", "+", "1"}]]}
	],
	{True, True, True},
	TestID -> "The-natural-numbers-show-as-zero-and-n-plus-one"
]

VerificationTest[
	Cases[
		TypeOf[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[h, a]}, Construct[AndIntroduction]], prelude]],
		Typed[name_Symbol, _] :> SymbolName[Unevaluated[name]],
		Infinity,
		Heads -> True
	],
	{"a", "a1", "b"},
	TestID -> "A-binder-showing-a-taken-name-gets-a-numbered-one"
]

VerificationTest[
	FreeQ[ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, NaturalNumberSuccessor[NaturalNumberSuccessor[k]] == k + 2]]], RowBox[{"k", "+", "1", "+", "1"}]],
	False,
	TestID -> "Successors-of-successors-add-up-from-the-left"
]

VerificationTest[
	With[{boxes = ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[a, Booleans], Typed[b, Booleans]}, Not[a && b] || (a && b && a)]]]]},
		{! FreeQ[boxes, "&&"], ! FreeQ[boxes, "||"], ! FreeQ[boxes, RowBox[{"!", _}]], FreeQ[boxes, "\[And]" | "\[Or]" | "\[Not]"], ! FreeQ[boxes, "\"\[DoubleStruckCapitalB]\""]}
	],
	{True, True, True, True, True},
	TestID -> "The-Booleans-show-as-Lean-shows-them"
]

VerificationTest[
	Cases[ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]]], "\"false\"", Infinity],
	{"\"false\""},
	TestID -> "A-Boolean-value-shows-in-lower-case"
]
