(* ::Package:: *)

(* Tests for Terms/SurfaceSyntax.wl and Terms/Formatting.wl: held syntax trees, terms that carry their
   environment, reading core terms back for display and exactly, and the notebook display. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

(* the boxes of an expression as they show, each tooltip's type left out: a term shows the types of its parts on
   mouseover, which change nothing it shows *)
(* the boxes of a display without its mouseovers and without the style a term sets around itself, which hides the quotes
   of names that are strings *)
shownBoxes[expression_] := ToBoxes[expression] //. {TooltipBox[shown_, ___] :> shown, StyleBox[shown_, ShowStringCharacters -> False] :> shown}

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
	TypeTheoryType[TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]}, x]]],
	TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[1]]}, A -> A], prelude],
	TestID -> "Types-read-back-with-binder-names-and-implicit-binders"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[Function[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"], Typed[x, A]}, x]]],
	TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[1]]}, A -> A], prelude],
	TestID -> "An-implicit-Annotation-is-the-same-binder-as-TypedImplicit"
]

VerificationTest[
	FreeQ[ToBoxes[TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[1]]}, TypeSpecifier[{A} -> A]]]], TemplateBox[{"\"{\"", _, "\"}\""}, "RowDefault"]],
	False,
	TestID -> "An-implicit-binder-shows-in-braces"
]

VerificationTest[
	Map[
		Function[term, With[{boxes = shownBoxes[term]}, {
			Count[boxes, RowBox[{"(", RowBox[{SubscriptBox["\[ForAll]" | "\[Exists]", _], _}] | RowBox[{"\[Not]", _}], ")"}], Infinity],
			Count[boxes, RowBox[{SubscriptBox["\[ForAll]" | "\[Exists]", _], _}], Infinity]
		}]],
		{
			TypeTheoryTerm[Equivalent[ForAll[{Typed[n, Naturals]}, n == n], ForAll[{Typed[m, Naturals]}, m == m]]],
			TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n == n] && True && Exists[{Typed[m, Naturals]}, m == m]],
			TypeTheoryTerm[Not[ForAll[{Typed[n, Naturals]}, n == n]] || True],
			TypeTheoryTerm[True && ForAll[{Typed[n, Naturals]}, n == n]]
		}
	],
	{{1, 2}, {1, 2}, {1, 1}, {0, 1}},
	TestID -> "A-quantifier-before-a-connective-is-parenthesized"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p]}, h]]],
	TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], prelude],
	TestID -> "A-function-type-between-propositions-reads-back-as-Implies"
]

VerificationTest[
	With[{term = TypeTheoryTerm[0 + 1 == 1]}, TypeTheoryType[TypeTheoryTerm[Implies[term, term], prelude]]],
	TypeTheoryTerm[TypeUniverse[0], prelude],
	TestID -> "A-TypeTheoryTerm-inside-a-term-is-spliced-in"
]

VerificationTest[
	Module[{statement = TypeTheoryTerm[2 + 2 == 4]}, MatchQ[TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4], prelude], TypeTheoryTerm[statement]], _Success]],
	True,
	TestID -> "A-symbol-whose-value-is-a-TypeTheoryTerm-stands-for-it"
]

VerificationTest[
	Take[Normal[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]], -1],
	{TypeTheoryTheorem[TwoPlusTwo, Construct[Subscript[Equal, 1], NonNegativeIntegers, 2 + 2, 4], Construct[Subscript["equalityReflexivity", 1], NonNegativeIntegers, 4]]},
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
	Cases[shownBoxes[TypeTheoryTerm[{TypeUniverse[0], TypeUniverse[1], NonNegativeIntegers}]], "\"Prop\"" | "\"Type\"" | "\"\[DoubleStruckCapitalN]\"", Infinity],
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
		ToBoxes[TypeTheoryTerm[TypeUniverse[Max[1, u]]]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes,
		InterpretationBox[TemplateBox[{_, _, "\"Sort\"", TemplateBox[{"\"(\"", TemplateBox[{_, _, "\"max\"", "1", "u"}, "RowWithSeparators"], "\")\""}, "RowDefault"]}, "RowWithSeparators"], _]
	],
	True,
	TestID -> "A-universe-at-a-maximum-of-levels-shows-max-in-parentheses"
]

VerificationTest[
	MatchQ[
		ToBoxes[TypeTheoryTerm[TypeUniverse[Max[u + 1, v + 1]]]] //. (StyleBox | TooltipBox)[boxes_, ___] :> boxes,
		InterpretationBox[TemplateBox[{_, _, "\"Type\"", TemplateBox[{"\"(\"", TemplateBox[{_, _, "\"max\"", "u", "v"}, "RowWithSeparators"], "\")\""}, "RowDefault"]}, "RowWithSeparators"], _]
	],
	True,
	TestID -> "A-universe-at-a-maximum-of-successors-shows-as-Type-of-the-maximum"
]

VerificationTest[
	MatchQ[
		shownBoxes[TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne]],
		InterpretationBox[GridBox[{{_, "FlipZero", ":", RowBox[{_, "\[LongRightArrow]", "BitOne"}]}}, ___], _TypeTheoryRewriteRule]
	],
	True,
	TestID -> "A-rewrite-rule-shows-its-sides-with-a-long-arrow"
]

VerificationTest[
	MatchQ[ToBoxes[prelude["equalityCongruence"]], InterpretationBox[_GridBox, _TypeTheoryTheorem]],
	True,
	TestID -> "A-declaration-displays-as-a-keyword-a-name-and-a-type"
]

VerificationTest[
	With[{boxes = ToBoxes[TypeTheoryType[TypeTheoryTerm["andIntroduction", prelude]]]},
		{FreeQ[boxes, "&&"], ! FreeQ[boxes, "\[And]"], StringFreeQ[ToString[boxes, InputForm, CharacterEncoding -> "ASCII"], "Formal"]}
	],
	{True, True, True},
	TestID -> "The-prelude-binders-show-as-plain-names-and-And-as-a-wedge"
]

VerificationTest[
	With[{boxes = ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, 0 + "successor"[k] == "successor"["zero"]], prelude]] //. (StyleBox | TooltipBox)[name_, ___] :> name},
		{FreeQ[boxes, "\"zero\"" | "\"successor\""], ! FreeQ[boxes, RowBox[{"k", "+", "1"}]], ! FreeQ[boxes, RowBox[{"0", "+", "1"}]]}
	],
	{True, True, True},
	TestID -> "The-natural-numbers-show-as-zero-and-n-plus-one"
]

VerificationTest[
	Cases[
		TypeTheoryType[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[h, a]}, Construct["andIntroduction"]], prelude]],
		(Typed | TypedImplicit)[name_Symbol, _] :> SymbolName[Unevaluated[name]],
		Infinity,
		Heads -> True
	],
	{"a", "a1", "b"},
	TestID -> "A-binder-showing-a-taken-name-gets-a-numbered-one"
]

(* a sum is of two, and a sum in a sum shows its parentheses on either side: (a + b) + c and a + (b + c) are different
   terms. So the successor of a successor is (k + 1) + 1 *)
VerificationTest[
	{
		FreeQ[
			ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, "successor"["successor"[k]] == k + 2]]] //. (StyleBox | TooltipBox)[name_, ___] :> name,
			RowBox[{RowBox[{"(", RowBox[{"k", "+", "1"}], ")"}], "+", "1"}]
		],
		FreeQ[
			ToBoxes[TypeTheoryType[TypeTheoryTerm["additionAssociativity", prelude]]] //. (StyleBox | TooltipBox)[name_, ___] :> name,
			RowBox[{RowBox[{"(", RowBox[{"\"a\"", "+", "\"b\""}], ")"}], "+", "\"c\""}]
		],
		FreeQ[
			ToBoxes[TypeTheoryType[TypeTheoryTerm["additionAssociativity", prelude]]] //. (StyleBox | TooltipBox)[name_, ___] :> name,
			RowBox[{"\"a\"", "+", RowBox[{"(", RowBox[{"\"b\"", "+", "\"c\""}], ")"}]}]
		],
		FreeQ[
			ToBoxes[TypeTheoryType[TypeTheoryTerm["additionAssociativity", prelude]]] //. (StyleBox | TooltipBox)[name_, ___] :> name,
			RowBox[{"\"a\"", "+", "\"b\"", "+", "\"c\""}]
		]
	},
	{False, False, False, True},
	TestID -> "A-sum-in-a-sum-shows-its-parentheses"
]

(* TraditionalForm shows a recursor applied to all its arguments as its cases: the recursor beside the term it recurses
   on, then a row for the motive and a row for each constructor, labelled by the constructor applied to the variables
   the case binds for its fields. An application is f(x) and an equation a = b, and a sum keeps the order it has: the
   boxes are StandardForm's, since the Wolfram Language's TraditionalForm would put the terms of a sum in its own order.
   StandardForm shows the recursor as before. *)
VerificationTest[
	Module[{term, traditional, standard},
		term = TypeTheoryTerm[
			Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[m, NonNegativeIntegers]}, NonNegativeIntegers],
				0,
				Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, (r + 2) + k],
				n
			]],
			prelude
		];
		traditional = ToBoxes[term, TraditionalForm] //. (StyleBox | TooltipBox | TagBox)[shown_, ___] :> shown;
		standard = ToBoxes[term, StandardForm] //. (StyleBox | TooltipBox | TagBox)[shown_, ___] :> shown;
		{
			Cases[traditional, GridBox[{{RowBox[{_SubscriptBox, _, "n"}], __}, rows__}, ___] :> Cases[{rows}, {_, label_, _} :> label], Infinity],
			FreeQ[traditional, RowBox[{RowBox[{"(", RowBox[{"r", "+", "2"}], ")"}], "+", "k"}]],
			FreeQ[standard, _GridBox],
			FreeQ[
				ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, "successor"[k] == k + 1 && "equalitySymmetry"["equalityReflexivity"[k]] == "equalityReflexivity"[k]], prelude], TraditionalForm] //.
					(StyleBox | TooltipBox | TagBox)[shown_, ___] :> shown,
				"==" | "\[Equal]" | "["
			],
			FreeQ[
				ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, "equalitySymmetry"["equalityReflexivity"[k]] == "equalityReflexivity"[k]], prelude], TraditionalForm] //.
					(StyleBox | TooltipBox | TagBox)[shown_, ___] :> shown,
				RowBox[{"\"equalityReflexivity\"", "(", "k", ")"}]
			]
		}
	],
	{{{"\"motive\"", "0", RowBox[{"k", "+", "1"}]}}, False, True, True, False},
	TestID -> "TraditionalForm-shows-a-recursor-as-its-cases"
]

(* In TraditionalForm a constant shows by the notation TraditionalForm has for it: the Wolfram Language's own for one of its
   symbols, a mod b, and f(x) for a symbol it has none for. An argument stays as the term shows it, a sum in the order it is
   written, in a TagBox that the Wolfram Language's typesetting leaves alone, and in parentheses where the notation sets it
   beside an operator. The operators a term lays out itself are not notations: an equation gets no parentheses from them.
   StandardForm shows the same constants applied in brackets. *)
VerificationTest[
	Module[{integers = TypeTheoryEnvironment["Integers"], term, traditional, plain},
		plain[boxes_] := boxes //. (StyleBox | TooltipBox | TagBox)[shown_, ___] :> shown;
		term = TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Mod[1 + a, 4] <= Quotient[a + b, 4]], integers];
		traditional = ToBoxes[term, TraditionalForm];
		{
			MatchQ[Cases[traditional, TemplateBox[_, "Mod"], Infinity], {TemplateBox[{RowBox[{"(", TagBox[_, "TypeTheoryArgument"], ")"}], "4"}, "Mod"]}],
			Cases[plain[traditional], TemplateBox[_, "Mod"] | RowBox[{"Quotient", __}], Infinity],
			Cases[plain[ToBoxes[term, StandardForm]], RowBox[{"Mod" | "Quotient", __}], Infinity],
			Cases[
				plain[ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, 5 == Length[{k}] + 1], prelude], TraditionalForm]],
				RowBox[{"5", __}],
				Infinity
			]
		}
	],
	{
		True,
		{TemplateBox[{RowBox[{"(", RowBox[{"1", "+", "a"}], ")"}], "4"}, "Mod"], RowBox[{"Quotient", "(", RowBox[{RowBox[{"a", "+", "b"}], ",", "4"}], ")"}]},
		{RowBox[{"Mod", "[", RowBox[{RowBox[{"1", "+", "a"}], ",", "4"}], "]"}], RowBox[{"Quotient", "[", RowBox[{RowBox[{"a", "+", "b"}], ",", "4"}], "]"}]},
		{RowBox[{"5", "=", RowBox[{RowBox[{"Length", "(", RowBox[{"{", "k", "}"}], ")"}], "+", "1"}]}]}
	},
	TestID -> "TraditionalForm-shows-a-constant-by-its-traditional-notation"
]

(* a notation of the user's for TraditionalForm shows there and not in StandardForm, and one for every form shows in
   both; twelve applications one in another take no longer to show than their count *)
VerificationTest[
	Module[{named, plain, nested},
		plain[boxes_] := boxes //. (StyleBox | TooltipBox | TagBox)[shown_, ___] :> shown;
		MakeBoxes["traditionalScaled"[a_, b_], TraditionalForm] := RowBox[{MakeBoxes[a, TraditionalForm], "\[CircleDot]", MakeBoxes[b, TraditionalForm]}];
		MakeBoxes["everyFormScaled"[a_, b_], form_] := MakeBoxes[CenterDot[a, b], form];
		named = TypeTheoryEnvironment[prelude, {
			TypeTheoryDefinition["traditionalScaled", Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n m]],
			TypeTheoryDefinition["everyFormScaled", Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n m]]
		}];
		nested = TypeTheoryTerm[Join[Join[Join[Join[Join[Join[Join[Join[Join[Join[Join[Join[{1}, {2}], {3}], {4}], {5}], {6}], {7}], {8}], {9}], {10}], {11}], {12}], {13}], prelude];
		{
			Cases[
				plain[ToBoxes[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, "traditionalScaled"[1 + x, x] == x], named], TraditionalForm]],
				RowBox[{__, "\[CircleDot]", __}],
				Infinity
			],
			Cases[
				plain[ToBoxes[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, "traditionalScaled"[1 + x, x] == x], named], StandardForm]],
				RowBox[{"\"traditionalScaled\"", __}],
				Infinity
			],
			Cases[
				plain[ToBoxes[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, "everyFormScaled"[1 + x, x] == x], named], TraditionalForm]],
				RowBox[{__, "\[CenterDot]", __}],
				Infinity
			],
			Count[plain[ToBoxes[nested, TraditionalForm]], RowBox[{"Join", "(", __}], {0, Infinity}],
			First[AbsoluteTiming[ToBoxes[nested, TraditionalForm]]] < 2
		}
	],
	{
		{RowBox[{RowBox[{"(", RowBox[{"1", "+", "x"}], ")"}], "\[CircleDot]", "x"}]},
		{RowBox[{"\"traditionalScaled\"", "[", RowBox[{RowBox[{"1", "+", "x"}], ",", "x"}], "]"}]},
		{RowBox[{RowBox[{"(", RowBox[{"1", "+", "x"}], ")"}], "\[CenterDot]", "x"}]},
		12,
		True
	},
	TestID -> "TraditionalForm-shows-a-notation-given-for-it"
]

(* A notation may give an InterpretationBox, which holds its parts: what a display rewrites inside it, the connectives,
   the parentheses of an operand, the mouseovers of operators, is computed before it is put in, and the boxes hold
   boxes alone, no rewrite left as it is written and no symbol of the display's own. *)
VerificationTest[
	Module[{named, shown, leftovers},
		MakeBoxes["interpretedBoth"[a_, b_], form_] := With[{x = MakeBoxes[a, form], y = MakeBoxes[b, form]}, InterpretationBox[RowBox[{x, "&&", y}], "interpretedBoth"[a, b]]];
		MakeBoxes["interpretedScaled"[a_, b_], TraditionalForm] := With[{x = MakeBoxes[a, TraditionalForm], y = MakeBoxes[b, TraditionalForm]},
			InterpretationBox[RowBox[{x, "\[CircleDot]", y}], "interpretedScaled"[a, b]]];
		named = TypeTheoryEnvironment[prelude, {
			TypeTheoryDefinition["interpretedBoth", Function[{Typed[x, TypeUniverse[0]], Typed[y, TypeUniverse[0]]}, x && y]],
			TypeTheoryDefinition["interpretedScaled", Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n m]]
		}];
		shown[term_, form_] := First[ToBoxes[term, form]] //. InterpretationBox[boxes_, _] :> boxes;
		leftovers[boxes_] := Union[Cases[
			boxes,
			symbol_Symbol /; MemberQ[{Replace, MapIndexed, With, If, Condition}, Unevaluated[symbol]] || StringStartsQ[Context[symbol], "WolframInstitute`TypeTheory`"] :> SymbolName[Unevaluated[symbol]],
			{0, Infinity},
			Heads -> True
		]];
		{
			leftovers[shown[TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies["interpretedBoth"[p, q && p], p]], named], StandardForm]],
			leftovers[shown[TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies["interpretedBoth"[p, q && p], p]], named], TraditionalForm]],
			leftovers[shown[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, "interpretedScaled"[1 + x, x] == x], named], TraditionalForm]],
			Cases[
				shown[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, "interpretedScaled"[1 + x, x] == x], named], TraditionalForm] //. (StyleBox | TooltipBox | TagBox)[boxes_, ___] :> boxes,
				RowBox[{__, "\[CircleDot]", __}],
				Infinity
			]
		}
	],
	{{}, {}, {}, {RowBox[{RowBox[{"(", RowBox[{"1", "+", "x"}], ")"}], "\[CircleDot]", "x"}]}},
	TestID -> "A-notation-that-gives-an-InterpretationBox-holds-boxes-alone"
]

(* a term sets a style around its boxes that hides the quotes of names that are strings, which an input cell would show *)
VerificationTest[
	MatchQ[ToBoxes[TypeTheoryTerm["true"]], InterpretationBox[StyleBox[_, ShowStringCharacters -> False], _TypeTheoryTerm]],
	True,
	TestID -> "A-term-shows-its-string-names-without-quotes-in-an-input-cell-too"
]

VerificationTest[
	With[{boxes = shownBoxes[WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[a, Booleans], Typed[b, Booleans]}, Not[a && b] || (a && b && a)]]]]},
		{! FreeQ[boxes, "&&"], ! FreeQ[boxes, "||"], ! FreeQ[boxes, RowBox[{"!", _}]], FreeQ[boxes, "\[And]" | "\[Or]" | "\[Not]"], ! FreeQ[boxes, "\"\[DoubleStruckCapitalB]\""]}
	],
	{True, True, True, True, True},
	TestID -> "The-Booleans-show-as-And-Or-and-Not-are-written"
]

VerificationTest[
	Cases[ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]]], "\"false\"", Infinity],
	{"\"false\""},
	TestID -> "A-Boolean-value-shows-in-lower-case"
]

VerificationTest[
	{
		FreeQ[ToBoxes[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]]], "\"\[DoubleStruckCapitalN]\""],
		FreeQ[ToBoxes[TypeTheoryType[TypeTheoryTerm[Function[{Typed[Naturals, TypeUniverse[1]], Typed[x, Naturals]}, x]]]], "\"\[DoubleStruckCapitalN]\""]
	},
	{False, True},
	TestID -> "Naturals-shows-as-the-natural-numbers-unless-a-binder-has-its-name"
]

VerificationTest[
	{
		Cases[shownBoxes[TypeTheoryTerm[CartesianProductType[NonNegativeIntegers, CartesianProductType[Booleans, Integers]]]], RowBox[{_, "\[Times]", _, "\[Times]", _}], Infinity] =!= {},
		Cases[shownBoxes[TypeTheoryTerm[CartesianProductType[CartesianProductType[NonNegativeIntegers, Booleans], Integers]]], RowBox[{RowBox[{"(", _, ")"}], "\[Times]", _}], Infinity] =!= {},
		Cases[shownBoxes[TypeTheoryTerm[DisjointUnionType[CartesianProductType[NonNegativeIntegers, Booleans], Booleans]]], RowBox[{RowBox[{_, "\[Times]", _}], "|", _}], Infinity] =!= {},
		FreeQ[shownBoxes[TypeTheoryTerm[DisjointUnionType[NonNegativeIntegers, CartesianProductType[NonNegativeIntegers, Booleans]]]], "CartesianProductType" | "DisjointUnionType" | "\[Cross]"],
		Cases[shownBoxes[TypeTheoryTerm[CircleTimes[A, B]]], RowBox[{"A", "\[CircleTimes]", "B"}], Infinity] =!= {}
	},
	{True, True, True, True, True},
	TestID -> "Products-and-sums-of-types-show-as-times-and-alternatives"
]

VerificationTest[
	{
		Cases[shownBoxes[TypeTheoryTerm["pair"[1, "pair"[2, 3]]]], TemplateBox[{"\"(\"", TemplateBox[{", ", "\", \"", "1", "2", "3"}, "RowWithSeparators"], "\")\""}, "RowDefault"], Infinity] =!= {},
		Cases[shownBoxes[TypeTheoryTerm["dependentPair"[1, 2]]], TemplateBox[{"\"\[LeftAngleBracket]\"", TemplateBox[{", ", "\", \"", "1", "2"}, "RowWithSeparators"], "\"\[RightAngleBracket]\""}, "RowDefault"], Infinity] =!= {}
	},
	{True, True},
	TestID -> "Pairs-show-as-tuples-and-dependent-pairs-in-angle-brackets"
]

VerificationTest[
	{
		Cases[shownBoxes[TypeTheoryTerm[Prepend[1][Prepend[2][{}]]]], TemplateBox[{"\"{\"", TemplateBox[{", ", "\", \"", "1", "2"}, "RowWithSeparators"], "\"}\""}, "RowDefault"], Infinity] =!= {},
		Cases[shownBoxes[TypeTheoryTerm[Prepend[Typed[{}, {NonNegativeIntegers}], 1]]], TemplateBox[{"\"{\"", TemplateBox[{", ", "\", \"", "1"}, "RowWithSeparators"], "\"}\""}, "RowDefault"], Infinity] =!= {},
		Cases[shownBoxes[TypeTheoryTerm[Join[l, {}]]], RowBox[{"{", "}"}], Infinity],
		FreeQ[shownBoxes[TypeTheoryTerm[Prepend[1][l]]], "Prepend"]
	},
	{True, True, {RowBox[{"{", "}"}]}, False},
	TestID -> "A-list-ending-in-the-empty-list-shows-its-elements-in-braces"
]

(* a list type shows as it is written, {A}, and lists of lists {{A}}; a constant named by a symbol, a type or a function,
   shows in bold, so that it is told apart from a constant named by a string, which shows as the string does, as a value does *)
VerificationTest[
	With[
		{
			lists = shownBoxes[TypeTheoryTerm[{{NonNegativeIntegers}}]],
			named = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[Polynomial, TypeUniverse[1]],
				TypeTheoryAxiom["Polynomials", TypeUniverse[1]],
				TypeTheoryAxiom["zeroPolynomial", "Polynomials"],
				TypeTheoryAxiom[degree, TypeSpecifier[{Polynomial} -> NonNegativeIntegers]],
				TypeTheoryAxiom[zero, Polynomial]
			}]
		},
		{
			Cases[lists, RowBox[{"{", RowBox[{"{", "\"\[DoubleStruckCapitalN]\"", "}"}], "}"}], {0, Infinity}] =!= {},
			FreeQ[lists, StyleBox],
			Length[Cases[shownBoxes[TypeTheoryTerm[TypeSpecifier[{Polynomial} -> {Polynomial}], named]], StyleBox["Polynomial", Bold, ___], Infinity]],
			FreeQ[shownBoxes[TypeTheoryTerm[TypeSpecifier[{"Polynomials"} -> {"Polynomials"}], named]], StyleBox],
			FreeQ[shownBoxes[TypeTheoryTerm[Typed["zeroPolynomial", "Polynomials"], named]], StyleBox],
			FreeQ[shownBoxes[TypeTheoryTerm[True && False]], StyleBox],
			Sort[Cases[shownBoxes[TypeTheoryTerm[degree[zero], named]] /. TooltipBox[boxes_, ___] :> boxes, StyleBox[name_String, Bold, ___] :> name, Infinity]],
			FreeQ[shownBoxes[TypeTheoryTerm[Function[Typed[zero, NonNegativeIntegers], zero], named]], StyleBox[_, Bold, ___]]
		}
	],
	{True, True, 2, True, True, True, {"degree", "zero"}, True},
	TestID -> "A-list-type-shows-in-braces-and-a-constant-named-by-a-symbol-in-bold"
]

VerificationTest[
	Cases[
		ToBoxes[TypeTheoryTerm[DependentSum[NonNegativeIntegers, Function[{Typed[n, NonNegativeIntegers]}, n == n]]]] //. (StyleBox | TooltipBox)[name_, ___] :> name,
		SubscriptBox["\[CapitalSigma]", RowBox[{"n", "\[Colon]", _}]],
		Infinity
	] =!= {},
	True,
	TestID -> "A-dependent-sum-shows-as-sigma-over-its-binder"
]

VerificationTest[
	{
		ToBoxes[TypeTheoryTerm["rationalOfPair"["pair"[3, 0]]]],
		Cases[ToBoxes[TypeTheoryTerm[QuotientIntroduction["rationalRelation", "pair"[5, 1]]]], FractionBox["5", "2"], Infinity, 1]
	},
	{InterpretationBox[StyleBox["3", ShowStringCharacters -> False], TypeTheoryTerm["rationalOfPair"["pair"[3, 0]]]], {FractionBox["5", "2"]}},
	TestID -> "A-class-of-a-pair-with-a-literal-denominator-still-shows-as-a-fraction"
]

VerificationTest[
	Cases[
		ToBoxes[TypeTheoryTerm[Subtype[Function[{Typed[n, NonNegativeIntegers]}, 2 <= n]]]] //. (StyleBox | TooltipBox)[name_, ___] :> name,
		TemplateBox[{"\"{\"", TemplateBox[{RowBox[{"n", "\[Colon]", _}], "\" // \"", _}, "RowDefault"], "\"}\""}, "RowDefault"],
		Infinity
	] =!= {},
	True,
	TestID -> "A-subtype-shows-its-variable-and-its-property"
]

VerificationTest[
	With[{boxes = First[ToBoxes[TypeTheoryTerm[ForAll[{Typed[PrivateDisplay`k, Naturals]}, PrivateDisplay`k + 0 == PrivateDisplay`k]]]]},
		{StringFreeQ[ToString[boxes, InputForm], "PrivateDisplay`"], ! FreeQ[boxes, "\"k\""]}
	],
	{True, True},
	TestID -> "A-bound-variable-shows-by-its-name-whatever-its-context"
]

(* a bound variable shows in the color of a local variable, a hypothesis of a goal in its target too, a universe level
   dimmed and an unsolved metavariable in the color of a hole; the colors come from one place *)
VerificationTest[
	With[
		{
			colors = WolframInstitute`TypeTheory`PackageScope`$displayColors,
			styled = Function[boxes, Cases[boxes, StyleBox[text_String, color_, ___] /; color =!= Bold :> {StringTrim[text, "\""], color}, Infinity]]
		},
		{
			DeleteDuplicates[styled[shownBoxes[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]]]] === {{"n", colors["BoundVariable"]}},
			DeleteDuplicates[styled[shownBoxes[TypeTheoryType[TypeTheoryTerm[List]]]]],
			FreeQ[styled[shownBoxes[TypeTheoryTerm[TypeUniverse[1]]]], colors["Level"]],
			MemberQ[
				styled[shownBoxes[TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], {TypeTheoryTactic["Introduce"]}]]],
				{"n", colors["BoundVariable"]}
			],
			shownBoxes[TypeTheoryTerm[TypeUniverse[Placeholder["?u3"]]]] =!= {} && ! FreeQ[
				ToBoxes[RawBoxes[WolframInstitute`TypeTheory`PackageScope`typeTheoryBoxes[
					WolframInstitute`TypeTheory`PackageScope`syntaxHead[TypeUniverse, {WolframInstitute`TypeTheory`PackageScope`syntaxHead[Placeholder, {WolframInstitute`TypeTheory`PackageScope`syntaxString["?u3"]}]}],
					StandardForm
				]]],
				StyleBox["\"?u3\"" | "?u3", colors["Unsolved"], ___]
			]
		}
	],
	{True, {{"u", WolframInstitute`TypeTheory`PackageScope`$displayColors["Level"]}}, True, True, True},
	TestID -> "A-bound-variable-a-level-and-an-unsolved-metavariable-show-in-their-colors"
]

(* the messages of failures as a terminal prints them, with no front end and no notebook boxes asked for: text, with no
   box left in it *)
textMessagesQ[] := With[{saved = Environment["TYPETHEORY_NOTEBOOK_BOXES"]},
	Internal`WithLocalSettings[
		SetEnvironment["TYPETHEORY_NOTEBOOK_BOXES" -> None],
		Block[{$FrontEnd = Null}, AllTrue[
			{
				TypeTheoryType[Function[{Typed[l, {NonNegativeIntegers}]}, l === {}]],
				TypeTheoryType[Typed[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]}, x], NonNegativeIntegers]]
			},
			Function[failure, FailureQ[failure] && StringFreeQ[ToString[failure, OutputForm], "Box"]]
		] && StringFreeQ[ToString[TypeTheoryTerm[Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> p[[1]] + 1], OutputForm], "Private"]],
		SetEnvironment["TYPETHEORY_NOTEBOOK_BOXES" -> Replace[saved, $Failed -> None]]
	]
]

(* on mouseover a constant shows its declared type and a bound variable the type its binder gives, drawn without
   tooltips of their own; by default only where a front end draws them, so that a terminal prints a failure's message,
   whose terms it reads from their boxes, as text *)
VerificationTest[
	With[{tips = Function[boxes, Cases[boxes, TooltipBox[shown_, tip_, ___] :> {shown /. StyleBox[inner_, ___] :> inner, FreeQ[tip, TooltipBox]}, Infinity]]},
		{
			Block[{WolframInstitute`TypeTheory`PackageScope`$displayTooltips = True}, With[{shown = tips[ToBoxes[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]]]},
				MemberQ[shown, {"n", True}] && AllTrue[shown, Last]
			]],
			Block[{WolframInstitute`TypeTheory`PackageScope`$displayTooltips = True}, First[tips[ToBoxes[TypeTheoryTerm["andIntroduction"]]]]],
			Block[{WolframInstitute`TypeTheory`PackageScope`$displayTooltips = False}, FreeQ[ToBoxes[TypeTheoryTerm["andIntroduction"]], TooltipBox]],
			textMessagesQ[]
		}
	],
	{True, {"\"andIntroduction\"", True}, True, True},
	TestID -> "A-constant-and-a-bound-variable-show-their-types-on-mouseover"
]

(* a constant applied shows as f[x], its name in bold with its type on mouseover, not as (f)[x]; a symbol of a paclet as
   documentation copies it, PacletSymbol[paclet, name], reads as the symbol it names *)
VerificationTest[
	With[{spaces = TypeTheoryEnvironment[prelude, {TypeTheoryAxiom[ModularSpace, NonNegativeIntegers -> TypeUniverse[1]]}]},
		{
			First[shownBoxes[TypeTheoryTerm[ModularSpace[12], spaces]]],
			MatchQ[TypeTheoryType[TypeTheoryTerm[PacletSymbol["WolframInstitute/TypeTheory", "Decide"][True], prelude]], TypeTheoryTerm[Booleans, _]],
			TypeTheoryTerm[PacletSymbol["WolframInstitute/TypeTheory", "Decide"][True], prelude] === TypeTheoryTerm[Decide[True], prelude],
			Hold @@ {TypeTheoryTerm[PacletSymbol["Nowhere/Nothing", "x"]]}
		}
	],
	{RowBox[{StyleBox["ModularSpace", Bold, StripOnInput -> False], "[", "12", "]"}], True, True, Hold[TypeTheoryTerm[PacletSymbol["Nowhere/Nothing", "x"]]]},
	TestID -> "A-constant-applied-shows-without-parentheses-and-a-PacletSymbol-reads-as-its-symbol"
]

(* the documentation site copies a symbol as PacletSymbol[If[PacletFind[paclet] === {}, PacletInstall[...], paclet], fullName]:
   the term reads the symbol without evaluating the guard, here one that would set guarded *)
VerificationTest[
	Block[{guarded = False},
		{
			TypeTheoryTerm[
				PacletSymbol[If[guarded = True; PacletFind["WolframInstitute/TypeTheory"] === {}, PacletInstall["WolframInstitute/TypeTheory"], "WolframInstitute/TypeTheory"], "WolframInstitute`TypeTheory`InductiveRecursor"][And][
					Function[{Typed[t, And[True, True]]}, PacletSymbol[If[guarded = True; False, Null, "WolframInstitute/TypeTheory"], "Naturals"]],
					Function[{Typed[p, True], Typed[q, True]}, 7],
					"andIntroduction"["trueIntroduction", "trueIntroduction"]],
				prelude] ===
				TypeTheoryTerm[InductiveRecursor[And][Function[{Typed[t, And[True, True]]}, Naturals], Function[{Typed[p, True], Typed[q, True]}, 7], "andIntroduction"["trueIntroduction", "trueIntroduction"]], prelude],
			guarded
		}
	],
	{True, False},
	TestID -> "A-PacletSymbol-with-the-install-guard-and-a-full-name-reads-as-its-symbol-without-evaluating-the-guard"
]

(* a notation of the user's for a constant, a rule of MakeBoxes for a symbol or a string head, shows instead of the bold
   head; a projection of a colored bound variable is p〚1〛, without parentheses *)
VerificationTest[
	Module[{doubling, boxes, projected},
		doubling = TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[Doubling, Typed[n, NonNegativeIntegers] |-> n + n], TypeTheoryAxiom["halving", NonNegativeIntegers -> NonNegativeIntegers]}];
		MakeBoxes[Doubling[a_], form_] := MakeBoxes[CenterDot[2, a], form];
		MakeBoxes["halving"[a_], form_] := MakeBoxes[a / 2, form];
		boxes = ToBoxes[TypeTheoryTerm[Typed[k, NonNegativeIntegers] |-> Doubling["halving"[k]], doubling]];
		projected = ToBoxes[TypeTheoryTerm[Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> p[[1]], prelude]];
		{
			! FreeQ[boxes, "\[CenterDot]"], ! FreeQ[boxes, FractionBox[_, "2"]], FreeQ[boxes, StyleBox["Doubling", ___]],
			! FreeQ[projected, RowBox[{_TooltipBox | _StyleBox, "\[LeftDoubleBracket]", __}]], ! FreeQ[projected, "\[LeftDoubleBracket]"],
			FreeQ[ToBoxes[TypeTheoryTerm[Typed[f, TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]] |-> f, prelude]], "TypeSpecifier" | "\"TypeSpecifier\"", Infinity]
		}
	],
	{True, True, True, True, True, True},
	TestID -> "A-notation-of-the-user-shows-a-constant-and-a-projection-of-a-variable-has-no-parentheses"
]

(* a sequence and its type show in brackets, and the type at a list of types that is no literal as Sequence @@ As *)
VerificationTest[
	With[{wolfram = TypeTheoryEnvironment["Prelude"]},
		{
			Cases[ToBoxes[TypeTheoryType[TypeTheoryTerm[Sequence[1, 2], wolfram]]] //. (StyleBox | TooltipBox)[name_, ___] :> name, TemplateBox[{"\"[\"", _, "\"]\""}, "RowDefault"], Infinity] =!= {},
			Cases[ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[Sequence[1, 2], wolfram]]], TemplateBox[{"\"[\"", _, "\"]\""}, "RowDefault"], Infinity] =!= {},
			Cases[ToBoxes[TypeTheoryType[TypeTheoryTerm[{Typed[As, {TypeUniverse[1]}], Typed[s, Sequence[As]]} |-> s, wolfram]]] //. (StyleBox | TooltipBox)[name_, ___] :> name, RowBox[{"Sequence", "@@", "As"}], Infinity] =!= {}
		}
	],
	{True, True, True},
	TestID -> "A-sequence-and-its-type-show-in-brackets"
]

(* every part with a type shows it on mouseover: an operator the type of the constant it is,
   which elaboration decides, ℕ → ℕ → ℕ for + of natural numbers and Expressions for an operator of an expression, as
   - in n x^(n - 1), a number its type, a constant of System, as Replace and AtomQ, on its name and brackets, and ↦ the
   type of its function; successor[k], shown as k + 1, shows the successor's type, beside the sum k + 1 *)
boxText[boxes_] := StringDelete[StringJoin[Cases[boxes //. {TooltipBox[shown_, ___] :> shown, StyleBox[shown_, ___] :> shown, TemplateBox[{items___}, ___] :> RowBox[{items}]}, _String, {0, Infinity}]], "\""]
typeTips[term_] := Cases[ToBoxes[term], TooltipBox[shown_, tip_, ___] :> {boxText[shown], boxText[tip]}, Infinity]

VerificationTest[
	With[
		{
			natural = typeTips[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, k + 0 == k - 1]]],
			power = typeTips[TypeTheoryTerm[ForAll[{Typed[n, Expressions]}, Replace[d[x^n], d[x^m_] :> m x^(m - 1)] == n x^(n - 1)]]],
			atom = typeTips[TypeTheoryTerm[Typed[e, Expressions] |-> AtomQ[e]]],
			successor = typeTips[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, "successor"[k] == k + 1]]],
			quoted = typeTips[TypeTheoryTerm[Unevaluated[1 + 2 + x]]]
		},
		{
			SubsetQ[natural, {{"+", "\[DoubleStruckCapitalN]\[RightArrow]\[DoubleStruckCapitalN]\[RightArrow]\[DoubleStruckCapitalN]"}, {"-", "\[DoubleStruckCapitalN]\[RightArrow]\[DoubleStruckCapitalN]\[RightArrow]\[DoubleStruckCapitalN]"}, {"0", "\[DoubleStruckCapitalN]"}, {"1", "\[DoubleStruckCapitalN]"}, {"\[DoubleStruckCapitalN]", "Type"}}],
			StringEndsQ[Last[SelectFirst[natural, First[#] === "\[Equal]" &]], "Prop"],
			SubsetQ[power, {{"Replace", "Expressions\[RightArrow](Expressions\[RightArrow]Match[Expressions])\[RightArrow]Expressions"}, {"d", "Expressions"}, {"x", "Expressions"}, {"-", "Expressions"}, {"1", "Expressions"}}],
			SubsetQ[atom, {{"AtomQ", "Expressions\[RightArrow]\[DoubleStruckCapitalB]"}, {"[", "Expressions\[RightArrow]\[DoubleStruckCapitalB]"}, {"\[RightTeeArrow]", "Expressions\[RightArrow]\[DoubleStruckCapitalB]"}}],
			Select[successor, First[#] === "+" &],
			Union[Last /@ quoted]
		}
	],
	{
		True, True, True, True,
		{{"+", "\[DoubleStruckCapitalN]\[RightArrow]\[DoubleStruckCapitalN]"}, {"+", "\[DoubleStruckCapitalN]\[RightArrow]\[DoubleStruckCapitalN]\[RightArrow]\[DoubleStruckCapitalN]"}},
		{"Expressions"}
	},
	TestID -> "Operators-numbers-and-symbols-show-their-types-on-mouseover"
]

(* the types on mouseover change nothing a term shows: its boxes with them left out are its boxes without them *)
VerificationTest[
	With[{integers = TypeTheoryEnvironment["Integers"], rationals = TypeTheoryEnvironment["Rationals"]},
		Map[
			Function[term, shownBoxes[term] === Block[{WolframInstitute`TypeTheory`PackageScope`$displayTooltips = False}, shownBoxes[term]]],
			{
				TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, k + 0 == k - 1]],
				TypeTheoryTerm[ForAll[{Typed[n, Expressions]}, Replace[d[x^n], d[x^m_] :> m x^(m - 1)] == n x^(n - 1)]],
				TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, "successor"[k] == k + 1]],
				TypeTheoryTerm[ForAll[{Typed[a, Integers], Typed[b, Integers]}, a - 1 < a + 2 && -a <= a b], integers],
				TypeTheoryTerm[ForAll[{Typed[a, Rationals], Typed[b, Rationals]}, a / b == a - 1/2 + 1/2], rationals],
				TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[p && q, q || ! p]]],
				TypeTheoryTerm[Typed[l, {NonNegativeIntegers}] |-> Length[Prepend[l, 1]] + 2 * 3^2],
				TypeTheoryTerm[Unevaluated[1 + 2 x - 3/4]],
				NormalForm[TypeTheoryTerm[Replace[d[x^3], d[x^m_] :> m x^(m - 1)]]],
				TypeTheoryTerm["pair"[1, "pair"[2, 3]]]
			}
		]
	],
	ConstantArray[True, 10],
	TestID -> "The-types-on-mouseover-change-nothing-a-term-shows"
]

(* a variable the term binds shows by its name also where another symbol of that name shadows it, as a variable of a
   notebook's context is shadowed by one of the context that is current: its context never shows *)
VerificationTest[
	Module[{term, boxes},
		term = ToExpression["TypeTheoryTerm[Function[{Typed[ShadowedTest`shadowed, NonNegativeIntegers]}, ShadowedTest`shadowed + 1]]"];
		ToExpression["ShadowingTest`shadowed"];
		boxes = Block[{$Context = "ShadowingTest`", $ContextPath = {"System`", "ShadowedTest`", "WolframInstitute`TypeTheory`"}}, ToBoxes[term]];
		{
			FreeQ[First[boxes], text_String /; StringContainsQ[text, "ShadowedTest`"]],
			! FreeQ[First[boxes], text_String /; StringContainsQ[text, "shadowed"]]
		}
	],
	{True, True},
	TestID -> "A-bound-variable-that-another-symbol-shadows-shows-by-its-name"
]


(* A coercion of the user's shows as ↑x, as the library's do; a class of a pair of literals of the integers as the
   integer it stands for; and a head whose rule of MakeBoxes for every form makes a summary box, an object's display, as
   PureMath's do, is no notation in StandardForm, where the term shows its parts, while its rule for TraditionalForm
   shows there. *)
SummarizedThing /: MakeBoxes[thing : SummarizedThing[_, _], form_] := summarizedBoxes[thing, form]
summarizedBoxes[thing_, form_] := BoxForm`ArrangeSummaryBox[SummarizedThing, thing, None, {BoxForm`SummaryItem[{"Parts: ", 2}]}, {}, form]
SummarizedThing /: MakeBoxes[SummarizedThing[a_, b_], TraditionalForm] := RowBox[{MakeBoxes[a, TraditionalForm], "\[EmptySquare]", MakeBoxes[b, TraditionalForm]}]

VerificationTest[
	Module[{plain, wrapped, summarized, wrappedTerm, summarizedTerm},
		plain[boxes_] := boxes //. (StyleBox | TooltipBox | TagBox)[shown_, ___] :> shown;
		wrapped = TypeTheoryEnvironment[prelude, {
			TypeTheoryInductiveType["Wrapped", TypeUniverse[0], {"wrap" -> TypeSpecifier[{NonNegativeIntegers} -> "Wrapped"]}],
			TypeTheoryDefinition["wrapNatural", Function[{Typed[n, NonNegativeIntegers]}, "wrap"[n]], "Coercion" -> True]
		}];
		summarized = TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[SummarizedThing, Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n + m]]}];
		(* the term read back, where elaboration has put the coercion in *)
		wrappedTerm = WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[k, NonNegativeIntegers]}, Typed[k, "Wrapped"]], wrapped]];
		summarizedTerm = TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, SummarizedThing[x, 1] == x + 1], summarized];
		{
			{! FreeQ[plain[ToBoxes[wrappedTerm, StandardForm]], "\"\[UpArrow]\""], FreeQ[plain[ToBoxes[wrappedTerm, StandardForm]], "\"wrapNatural\""]},
			MemberQ[{"-3", RowBox[{"-", "3"}]}, First[plain[ToBoxes[TypeTheoryTerm[QuotientIntroduction["integerRelation", "pair"[2, 5]], "Integers"], StandardForm]]]],
			FreeQ[ToBoxes[summarizedTerm, StandardForm], "SummaryHead" | "SummaryPanel"],
			! FreeQ[ToBoxes[summarizedTerm, TraditionalForm], "\[EmptySquare]"]
		}
	],
	{{True, True}, True, True, True},
	TestID -> "User-coercions-integers-and-objects-with-summary-boxes-show-as-the-library's-terms-do"
]
