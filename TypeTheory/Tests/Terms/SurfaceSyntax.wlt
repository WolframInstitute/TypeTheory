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
		Function[term, With[{boxes = ToBoxes[term]}, {
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
		ToBoxes[TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne]],
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

VerificationTest[
	FreeQ[ToBoxes[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, "successor"["successor"[k]] == k + 2]]] //. (StyleBox | TooltipBox)[name_, ___] :> name, RowBox[{"k", "+", "1", "+", "1"}]],
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
		Cases[ToBoxes[TypeTheoryTerm[CartesianProductType[NonNegativeIntegers, CartesianProductType[Booleans, Integers]]]], RowBox[{_, "\[Times]", _, "\[Times]", _}], Infinity] =!= {},
		Cases[ToBoxes[TypeTheoryTerm[CartesianProductType[CartesianProductType[NonNegativeIntegers, Booleans], Integers]]], RowBox[{RowBox[{"(", _, ")"}], "\[Times]", _}], Infinity] =!= {},
		Cases[ToBoxes[TypeTheoryTerm[DisjointUnionType[CartesianProductType[NonNegativeIntegers, Booleans], Booleans]]], RowBox[{RowBox[{_, "\[Times]", _}], "\[CirclePlus]", _}], Infinity] =!= {},
		FreeQ[ToBoxes[TypeTheoryTerm[DisjointUnionType[NonNegativeIntegers, CartesianProductType[NonNegativeIntegers, Booleans]]]], "CartesianProductType" | "DisjointUnionType" | "\[Cross]"],
		Cases[ToBoxes[TypeTheoryTerm[CircleTimes[A, B]]], RowBox[{"A", "\[CircleTimes]", "B"}], Infinity] =!= {}
	},
	{True, True, True, True, True},
	TestID -> "Products-and-sums-of-types-show-as-times-and-circle-plus"
]

VerificationTest[
	{
		Cases[ToBoxes[TypeTheoryTerm["pair"[1, "pair"[2, 3]]]], TemplateBox[{"\"(\"", TemplateBox[{", ", "\", \"", "1", "2", "3"}, "RowWithSeparators"], "\")\""}, "RowDefault"], Infinity] =!= {},
		Cases[ToBoxes[TypeTheoryTerm["dependentPair"[1, 2]]], TemplateBox[{"\"\[LeftAngleBracket]\"", TemplateBox[{", ", "\", \"", "1", "2"}, "RowWithSeparators"], "\"\[RightAngleBracket]\""}, "RowDefault"], Infinity] =!= {}
	},
	{True, True},
	TestID -> "Pairs-show-as-tuples-and-dependent-pairs-in-angle-brackets"
]

VerificationTest[
	{
		Cases[ToBoxes[TypeTheoryTerm[Prepend[1][Prepend[2][{}]]]], TemplateBox[{"\"{\"", TemplateBox[{", ", "\", \"", "1", "2"}, "RowWithSeparators"], "\"}\""}, "RowDefault"], Infinity] =!= {},
		Cases[ToBoxes[TypeTheoryTerm[Prepend[Typed[{}, {NonNegativeIntegers}], 1]]], TemplateBox[{"\"{\"", TemplateBox[{", ", "\", \"", "1"}, "RowWithSeparators"], "\"}\""}, "RowDefault"], Infinity] =!= {},
		Cases[ToBoxes[TypeTheoryTerm[Join[l, {}]]], RowBox[{"{", "}"}], Infinity],
		FreeQ[ToBoxes[TypeTheoryTerm[Prepend[1][l]]], "Prepend"]
	},
	{True, True, {RowBox[{"{", "}"}]}, False},
	TestID -> "A-list-ending-in-the-empty-list-shows-its-elements-in-braces"
]

(* a list type shows as it is written, {A}, and lists of lists {{A}}; a constant named by a symbol, a type or a function,
   shows in bold, so that it is told apart from a constant named by a string, which shows as the string does, as a value does *)
VerificationTest[
	With[
		{
			lists = ToBoxes[TypeTheoryTerm[{{NonNegativeIntegers}}]],
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
			Length[Cases[ToBoxes[TypeTheoryTerm[TypeSpecifier[{Polynomial} -> {Polynomial}], named]], StyleBox["Polynomial", Bold, ___], Infinity]],
			FreeQ[ToBoxes[TypeTheoryTerm[TypeSpecifier[{"Polynomials"} -> {"Polynomials"}], named]], StyleBox],
			FreeQ[ToBoxes[TypeTheoryTerm[Typed["zeroPolynomial", "Polynomials"], named]], StyleBox],
			FreeQ[ToBoxes[TypeTheoryTerm[True && False]], StyleBox],
			Sort[Cases[ToBoxes[TypeTheoryTerm[degree[zero], named]] /. TooltipBox[boxes_, ___] :> boxes, StyleBox[name_String, Bold, ___] :> name, Infinity]],
			FreeQ[ToBoxes[TypeTheoryTerm[Function[Typed[zero, NonNegativeIntegers], zero], named]], StyleBox[_, Bold, ___]]
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
	{InterpretationBox["3", TypeTheoryTerm["rationalOfPair"["pair"[3, 0]]]], {FractionBox["5", "2"]}},
	TestID -> "A-class-of-a-pair-with-a-literal-denominator-still-shows-as-a-fraction"
]

VerificationTest[
	Cases[
		ToBoxes[TypeTheoryTerm[Subtype[Function[{Typed[n, NonNegativeIntegers]}, 2 <= n]]]] //. (StyleBox | TooltipBox)[name_, ___] :> name,
		TemplateBox[{"\"{\"", TemplateBox[{RowBox[{"n", "\[Colon]", _}], "\" // \"", _}, "RowDefault"], "\"}\""}, "RowDefault"],
		Infinity
	] =!= {},
	True,
	TestID -> "A-subtype-shows-as-Lean-shows-it"
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
			DeleteDuplicates[styled[ToBoxes[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]]]] === {{"n", colors["BoundVariable"]}},
			DeleteDuplicates[styled[ToBoxes[TypeTheoryType[TypeTheoryTerm[List]]]]],
			FreeQ[styled[ToBoxes[TypeTheoryTerm[TypeUniverse[1]]]], colors["Level"]],
			MemberQ[
				styled[ToBoxes[TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], {TypeTheoryTactic["Introduce"]}]]],
				{"n", colors["BoundVariable"]}
			],
			ToBoxes[TypeTheoryTerm[TypeUniverse[Placeholder["?u3"]]]] =!= {} && ! FreeQ[
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

(* on mouseover a constant shows its declared type and a bound variable the type its binder gives, drawn without
   tooltips of their own *)
VerificationTest[
	With[{tips = Function[boxes, Cases[boxes, TooltipBox[shown_, tip_, ___] :> {shown /. StyleBox[inner_, ___] :> inner, FreeQ[tip, TooltipBox]}, Infinity]]},
		{
			DeleteDuplicates[tips[ToBoxes[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]]]],
			First[tips[ToBoxes[TypeTheoryTerm["andIntroduction"]]]],
			Block[{WolframInstitute`TypeTheory`PackageScope`$displayTooltips = False}, FreeQ[ToBoxes[TypeTheoryTerm["andIntroduction"]], TooltipBox]]
		}
	],
	{{{"n", True}}, {"\"andIntroduction\"", True}, True},
	TestID -> "A-constant-and-a-bound-variable-show-their-types-on-mouseover"
]

(* a constant applied shows as f[x], its name in bold with its type on mouseover, not as (f)[x]; a symbol of a paclet as
   documentation copies it, PacletSymbol[paclet, name], reads as the symbol it names *)
VerificationTest[
	With[{spaces = TypeTheoryEnvironment[prelude, {TypeTheoryAxiom[ModularSpace, NonNegativeIntegers -> TypeUniverse[1]]}]},
		{
			First[ToBoxes[TypeTheoryTerm[ModularSpace[12], spaces]]] /. TooltipBox[shown_, ___] :> shown,
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

(* a sequence and its type show in brackets, and the type at a list of types that is no literal as Sequence @@ As *)
VerificationTest[
	With[{wolfram = TypeTheoryEnvironment["WolframLanguage"]},
		{
			Cases[ToBoxes[TypeTheoryType[TypeTheoryTerm[Sequence[1, 2], wolfram]]] //. (StyleBox | TooltipBox)[name_, ___] :> name, TemplateBox[{"\"[\"", _, "\"]\""}, "RowDefault"], Infinity] =!= {},
			Cases[ToBoxes[WeakHeadNormalForm[TypeTheoryTerm[Sequence[1, 2], wolfram]]], TemplateBox[{"\"[\"", _, "\"]\""}, "RowDefault"], Infinity] =!= {},
			Cases[ToBoxes[TypeTheoryType[TypeTheoryTerm[{Typed[As, {TypeUniverse[1]}], Typed[s, Sequence[As]]} |-> s, wolfram]]] //. (StyleBox | TooltipBox)[name_, ___] :> name, RowBox[{"Sequence", "@@", "As"}], Infinity] =!= {}
		}
	],
	{True, True, True},
	TestID -> "A-sequence-and-its-type-show-in-brackets"
]
