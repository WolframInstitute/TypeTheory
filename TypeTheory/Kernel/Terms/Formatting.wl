(* ::Package:: *)

(*
Formatting: how terms and proofs look in a notebook.

A TypeTheoryTerm shows its term in mathematical notation. The display is built from built-in operators,
so the Wolfram Language's own typesetting decides where parentheses go:

	Typed[x, A]                         x ∶ A                Colon
	Annotation[Typed[x, A], kind]       {x ∶ A}, ⦃x ∶ A⦄, [x ∶ A]
	ForAll[{b1, b2}, B]                 ∀_b1 ∀_b2 B          ForAll, one binder at a time
	Exists[{b}, B]                      ∃_b B
	Function[{b1, b2}, t]               (b1) (b2) ↦ t        RightTeeArrow
	Implies[A, Implies[B, C]]           A ⇒ B ⇒ C            DoubleRightArrow
	TypeSpecifier[{A, B} -> C]          A → B → C            RightArrow
	RightTee[{h1, h2}, T]               h1, h2 ⊢ T
	TypeUniverse[0], [1], [u + 1], [u]  Prop, Type, Type u, Sort u
	NonNegativeIntegers                 ℕ
	InductiveRecursor[I]                I_rec
	And[a, b], Or[a, b], Not[a]         a ∧ b, a ∨ b, ¬a
	zero, successor[n]                  0, n + 1             the natural numbers of the term's environment, as Lean shows them

The display rewrites the syntax tree of the term with these operators, rebuilds it held, and takes its
boxes with MakeBoxes; InterpretationBox keeps the term itself behind the display. The bound variables of
the prelude and of generated recursors are symbols of the paclet's private contexts, shown by their names.

A TypeTheoryProof shows its open goals as a list of hypotheses over the goal, as in a proof assistant's
goal view. A declaration shows as its keyword, its name and its type, as in a proof assistant's source.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[typeTheoryBoxes]
PackageScoped[displaySyntax]


(* ::Section:: *)
(*Usage Messages*)


typeTheoryBoxes::usage = "typeTheoryBoxes[syntax, form] gives boxes showing the syntax tree of a term in mathematical notation."
displaySyntax::usage = "displaySyntax[syntax] rewrites the syntax tree of a term with the built-in operators that show it in mathematical notation."


(* ::Section:: *)
(*Function Definitions*)


typeTheoryBoxes[syntax_, form_] := Block[{$displayedNaturalNumbers = displayedNaturalNumbers[]},
	logicalOperatorBoxes @ Replace[heldFromSyntax[displaySyntax[syntax]], HoldComplete[display_] :> MakeBoxes[display, form]]
]

TypeTheoryTerm /: MakeBoxes[term : TypeTheoryTerm[expression_, ___], form : StandardForm | TraditionalForm] := With[
	{boxes = withDisplayEnvironment[termEnvironment[term], typeTheoryBoxes[toSyntax[expression], form]]},
	InterpretationBox[boxes, term]
]

(* the natural numbers a display shows as 0 and n + 1: those of the environment shown, and outside one, as
   in a declaration, the prelude's *)
$displayedNaturalNumbers = Automatic

SetAttributes[withDisplayEnvironment, HoldRest]
withDisplayEnvironment[environment_, expression_] := Block[{$displayedNaturalNumbers = settingsOrNone[environment]}, expression]

displayedNaturalNumbers[] := Replace[$displayedNaturalNumbers, Automatic :> settingsOrNone[preludeEnvironment[]]]

settingsOrNone[environment_] := Replace[Quiet[naturalNumberSettings[environment]], Except[_Association] -> <||>]

naturalNumberConstantQ[syntaxSymbol[name_HoldComplete], key_String] := Lookup[displayedNaturalNumbers[], key, None] === name
naturalNumberConstantQ[syntaxString[name_String], key_String] := Lookup[displayedNaturalNumbers[], key, None] === HoldComplete[name]
naturalNumberConstantQ[_, _] := False

(* And, Or and Not show as ∧, ∨ and ¬, with the parentheses MakeBoxes chose for &&, || and !; deeper boxes
   are replaced first *)
logicalOperatorBoxes[boxes_] := Replace[
	boxes,
	{
		RowBox[{"!", operand_}] :> RowBox[{"\[Not]", operand}],
		RowBox[operands : {_, "&&", __}] :> RowBox[Replace[operands, "&&" -> "\[And]", {1}]],
		RowBox[operands : {_, "||", __}] :> RowBox[Replace[operands, "||" -> "\[Or]", {1}]]
	},
	{0, Infinity}
]

SetAttributes[privateNameQ, HoldAllComplete]
privateNameQ[symbol_Symbol] := With[{context = Context[Unevaluated[symbol]]},
	StringStartsQ[context, "WolframInstitute`TypeTheory`"] && context =!= "WolframInstitute`TypeTheory`"
]


(* ::Subsection:: *)
(*Notation*)


(* the arguments are rewritten first, so each rule sees displayed arguments *)
displaySyntax[syntaxApplication[head_, arguments_List]] := displayApplication[head, displaySyntax /@ arguments]
displaySyntax[syntaxSymbol[HoldComplete[NonNegativeIntegers]]] := syntaxString["\[DoubleStruckCapitalN]"]
displaySyntax[name : syntaxSymbol[_] | syntaxString[_]] /; naturalNumberConstantQ[name, "Zero"] := syntaxInteger[0]
displaySyntax[syntaxSymbol[HoldComplete[symbol_Symbol]]] /; privateNameQ[symbol] := syntaxString[SymbolName[Unevaluated[symbol]]]
displaySyntax[syntax_] := syntax

displayApplication[syntaxSymbol[HoldComplete[Typed]], {term_, type_}] := syntaxHead[Colon, {term, type}]
displayApplication[syntaxSymbol[HoldComplete[Annotation]], {binder_, syntaxString[kind : "Implicit" | "StrictImplicit" | "InstanceImplicit"]}] :=
	Replace[kind, {
		"Implicit" :> delimited["{", binder, "}"],
		"StrictImplicit" :> delimited["\:2983", binder, "\:2984"],
		"InstanceImplicit" :> delimited["[", binder, "]"]
	}]
displayApplication[syntaxSymbol[HoldComplete[head : ForAll | Exists]], {binders_, body_}] := Fold[
	Function[{accumulated, binder}, syntaxHead[head, {binder, accumulated}]],
	body,
	Reverse[listElements[binders]]
]
displayApplication[syntaxSymbol[HoldComplete[Function]], {binders_, body_}] := syntaxHead[RightTeeArrow, {binderRow[listElements[binders]], body}]
displayApplication[syntaxSymbol[HoldComplete[Implies]], {domain_, codomain_}] := arrowChain[DoubleRightArrow, {domain}, codomain]
displayApplication[syntaxSymbol[HoldComplete[TypeSpecifier]], {syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {domains_, codomain_}]}] :=
	arrowChain[RightArrow, listElements[domains], codomain]
displayApplication[syntaxSymbol[HoldComplete[RightTee]], {syntaxApplication[syntaxSymbol[HoldComplete[List]], {}], goal_}] :=
	syntaxHead[Row, {syntaxHead[List, {syntaxString["\[RightTee] "], goal}]}]
displayApplication[syntaxSymbol[HoldComplete[RightTee]], {hypotheses_, goal_}] :=
	syntaxHead[RightTee, {syntaxHead[Row, {syntaxHead[List, listElements[hypotheses]], syntaxString[", "]}], goal}]
displayApplication[syntaxSymbol[HoldComplete[TypeUniverse]], {level_}] := universeDisplay[level]
displayApplication[syntaxSymbol[HoldComplete[InductiveRecursor]], {type_}] := syntaxHead[Subscript, {type, syntaxString["rec"]}]
(* successors of successors add up from the left, n + 1 + 1, as Lean writes them *)
displayApplication[head_, {syntaxApplication[syntaxSymbol[HoldComplete[Plus]], summands_List]}] /; naturalNumberConstantQ[head, "Successor"] :=
	syntaxHead[Plus, Append[summands, syntaxInteger[1]]]
displayApplication[head_, {argument_}] /; naturalNumberConstantQ[head, "Successor"] := syntaxHead[Plus, {argument, syntaxInteger[1]}]
displayApplication[head_, arguments_List] := syntaxApplication[displaySyntax[head], arguments]

listElements[syntaxApplication[syntaxSymbol[HoldComplete[List]], elements_List]] := elements
listElements[single_] := {single}

delimited[left_String, syntax_, right_String] := syntaxHead[Row, {syntaxHead[List, {syntaxString[left], syntax, syntaxString[right]}]}]

(* several binders are each parenthesized, unless their brackets already delimit them *)
binderRow[{binder_}] := binder
binderRow[binders_List] := syntaxHead[Row, {
	syntaxHead[List, Replace[binders, colon : syntaxApplication[syntaxSymbol[HoldComplete[Colon]], _] :> delimited["(", colon, ")"], {1}]],
	syntaxString[" "]
}]

(* a chain of arrows nested to the right is shown flat: A ⇒ B ⇒ C *)
arrowChain[operator_Symbol, domains_List, syntaxApplication[syntaxSymbol[HoldComplete[operator_]], rest_List]] := syntaxHead[operator, Join[domains, rest]]
arrowChain[operator_Symbol, domains_List, codomain_] := syntaxHead[operator, Append[domains, codomain]]

universeDisplay[syntaxInteger[0]] := syntaxString["Prop"]
universeDisplay[syntaxInteger[1]] := syntaxString["Type"]
universeDisplay[syntaxInteger[n_Integer]] := sortDisplay["Type", syntaxInteger[n - 1]]
universeDisplay[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {level_, syntaxInteger[1]}]] := sortDisplay["Type", level]
universeDisplay[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {level_, syntaxInteger[n_Integer]}]] :=
	sortDisplay["Type", syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {level, syntaxInteger[n - 1]}]]
universeDisplay[level_] := sortDisplay["Sort", level]

(* a level that is a sum is parenthesized, as Lean writes it: Type (u + 1) *)
sortDisplay[keyword_String, level : syntaxApplication[syntaxSymbol[HoldComplete[Plus]], _]] := sortDisplay[keyword, delimited["(", level, ")"]]
sortDisplay[keyword_String, level_] := syntaxHead[Row, {syntaxHead[List, {syntaxString[keyword], level}], syntaxString[" "]}]


(* ::Subsection:: *)
(*Proofs*)


(* the display is not interpretable: a proof holds its environment, which a notebook should not store in every output *)
TypeTheoryProof /: MakeBoxes[TypeTheoryProof[data_Association], form : StandardForm | TraditionalForm] :=
	withDisplayEnvironment[data["Environment"], ToBoxes[proofPanel[data, form], form]]

proofPanel[data_, form_] := Framed[
	Column[Prepend[Function[goal, goalPanel[data, goal, form]] /@ data["Goals"], proofHeader[Length[data["Goals"]]]], Spacings -> 1.2],
	FrameStyle -> LightDarkSwitched[GrayLevel[0.8], GrayLevel[0.35]],
	RoundingRadius -> 4,
	FrameMargins -> 8
]

proofHeader[0] := Style["Proof complete", Bold, StandardGreen]
proofHeader[1] := Row[{Style["Proof", Bold], Style["  1 goal", StandardGray]}]
proofHeader[n_Integer] := Row[{Style["Proof", Bold], Style["  " <> ToString[n] <> " goals", StandardGray]}]

goalPanel[data_, goal_, form_] := Replace[Quiet @ catchKernelFailure[goalDisplaySyntax[data, goal]], {
	{case_, hypotheses_List, target_} :> Column[Join[
		Replace[case, {None -> {}, HoldComplete[name_] :> {Style[Row[{"case ", HoldForm[name]}], Italic, StandardGray]}}],
		Function[hypothesis, RawBoxes[typeTheoryBoxes[hypothesis, form]]] /@ hypotheses,
		{Row[{Style["\[RightTee] ", Bold], RawBoxes[typeTheoryBoxes[target, form]]}]}
	]],
	_ :> Style["The goal " <> ToString[goal] <> " cannot be displayed.", StandardRed]
}]


(* ::Subsection:: *)
(*Declarations*)


TypeTheoryAxiom /: MakeBoxes[declaration : TypeTheoryAxiom[name_, type_, ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, "axiom", {{toSyntax[name], toSyntax[type]}}, form]

TypeTheoryDefinition /: MakeBoxes[declaration : TypeTheoryDefinition[name_, Typed[value_, type_], ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, "definition", {{toSyntax[name], toSyntax[type], toSyntax[value]}}, form]
TypeTheoryDefinition /: MakeBoxes[declaration : TypeTheoryDefinition[name_, value_, ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, "definition", {{toSyntax[name], None, toSyntax[value]}}, form]

TypeTheoryTheorem /: MakeBoxes[declaration : TypeTheoryTheorem[name_, statement_, Except[_Rule | _RuleDelayed], ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, "theorem", {{toSyntax[name], toSyntax[statement]}}, form]

TypeTheoryInductiveType /: MakeBoxes[declaration : TypeTheoryInductiveType[name_, type_, constructors_List, ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[
		declaration,
		"inductive",
		Prepend[
			Cases[Unevaluated[constructors], (Rule | RuleDelayed)[constructor_, constructorType_] :> {toSyntax[constructor], toSyntax[constructorType]}],
			{toSyntax[name], toSyntax[type]}
		],
		form
	]

(* the keyword, then name : type (:= value), with each constructor of an inductive type on a line of its own *)
declarationBoxes[declaration_, keyword_String, {first_, constructors___}, form_] := With[
	{
		rows = Join[
			{Join[{StyleBox[keyword, FontWeight -> Bold, FontColor -> StandardBlue]}, declarationRow[first, form]]},
			Function[constructor, Join[{"|"}, declarationRow[constructor, form]]] /@ {constructors}
		]
	},
	InterpretationBox[GridBox[rows, GridBoxAlignment -> {"Columns" -> {{Left}}}, GridBoxSpacings -> {"Columns" -> {{0.6}}}], declaration]
]

declarationRow[{name_, type_}, form_] := {nameBoxes[name, form], ":", typeTheoryBoxes[type, form]}
declarationRow[{name_, None, value_}, form_] := {nameBoxes[name, form], ":=", typeTheoryBoxes[value, form]}
declarationRow[{name_, type_, value_}, form_] := {nameBoxes[name, form], ":", RowBox[{typeTheoryBoxes[type, form], " := ", typeTheoryBoxes[value, form]}]}

(* a declared name shows as itself: the constructor NaturalNumberZero is not shown as 0 where it is declared *)
nameBoxes[name_, form_] := Block[{$displayedNaturalNumbers = <||>}, typeTheoryBoxes[name, form]]
