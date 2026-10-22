(* ::Package:: *)

(*
Formatting: how terms and proofs look in a notebook.

A TypeTheoryTerm shows its term in mathematical notation. The display is built from built-in operators,
so the Wolfram Language's own typesetting decides where parentheses go:

	Typed[x, A]                         x ∶ A                Colon
	TypedImplicit[x, A]                 {x ∶ A}
	Typed[x, A, q], TypedImplicit[x, A, q]   q x ∶ A, {q x ∶ A}   the quantity first, as Idris writes it
	Annotation[Typed[x, A], kind]       {x ∶ A}, ⦃x ∶ A⦄, [x ∶ A]
	ForAll[{b1, b2}, B]                 ∀_b1 ∀_b2 B          ForAll, one binder at a time
	Exists[{b}, B]                      ∃_b B
	Function[{b1, b2}, t]               (b1) (b2) ↦ t        RightTeeArrow
	Implies[A, Implies[B, C]]           A ⇒ B ⇒ C            DoubleRightArrow
	TypeSpecifier[{A, B} -> C]          A → B → C            RightArrow
	RightTee[{h1, h2}, T]               h1, h2 ⊢ T
	TypeUniverse[0], [1], [u + 1], [u]  Prop, Type, Type u, Sort u
	TypeUniverse[Max[1, u]]             Sort (max 1 u)
	TypeUniverse[Max[u + 1, v + 1]]     Type (max u v)
	NonNegativeIntegers                 ℕ
	InductiveRecursor[I]                I_rec
	InductiveRecursor[I, k]             I_rec_k              the recursor on the k-th type I's block nests
	And[a, b], Or[a, b], Not[a]         a ∧ b, a ∨ b, ¬a
	Booleans, "true", "false"          𝔹, true, false       a constant named by a string shows as the string
	Circle                              𝕊¹                   the circle of the HoTT environment
	"and", "or", "not"                  a && b, a || b, !a   as Lean writes them for its Bool
	Integers                            ℤ                    the integers of TypeTheoryEnvironment["Integers"]
	"integerAddition" and the others    x + y, x y, x - y, -x, x^n, x ≤ y, ...   as the natural numbers' operations
	"integerOfNatural"[n]               ↑n, or the literal n itself
	Rationals                           ℚ                    the rationals of TypeTheoryEnvironment["Rationals"]
	"rationalAddition" and the others   x + y, x y, x - y, -x, x^n, x^-1, x / y, x ≤ y, ...   as the integers' operations
	"rationalOfInteger"[x]              ↑x, or the literal itself
	"rationalOfPair"[Pair[a, b]]        a / (b + 1), and a where b is 0, for a literal b
	zero, successor[n]                  0, n + 1             the natural numbers of the term's environment, as Lean shows them
	NaturalNumberPredecessor[n]         n - 1
	IntervalZero, IntervalOne           0, 1                 the endpoints of the interval of cubical type theory
	IntervalMeet, IntervalJoin, IntervalReverse   r ∧ s, r ∨ s, ~r
	Path[Function[{i}, A], a, b]        a ≡ b                Congruent, where the line is constant

The display rewrites the syntax tree of the term with these operators, rebuilds it held, and takes its
boxes with MakeBoxes; InterpretationBox keeps the term itself behind the display. The bound variables of
the prelude and of generated recursors are symbols of the paclet's private contexts, shown by their names.

A TypeTheoryProof shows its open goals as a list of hypotheses over the goal, as in a proof assistant's
goal view. A declaration shows as its keyword, its name and its type, as in a proof assistant's source;
a rewrite rule shows its two sides as lhs ⟶ rhs, apart from the arrow of function types.
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


(* Naturals, written for the natural numbers, shows as they do, unless the term binds a variable of that name *)
typeTheoryBoxes[syntax_, form_] := Block[
	{
		$displayedNaturalNumbers = displayedNaturalNumbers[],
		$naturalsBound = ! FreeQ[syntax, syntaxApplication[syntaxSymbol[HoldComplete[Typed | TypedImplicit]], {syntaxSymbol[HoldComplete[Naturals]], __}]]
	},
	quantifiedOperandBoxes @ logicalOperatorBoxes @ Replace[heldFromSyntax[displaySyntax[syntax]], HoldComplete[display_] :> MakeBoxes[display, form]]
]

TypeTheoryTerm /: MakeBoxes[term : TypeTheoryTerm[expression_, ___], form : StandardForm | TraditionalForm] := With[
	{boxes = withDisplayEnvironment[termEnvironment[term], typeTheoryBoxes[toSyntax[expression], form]]},
	InterpretationBox[boxes, term]
]

(* the natural numbers a display shows as 0 and n + 1: those of the environment shown, and outside one, as
   in a declaration, the default environment's *)
$displayedNaturalNumbers = Automatic

SetAttributes[withDisplayEnvironment, HoldRest]
withDisplayEnvironment[environment_, expression_] := Block[{$displayedNaturalNumbers = settingsOrNone[environment]}, expression]

displayedNaturalNumbers[] := Replace[$displayedNaturalNumbers, Automatic :> settingsOrNone[defaultEnvironment[]]]

settingsOrNone[environment_] := Replace[Quiet[naturalNumberSettings[environment]], Except[_Association] -> <||>]

naturalNumberConstantQ[syntaxSymbol[name_HoldComplete], key_String] := Lookup[displayedNaturalNumbers[], key, None] === name
naturalNumberConstantQ[syntaxString[name_String], key_String] := Lookup[displayedNaturalNumbers[], key, None] === HoldComplete[name]
naturalNumberConstantQ[_, _] := False

(* And, Or and Not show as ∧, ∨ and ¬, with the parentheses MakeBoxes chose for &&, || and !; deeper boxes
   are replaced first. The operations on Booleans are shown as Nand, Nor and PlusMinus, which have the
   precedences of && and || and bind tighter than !, and then take the symbols &&, || and !. *)
logicalOperatorBoxes[boxes_] := Replace[
	Replace[
		boxes,
		{
			RowBox[{"!", operand_}] :> RowBox[{"\[Not]", operand}],
			RowBox[operands : {_, "&&", __}] :> RowBox[Replace[operands, "&&" -> "\[And]", {1}]],
			RowBox[operands : {_, "||", __}] :> RowBox[Replace[operands, "||" -> "\[Or]", {1}]]
		},
		{0, Infinity}
	],
	{
		RowBox[{"\[PlusMinus]", operand_}] :> RowBox[{"!", operand}],
		RowBox[operands : {_, "\[Nand]", __}] :> RowBox[Replace[operands, "\[Nand]" -> "&&", {1}]],
		RowBox[operands : {_, "\[Nor]", __}] :> RowBox[Replace[operands, "\[Nor]" -> "||", {1}]]
	},
	{0, Infinity}
]

(* A quantifier reaches as far right as it can, as Lean reads it, but for MakeBoxes ∀ binds tighter than
   ∧, ∨ and ⧦, so (∀x, p) ∧ q would show as ∀_x p ∧ q. An operand of those that ends with a quantifier,
   other than the last, is parenthesized, as MakeBoxes already does before ⇒ and ==; a notation given
   with MakeBoxes is parenthesized too. *)
quantifiedOperandBoxes[boxes_] := Replace[
	boxes,
	RowBox[operands : {_, _String, __}] /; OddQ[Length[operands]] && SubsetQ[$looseOperators, operands[[2 ;; ;; 2]]] :> RowBox[MapIndexed[
		Function[{operand, position}, If[OddQ[First[position]] && First[position] < Length[operands] && quantifierEndedQ[operand], RowBox[{"(", operand, ")"}], operand]],
		operands
	]],
	{0, Infinity}
]

$looseOperators = {"\[And]", "\[Or]", "\[Xor]", "\[Equivalent]", "\[Implies]"}

quantifierEndedQ[RowBox[{SubscriptBox["\[ForAll]" | "\[Exists]", _], _}]] := True
quantifierEndedQ[RowBox[{"\[Not]", operand_}]] := quantifierEndedQ[operand]
quantifierEndedQ[RowBox[{__, operator_String, last_}]] /; MemberQ[$looseOperators, operator] := quantifierEndedQ[last]
quantifierEndedQ[_] := False

SetAttributes[privateNameQ, HoldAllComplete]
privateNameQ[symbol_Symbol] := With[{context = Context[Unevaluated[symbol]]},
	StringStartsQ[context, "WolframInstitute`TypeTheory`"] && context =!= "WolframInstitute`TypeTheory`"
]


(* ::Subsection:: *)
(*Notation*)


(* the arguments are rewritten first, so each rule sees displayed arguments *)
displaySyntax[syntaxApplication[head_, arguments_List]] := displayApplication[head, displaySyntax /@ arguments]
displaySyntax[syntaxSymbol[HoldComplete[NonNegativeIntegers]]] := syntaxString["\[DoubleStruckCapitalN]"]
displaySyntax[syntaxSymbol[HoldComplete[Naturals]]] /; ! TrueQ[$naturalsBound] := syntaxString["\[DoubleStruckCapitalN]"]
displaySyntax[syntaxSymbol[HoldComplete[Integers]]] := syntaxString["\[DoubleStruckCapitalZ]"]
displaySyntax[syntaxSymbol[HoldComplete[Rationals]]] := syntaxString["\[DoubleStruckCapitalQ]"]
displaySyntax[syntaxSymbol[HoldComplete[Booleans]]] := syntaxString["\[DoubleStruckCapitalB]"]
displaySyntax[syntaxSymbol[HoldComplete[Circle]]] := syntaxString["\[DoubleStruckCapitalS]\:00b9"]
displaySyntax[syntaxSymbol[HoldComplete[IntervalZero]]] := syntaxInteger[0]
displaySyntax[syntaxSymbol[HoldComplete[IntervalOne]]] := syntaxInteger[1]
displaySyntax[name : syntaxSymbol[_] | syntaxString[_]] /; naturalNumberConstantQ[name, "Zero"] := syntaxInteger[0]
displaySyntax[syntaxSymbol[HoldComplete[symbol_Symbol]]] /; privateNameQ[symbol] := syntaxString[SymbolName[Unevaluated[symbol]]]
displaySyntax[syntax_] := syntax

displayApplication[syntaxSymbol[HoldComplete[Typed]], {term_, type_}] := syntaxHead[Colon, {term, type}]
displayApplication[syntaxSymbol[HoldComplete[TypedImplicit]], {term_, type_}] := delimited["{", syntaxHead[Colon, {term, type}], "}"]
displayApplication[syntaxSymbol[HoldComplete[head : Typed | TypedImplicit]], {term_, type_, quantity_}] :=
	displayApplication[syntaxSymbol[HoldComplete[head]], {syntaxHead[Row, {syntaxHead[List, {quantity, term}], syntaxString[" "]}], type}]
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
displayApplication[syntaxSymbol[HoldComplete[InductiveRecursor]], {type_, syntaxInteger[index_Integer]}] := syntaxHead[Subscript, {type, syntaxString["rec_" <> ToString[index]]}]
(* the operations of the interval show as cubical type theory writes them, and a path over a constant line as a ≡ b *)
displayApplication[syntaxSymbol[HoldComplete[IntervalMeet]], arguments : {_, _}] := syntaxHead[And, arguments]
displayApplication[syntaxSymbol[HoldComplete[IntervalJoin]], arguments : {_, _}] := syntaxHead[Or, arguments]
displayApplication[syntaxSymbol[HoldComplete[IntervalReverse]], {argument_}] := prefixed["~", argument]
displayApplication[
	syntaxSymbol[HoldComplete[Path]],
	{syntaxApplication[syntaxSymbol[HoldComplete[RightTeeArrow]], {syntaxApplication[syntaxSymbol[HoldComplete[Colon]], {name_, _}], body_}], left_, right_}
] /; FreeQ[body, name] := syntaxHead[Congruent, {left, right}]
(* the predecessor shows as n - 1, which it is by computation *)
displayApplication[syntaxSymbol[HoldComplete[NaturalNumberPredecessor]], {argument_}] := syntaxHead[Subtract, {argument, syntaxInteger[1]}]
(* (a && b) && c shows as a && b && c, the way Lean reads it *)
displayApplication[syntaxString["not"], {argument_}] := syntaxHead[PlusMinus, {argument}]
displayApplication[syntaxString["and"], {syntaxApplication[syntaxSymbol[HoldComplete[Nand]], rest_List], last_}] := syntaxHead[Nand, Append[rest, last]]
displayApplication[syntaxString["and"], arguments_List] := syntaxHead[Nand, arguments]
displayApplication[syntaxString["or"], {syntaxApplication[syntaxSymbol[HoldComplete[Nor]], rest_List], last_}] := syntaxHead[Nor, Append[rest, last]]
displayApplication[syntaxString["or"], arguments_List] := syntaxHead[Nor, arguments]
(* the integers' operations show as those of the natural numbers, which the types tell apart, as in Lean *)
displayApplication[syntaxString["integerAddition"], arguments_List] := displayApplication[syntaxSymbol[HoldComplete[Plus]], arguments]
displayApplication[syntaxString["integerMultiplication"], arguments_List] := displayApplication[
	syntaxSymbol[HoldComplete[Times]],
	(* a negative factor is parenthesized, 2 (-1), so it does not read as 2 - 1 *)
	Replace[arguments, negative : syntaxApplication[syntaxSymbol[HoldComplete[Row]], {syntaxApplication[syntaxSymbol[HoldComplete[List]], {syntaxString["-" | "-("], ___}]}] :> delimited["(", negative, ")"], {1}]
]
displayApplication[syntaxString["integerSubtraction"], arguments_List] := syntaxHead[Subtract, arguments]
displayApplication[syntaxString["integerPower"], arguments_List] := displayApplication[syntaxSymbol[HoldComplete[Power]], arguments]
displayApplication[syntaxString["integerNegation"], {argument_}] := prefixed["-", argument]
displayApplication[syntaxString["integerLessEqual"], arguments_List] := syntaxHead[LessEqual, arguments]
displayApplication[syntaxString["integerLess"], arguments_List] := syntaxHead[Less, arguments]
displayApplication[syntaxString["integerGreaterEqual"], arguments_List] := syntaxHead[GreaterEqual, arguments]
displayApplication[syntaxString["integerGreater"], arguments_List] := syntaxHead[Greater, arguments]
displayApplication[syntaxString["integerOfNatural"], {literal : syntaxInteger[_Integer]}] := literal
displayApplication[syntaxString["integerOfNatural"], {argument_}] := prefixed["\[UpArrow]", argument]
(* the rationals' operations show as the integers' do, an inverse as x^-1 and a division as x / y *)
displayApplication[syntaxString["rationalAddition"], arguments_List] := displayApplication[syntaxString["integerAddition"], arguments]
displayApplication[syntaxString["rationalMultiplication"], arguments_List] := displayApplication[syntaxString["integerMultiplication"], arguments]
displayApplication[syntaxString["rationalSubtraction"], arguments_List] := syntaxHead[Subtract, arguments]
displayApplication[syntaxString["rationalPower"], arguments_List] := displayApplication[syntaxSymbol[HoldComplete[Power]], arguments]
displayApplication[syntaxString["rationalNegation"], {argument_}] := prefixed["-", argument]
displayApplication[syntaxString["rationalInverse"], {argument_}] := syntaxHead[Power, {argument, syntaxInteger[-1]}]
displayApplication[syntaxString["rationalDivision"], arguments_List] := syntaxHead[Divide, arguments]
displayApplication[syntaxString["rationalLessEqual"], arguments_List] := syntaxHead[LessEqual, arguments]
displayApplication[syntaxString["rationalLess"], arguments_List] := syntaxHead[Less, arguments]
displayApplication[syntaxString["rationalGreaterEqual"], arguments_List] := syntaxHead[GreaterEqual, arguments]
displayApplication[syntaxString["rationalGreater"], arguments_List] := syntaxHead[Greater, arguments]
displayApplication[syntaxString["rationalOfInteger"], {literal : syntaxInteger[_Integer]}] := literal
displayApplication[syntaxString["rationalOfInteger"], {negative : syntaxApplication[syntaxSymbol[HoldComplete[Row]], {syntaxApplication[syntaxSymbol[HoldComplete[List]], {syntaxString["-"], syntaxInteger[_Integer]}]}]}] := negative
(* a natural number cast to an integer and then to a rational shows as Lean shows it, ↑↑n *)
displayApplication[
	syntaxString["rationalOfInteger"],
	{syntaxApplication[syntaxSymbol[HoldComplete[Row]], {syntaxApplication[syntaxSymbol[HoldComplete[List]], {syntaxString["\[UpArrow]"], inner_}]}]}
] := prefixed["\[UpArrow]\[UpArrow]", inner]
displayApplication[syntaxString["rationalOfInteger"], {argument_}] := prefixed["\[UpArrow]", argument]
(* a class of a pair with a literal denominator shows as the fraction it stands for, as computation gives it too *)
displayApplication[
	syntaxSymbol[HoldComplete[QuotientIntroduction]],
	{syntaxString["rationalRelation"], pair : syntaxApplication[syntaxSymbol[HoldComplete[Pair]], {_, syntaxInteger[_Integer]}]}
] := displayApplication[syntaxString["rationalOfPair"], {pair}]
displayApplication[syntaxString["rationalOfPair"], {syntaxApplication[syntaxSymbol[HoldComplete[Pair]], {numerator_, syntaxInteger[0]}]}] := numerator
displayApplication[syntaxString["rationalOfPair"], {syntaxApplication[syntaxSymbol[HoldComplete[Pair]], {numerator_, syntaxInteger[denominator_Integer]}]}] :=
	syntaxHead[Divide, {numerator, syntaxInteger[denominator + 1]}]

(* -x and ↑x, with an argument that is no name or number in parentheses, so x + -y keeps its sign and
   ↑(m + n) its sum *)
prefixed[sign_String, argument : (_syntaxSymbol | _syntaxString | _syntaxInteger)] := syntaxHead[Row, {syntaxHead[List, {syntaxString[sign], argument}]}]
prefixed[sign_String, argument_] := syntaxHead[Row, {syntaxHead[List, {syntaxString[sign <> "("], argument, syntaxString[")"]}]}]
(* (a + b) + c shows as a + b + c, and (a b) c as a b c, the way Lean reads + and * *)
displayApplication[syntaxSymbol[HoldComplete[head : Plus | Times]], {syntaxApplication[syntaxSymbol[HoldComplete[head_]], rest_List], last_}] :=
	syntaxHead[head, Append[rest, last]]
(* a ∧ (b ∧ c) shows as a ∧ b ∧ c, the way it is read *)
displayApplication[syntaxSymbol[HoldComplete[head_]], {first_, syntaxApplication[syntaxSymbol[HoldComplete[head_]], rest_List]}] /; MatchQ[head, And | Or] :=
	syntaxHead[head, Prepend[rest, first]]
(* successors of successors add up from the left, n + 1 + 1, as Lean writes them *)
displayApplication[head_, {syntaxApplication[syntaxSymbol[HoldComplete[Plus]], summands_List]}] /; naturalNumberConstantQ[head, "Successor"] :=
	syntaxHead[Plus, Append[summands, syntaxInteger[1]]]
displayApplication[head_, {argument_}] /; naturalNumberConstantQ[head, "Successor"] := syntaxHead[Plus, {argument, syntaxInteger[1]}]
displayApplication[head_, arguments_List] := syntaxApplication[displaySyntax[head], arguments]

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
(* a maximum of successors is a successor: Type (max u v), as Lean writes it *)
universeDisplay[syntaxApplication[syntaxSymbol[HoldComplete[Max]], levels_List]] /; AllTrue[levels, successorSyntaxQ] :=
	sortDisplay["Type", syntaxHead[Max, predecessorSyntax /@ levels]]
universeDisplay[level_] := sortDisplay["Sort", level]

successorSyntaxQ[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {_, syntaxInteger[_Integer?Positive]}]] := True
successorSyntaxQ[syntaxInteger[_Integer?Positive]] := True
successorSyntaxQ[_] := False

predecessorSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {level_, syntaxInteger[1]}]] := level
predecessorSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Plus]], {level_, syntaxInteger[n_Integer]}]] := syntaxHead[Plus, {level, syntaxInteger[n - 1]}]
predecessorSyntax[syntaxInteger[n_Integer]] := syntaxInteger[n - 1]

(* a level that is a sum or a maximum is parenthesized, as Lean writes it: Type (u + 1), Sort (max 1 u) *)
sortDisplay[keyword_String, level : syntaxApplication[syntaxSymbol[HoldComplete[Plus | Max | ImpredicativeMaximum]], _]] :=
	sortDisplay[keyword, levelArgumentDisplay[level]]
sortDisplay[keyword_String, level_] := syntaxHead[Row, {syntaxHead[List, {syntaxString[keyword], level}], syntaxString[" "]}]

levelArgumentDisplay[level : syntaxApplication[syntaxSymbol[HoldComplete[Plus]], _]] := delimited["(", level, ")"]
levelArgumentDisplay[syntaxApplication[syntaxSymbol[HoldComplete[head : Max | ImpredicativeMaximum]], levels_List]] := delimited[
	"(",
	syntaxHead[Row, {syntaxHead[List, Prepend[levelArgumentDisplay /@ levels, syntaxString[Replace[head, {Max -> "max", ImpredicativeMaximum -> "imax"}]]]], syntaxString[" "]}],
	")"
]
levelArgumentDisplay[level_] := level


(* ::Subsection:: *)
(*Proofs*)


(* the display is interpretable, as a term's is: copied or evaluated again it is the proof, which holds only a handle to its environment *)
TypeTheoryProof /: MakeBoxes[proof : TypeTheoryProof[data_Association], form : StandardForm | TraditionalForm] := With[
	{boxes = withDisplayEnvironment[data["Environment"], ToBoxes[proofPanel[data, form], form]]},
	InterpretationBox[boxes, proof]
]

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

TypeTheoryDefinition /: MakeBoxes[declaration : TypeTheoryDefinition[name_, Typed[value_, type_], options___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, definitionKeyword[Hold[options]], {{toSyntax[name], toSyntax[type], toSyntax[value]}}, form]
TypeTheoryDefinition /: MakeBoxes[declaration : TypeTheoryDefinition[name_, value_, options___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, definitionKeyword[Hold[options]], {{toSyntax[name], None, toSyntax[value]}}, form]

(* an opaque definition, an instance or a coercion is named so, as Lean's opaque, instance and @[coe] *)
definitionKeyword[heldOptions_Hold] := Replace[
	Select[{"Opaque", "Instance", "Coercion"}, Function[role, MemberQ[heldOptions, (Rule | RuleDelayed)[role, True]]]],
	{{} -> "definition", roles_ :> ToLowerCase[StringRiffle[roles, " "]]}
]

TypeTheoryTheorem /: MakeBoxes[declaration : TypeTheoryTheorem[name_, statement_, Except[_Rule | _RuleDelayed], ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, "theorem", {{toSyntax[name], toSyntax[statement]}}, form]

TypeTheoryRewriteRule /: MakeBoxes[declaration : TypeTheoryRewriteRule[name_, rule_, ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[declaration, "rewrite", {{toSyntax[name], rewriteSyntax[toSyntax[rule]]}}, form]

(* the two sides of a rewrite rule show as lhs ⟶ rhs, an arrow apart from that of function types *)
rewriteSyntax[syntaxApplication[forAll : syntaxSymbol[HoldComplete[ForAll]], {binders_, body_}]] := syntaxApplication[forAll, {binders, rewriteSyntax[body]}]
rewriteSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {left_, right_}]] := syntaxHead[LongRightArrow, {left, right}]
rewriteSyntax[syntax_] := syntax

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

(* mutually inductive types: each type on a line of its own, then the constructors of all of them *)
TypeTheoryInductiveType /: MakeBoxes[declaration : TypeTheoryInductiveType[types : {(_Rule | _RuleDelayed) ..}, constructors_List, ___], form : StandardForm | TraditionalForm] :=
	declarationBoxes[
		declaration,
		"inductive",
		Cases[Unevaluated[types], (Rule | RuleDelayed)[name_, type_] :> {toSyntax[name], toSyntax[type]}],
		Cases[Unevaluated[constructors], (Rule | RuleDelayed)[constructor_, constructorType_] :> {toSyntax[constructor], toSyntax[constructorType]}],
		form
	]

(* the keyword, then name : type (:= value), with each constructor of an inductive type on a line of its own *)
declarationBoxes[declaration_, keyword_String, {first_, constructors___}, form_] := declarationBoxes[declaration, keyword, {first}, {constructors}, form]

declarationBoxes[declaration_, keyword_String, headings_List, constructors_List, form_] := With[
	{
		rows = Join[
			Function[heading, Join[{StyleBox[keyword, FontWeight -> Bold, FontColor -> StandardBlue]}, declarationRow[heading, form]]] /@ headings,
			Function[constructor, Join[{"|"}, declarationRow[constructor, form]]] /@ constructors
		]
	},
	InterpretationBox[GridBox[rows, GridBoxAlignment -> {"Columns" -> {{Left}}}, GridBoxSpacings -> {"Columns" -> {{0.6}}}], declaration]
]

declarationRow[{name_, type_}, form_] := {nameBoxes[name, form], ":", typeTheoryBoxes[type, form]}
declarationRow[{name_, None, value_}, form_] := {nameBoxes[name, form], ":=", typeTheoryBoxes[value, form]}
declarationRow[{name_, type_, value_}, form_] := {nameBoxes[name, form], ":", RowBox[{typeTheoryBoxes[type, form], " := ", typeTheoryBoxes[value, form]}]}

(* a declared name shows as itself: the constructor NaturalNumberZero is not shown as 0 where it is declared *)
nameBoxes[name_, form_] := Block[{$displayedNaturalNumbers = <||>}, typeTheoryBoxes[name, form]]
