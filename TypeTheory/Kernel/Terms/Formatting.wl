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
	A -> B -> C, TypeSpecifier[{A, B} -> C]  A → B → C       RightArrow
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
	"rationalOfPair"["pair"[a, b]]        a / (b + 1), and a where b is 0, for a literal b
	zero, successor[n]                  0, n + 1             the natural numbers of the term's environment, as Lean shows them
	NaturalNumberPredecessor[n]         n - 1
	IntervalZero, IntervalOne           0, 1                 the endpoints of the interval of cubical type theory
	IntervalMeet, IntervalJoin, IntervalReverse   r ∧ s, r ∨ s, ~r
	Path[Function[{i}, A], a, b]        a ≡ b                Congruent, where the line is constant
	CartesianProductType[A, B]          A × B                Cross, which takes ×; A × B × C for A × (B × C)
	DisjointUnionType[A, B]             A | B                Alternatives, as the pattern _A | _B; A | B | C for A | (B | C)
	"pair"[a, "pair"[b, c]]                 (a, b, c)
	DependentSum[A, Function[{b}, B]]   Σ_b B                NotExists, which takes Σ, one binder
	"dependentPair"[a, b]                 〈a, b〉              LeftAngleBracket, as AngleBracket shows
	Prepend[1][Prepend[2][{}]]          {1, 2}               in braces: [1, 2] in f[[1, 2]] would read as Part
	Prepend[x][l]                       Prepend • x • l      by Application, where l is no literal
	"sequencePrepend"[1, "emptySequence"]   [1]                  "emptySequence" as [], a sequence in brackets
	Sequence[A, B]                      [A, B]               the type, as the sequences show; Sequence @@ As for a list
	                                                         As of types that is no literal
	List[A]                             {A}                  the type, as the Wolfram Language shows List[A]
	Subtype[Function[{x}, p]]           {x ∶ A // p}         one binder, as Lean writes { x // p }

A constant named by a symbol outside System, a type or a function alike, as Option or a declared degree,
shows in bold, so that it is told apart from a constant named by a string, which shows as the
string does, and from a variable. A constant named by a string is never bold, nor is a notation, as ℕ, nor a System
symbol, as True, And, List or Sequence, which shows as the Wolfram Language shows it.

A variable the term binds, and a hypothesis of a goal in its target, shows in the green of a local variable; a universe
level, as the u of Type u, in gray; an unsolved metavariable, as ?u3, in the orange of a hole ($displayColors).
The display rewrites the syntax tree of the term with these operators, rebuilds it held, and takes its
boxes with MakeBoxes; InterpretationBox keeps the term itself behind the display. The bound variables of
the prelude and of generated recursors are symbols of the paclet's private contexts, shown by their names.

A TypeTheoryProofTree shows drawn, as natural deduction is written: each conclusion under a line over its premises, the
rule named at the line's right, →I, →E, ∧I, ∧E, ∨I, ∨E or ⊥E, and an assumption bare.
A TypeTheoryProof shows its open goals as a list of hypotheses over the goal, as in a proof assistant's
goal view. A declaration shows as its keyword, its name and its type, as in a proof assistant's source;
a rewrite rule shows its two sides as lhs ⟶ rhs, apart from the arrow of function types.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[typeTheoryBoxes]
PackageScoped[expressionOfSyntax]
PackageScoped[sequencePieces]
PackageScoped[prependedElements]
PackageScoped[associationPairsQ]
PackageScoped[ruleSyntaxQ]
PackageScoped[constructedPieces]
PackageScoped[stringOfSyntax]
PackageScoped[rememberDisplayEnvironment]
PackageScoped[displaySyntax]
PackageScoped[$displayColors]
PackageScoped[$displayTooltips]


(* ::Section:: *)
(*Usage Messages*)


typeTheoryBoxes::usage = "typeTheoryBoxes[syntax, form] gives boxes showing the syntax tree of a term in mathematical notation."
displaySyntax::usage = "displaySyntax[syntax] rewrites the syntax tree of a term with the built-in operators that show it in mathematical notation."
$displayTooltips::usage = "$displayTooltips is True where a display shows the types of constants and bound variables on mouseover, False where it does not, and Automatic, the default, where a front end draws the display or TYPETHEORY_NOTEBOOK_BOXES is \"True\"."
prependedElements::usage = "prependedElements[syntax] gives the elements of the list literal syntax, {} where it is none."
ruleSyntaxQ::usage = "ruleSyntaxQ[syntax] gives True if syntax is a rule, lhs -> rhs or lhs :> rhs."
associationPairsQ::usage = "associationPairsQ[syntax] gives True if syntax is a list literal of pairs, the pairs of an association written out."
$displayColors::usage = "$displayColors is the Association of the colors a display gives a bound variable, a universe level and an unsolved metavariable."


(* ::Section:: *)
(*Function Definitions*)


(* Naturals, written for the natural numbers, shows as they do, unless the term binds a variable of that name *)
typeTheoryBoxes[syntax_, form_] := displayed[syntax, form,
	quantifiedOperandBoxes @ typeOperatorBoxes @ logicalOperatorBoxes @ Replace[heldFromSyntax[displaySyntax[syntax]], HoldComplete[display_] :> MakeBoxes[display, form]]
]

(* the state a display of the syntax of a term reads while it is built, in a notebook and in text alike *)
SetAttributes[displayed, HoldRest]
displayed[syntax_, form_, body_] := Block[
	{
		$displayedNaturalNumbers = displayedNaturalNumbers[],
		$naturalsBound = ! FreeQ[syntax, syntaxApplication[syntaxSymbol[HoldComplete[Typed | TypedImplicit]], {syntaxSymbol[HoldComplete[Naturals]], __}]],
		$boundSymbols = Join[$goalSymbols, boundSymbols[syntax]],
		$boundTypes = Join[$goalTypes, boundTypes[syntax]],
		$symbolConstants = <||>,
		$constantTypes = <||>,
		$tooltipsShown = tooltipsWanted[] && form =!= OutputForm && LeafCount[syntax] <= $tooltipLeafLimit,
		$displayForm = form,
		$notationHeads = notationHeads[]
	},
	body
]

(* in text, as a front end that shows OutputForm prints it, a term shows as it shows in a notebook; a Format rule with a
   condition never applies, so the test is inside *)
TypeTheoryTerm /: Format[term : TypeTheoryTerm[expression_, environment___], OutputForm] := If[ MatchQ[{environment}, {} | {_?environmentQ} | {_String}],
	withDisplayEnvironment[termEnvironment[term], textDisplay[toSyntax[expression]]],
	OutputForm[ToString[Unevaluated[term], InputForm]]
]

textDisplay[syntax_] := displayed[syntax, OutputForm, shownForm[heldFromSyntax[displaySyntax[syntax]]]]
shownForm[HoldComplete[shown_]] := HoldForm[shown]

TypeTheoryTerm /: MakeBoxes[term : TypeTheoryTerm[expression_, environment___], form : StandardForm | TraditionalForm] /; MatchQ[{environment}, {} | {_?environmentQ} | {_String}] := With[
	{boxes = withDisplayEnvironment[termEnvironment[term], typeTheoryBoxes[toSyntax[expression], form]]},
	InterpretationBox[boxes, term] /; notebookBoxesQ[]
]
(* with no front end to draw them, as in a terminal, which prints a failure's message from the boxes of its terms, the
   boxes are those a terminal prints as text: rows of their pieces, without styles, tooltips or tags *)
TypeTheoryTerm /: MakeBoxes[term : TypeTheoryTerm[expression_, environment___], form : StandardForm | TraditionalForm] /; MatchQ[{environment}, {} | {_?environmentQ} | {_String}] := With[
	{boxes = textBoxes[withDisplayEnvironment[termEnvironment[term], typeTheoryBoxes[toSyntax[expression], form]]]},
	InterpretationBox[boxes, term]
]

textBoxes[boxes_] := boxes //. {
	TemplateBox[{separator_, _, items___}, "RowWithSeparators", ___] :> RowBox[Riffle[{items}, separator]],
	TemplateBox[{items___}, "RowDefault", ___] :> RowBox[{items}],
	SubscriptBox[quantifier : "\[ForAll]" | "\[Exists]", binder_, ___] :> RowBox[{quantifier, binder, " "}],
	(TooltipBox | StyleBox | TagBox | InterpretationBox)[shown_, ___] :> shown
}

(* the natural numbers a display shows as 0 and n + 1: those of the environment shown, and outside one, as
   in a declaration, the default environment's *)
$displayedNaturalNumbers = Automatic

SetAttributes[withDisplayEnvironment, HoldRest]
withDisplayEnvironment[environment_, expression_] := Block[
	{$displayedNaturalNumbers = settingsOrNone[environment], $displayedOverloads = overloadsOrNone[environment], $displayEnvironment = environment},
	expression
]

(* the environment whose constants a display looks up: the term's, and outside one the default environment *)
$displayEnvironment = Automatic

displayEnvironment[] := Replace[$displayEnvironment, Automatic :> defaultEnvironment[]]

(* the constants declared with "Overloads" -> operation, which show as the operation does: <|HoldComplete[constant] -> operation|> *)
$displayedOverloads = <||>

overloadsOrNone[environment_] := Replace[
	Quiet @ Association @ Catenate @ Map[
		Function[operation, Function[constant, constant -> First[operation]] /@ overloadingConstants[environment, operation]],
		HoldComplete /@ Unevaluated[{Plus, Times, Subtract, Power, Minus, LessEqual, Less, GreaterEqual, Greater}]
	],
	Except[_Association] -> <||>
]

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

(* A product of types and a dependent sum show as Cross and NotExists, which bind as × and a quantifier do,
   and then take the symbols × and Σ. CircleTimes is left to the types named by it, which show as ⊗. *)
typeOperatorBoxes[boxes_] := Replace[
	boxes,
	{
		RowBox[operands : {_, "\[Cross]", __}] :> RowBox[Replace[operands, "\[Cross]" -> "\[Times]", {1}]],
		SubscriptBox["\[NotExists]", binder_] :> SubscriptBox["\[CapitalSigma]", binder]
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

(* the symbols the binders of a term name: of ForAll, Function, Exists and the hypotheses of a goal *)
$boundSymbols = <||>

(* the names of the hypotheses of the goal on display, local to its target as a bound variable is, and their types *)
$goalSymbols = <||>
$goalTypes = <||>

(* the type each binder gives the symbol it names, where the term binds it at one type only *)
$boundTypes = <||>

boundTypes[syntax_] := Association[Cases[
	Normal[GroupBy[
		Catenate @ Cases[
			syntax,
			syntaxApplication[syntaxSymbol[HoldComplete[ForAll | Function | Exists | RightTee]], {binders_, __}] :> Catenate[binderTyping /@ listElements[binders]],
			{0, Infinity}
		],
		First -> Last,
		DeleteDuplicates
	]],
	(name_ -> {type_}) :> name -> type
]]

binderTyping[syntaxApplication[syntaxSymbol[HoldComplete[Typed | TypedImplicit]], {syntaxSymbol[name : HoldComplete[_Symbol]], type_, ___}]] := {name -> type}
binderTyping[syntaxApplication[syntaxSymbol[HoldComplete[Annotation]], {binder_, _}]] := binderTyping[binder]
binderTyping[_] := {}

boundSymbols[syntax_] := AssociationMap[True&, DeleteDuplicates @ Catenate @ Cases[
	syntax,
	syntaxApplication[syntaxSymbol[HoldComplete[ForAll | Function | Exists | RightTee]], {binders_, __}] :> Catenate[binderSymbol /@ listElements[binders]],
	{0, Infinity}
]]

binderSymbol[syntaxSymbol[name : HoldComplete[_Symbol]]] := {name}
binderSymbol[syntaxApplication[syntaxSymbol[HoldComplete[Typed | TypedImplicit]], {syntaxSymbol[name : HoldComplete[_Symbol]], ___}]] := {name}
binderSymbol[syntaxApplication[syntaxSymbol[HoldComplete[Annotation]], {binder_, _}]] := binderSymbol[binder]
binderSymbol[_] := {}

SetAttributes[offPathQ, HoldAllComplete]
offPathQ[symbol_Symbol] := With[{context = Context[Unevaluated[symbol]]}, context =!= $Context && ! MemberQ[$ContextPath, context]]

SetAttributes[privateNameQ, HoldAllComplete]
privateNameQ[symbol_Symbol] := With[{context = Context[Unevaluated[symbol]]},
	StringStartsQ[context, "WolframInstitute`TypeTheory`"] && context =!= "WolframInstitute`TypeTheory`"
]


(* ::Subsection:: *)
(*Notation*)


(* the arguments are rewritten first, so each rule sees displayed arguments *)
displaySyntax[syntaxApplication[head_, arguments_List]] := displayApplication[head, displaySyntax /@ arguments]
(* products, sums, pairs and lists nested to the right show as one row, as Lean shows them *)
displaySyntax[syntax : syntaxApplication[syntaxSymbol[HoldComplete[CartesianProductType]], {_, _}]] :=
	syntaxHead[Cross, displaySyntax /@ rightNested[CartesianProductType, syntax]]
displaySyntax[syntax : syntaxApplication[syntaxSymbol[HoldComplete[DisjointUnionType]], {_, _}]] :=
	syntaxHead[Alternatives, displaySyntax /@ rightNested[DisjointUnionType, syntax]]
displaySyntax[syntax : syntaxApplication[syntaxString["pair"], {_, _}]] := tupleDisplay["(", displaySyntax /@ rightNested["pair", syntax], ")"]
displaySyntax[syntax : syntaxApplication[syntaxString["dependentPair"], {_, _}]] :=
	tupleDisplay["\[LeftAngleBracket]", displaySyntax /@ rightNested["dependentPair", syntax], "\[RightAngleBracket]"]
(* the constructor of lists applied as it reads back, "Prepend"[x, l], as written in operator form, Prepend[x][l], and
   in the Wolfram Language's two-argument form, Prepend[l, x] *)
$prependSyntaxPatterns = {
	syntaxApplication[syntaxString["Prepend"], {_, _}],
	syntaxApplication[syntaxApplication[syntaxSymbol[HoldComplete[Prepend]], {_}], {_}],
	syntaxApplication[syntaxSymbol[HoldComplete[Prepend]], {_, _}]
}

(* one rule for each, put in with With, as the left side of := is not evaluated, and none of alternatives, which would
   rank below the rule for any application *)
Scan[
	Function[pattern, With[{each = pattern}, displaySyntax[syntax : each] /; listLiteralQ[syntax] := tupleDisplay["{", displaySyntax /@ prependedElements[syntax], "}"]]],
	$prependSyntaxPatterns
]
(* the constructor of lists, where its list is no literal, shows as its operator form applied, Prepend \[Application] x
   \[Application] l, each Application of two, as only that shows infix; it reads back as Prepend[x][l] *)
displaySyntax[syntax : syntaxApplication[syntaxString["Prepend"], arguments_List]] /; ! listLiteralQ[syntax] :=
	Fold[Function[{applied, argument}, syntaxHead[Application, {applied, argument}]], syntaxSymbol[HoldComplete[Prepend]], displaySyntax /@ arguments]
displaySyntax[syntaxString["Prepend"]] := syntaxSymbol[HoldComplete[Prepend]]
displaySyntax[syntax : syntaxApplication[syntaxString["sequencePrepend"], {_, _}]] /; sequenceLiteralQ[syntax] :=
	tupleDisplay["[", displaySyntax /@ Most[rightNested["sequencePrepend", syntax]], "]"]
displaySyntax[syntaxString["emptySequence"]] := syntaxString["[]"]
(* a sequence of any number of elements shows in brackets, as every sequence does, [a, b, ...], however it is written,
   Unevaluated[a, b, ...]: a sequence among its elements spliced in, one that is no literal by itself, and the sequence
   of the elements of a list as Sequence @@ l; its type shows as A... *)
displaySyntax[syntaxString["emptySequenceOf"]] := sequenceDisplay[{}]
displaySyntax[syntax : syntaxApplication[syntaxString["sequenceOfPrepend"], {_, _}]] := sequenceDisplay[sequencePieces[syntax]]
displaySyntax[syntax : syntaxApplication[syntaxString["sequenceOfJoin"], {_, _}]] := sequenceDisplay[sequencePieces[syntax]]
displaySyntax[syntax : syntaxApplication[syntaxString["sequenceOfList"], {_}]] := sequenceDisplay[{syntax}]
displaySyntax[syntaxApplication[syntaxSymbol[HoldComplete[Unevaluated]], elements_List]] := sequenceDisplay[elements]
displaySyntax[syntax : syntaxApplication[syntaxSymbol[HoldComplete[Apply]], {syntaxSymbol[HoldComplete[Unevaluated]], _}]] := sequenceDisplay[{syntax}]

sequenceDisplay[pieces_List] := tupleDisplay["[", pieceDisplay /@ Catenate[splicedPieces /@ pieces], "]"]
(* the list of the elements of a sequence, {s}, as the Wolfram Language splices a sequence into a list *)
displaySyntax[syntaxApplication[syntaxString["listOfSequence"], {sequence_}]] := syntaxHead[List, pieceDisplay /@ splicedPieces[sequence]]

splicedPieces[syntaxApplication[syntaxSymbol[HoldComplete[Unevaluated]], elements_List]] := Catenate[splicedPieces /@ elements]
splicedPieces[syntax : syntaxString["emptySequenceOf"]] := sequencePieces[syntax]
splicedPieces[syntax : syntaxApplication[syntaxString["sequenceOfPrepend"], {_, _}]] := Catenate[splicedPieces /@ sequencePieces[syntax]]
splicedPieces[syntax : syntaxApplication[syntaxString["sequenceOfJoin"], {_, _}]] := Catenate[splicedPieces /@ sequencePieces[syntax]]
splicedPieces[piece_] := {piece}

pieceDisplay[syntaxApplication[syntaxString["sequenceOfList"], {list_}]] := syntaxHead[Apply, {syntaxSymbol[HoldComplete[Sequence]], displaySyntax[list]}]
pieceDisplay[syntaxApplication[syntaxSymbol[HoldComplete[Apply]], {syntaxSymbol[HoldComplete[Unevaluated]], list_}]] := syntaxHead[Apply, {syntaxSymbol[HoldComplete[Sequence]], displaySyntax[list]}]
pieceDisplay[piece_] := displaySyntax[piece]
(* A... in one piece, so that an arrow, which binds tighter than ..., does not put it in parentheses, A → (B...) → C *)
displaySyntax[syntaxApplication[syntaxString["sequenceOf"], {element_}]] := displaySyntax[syntaxHead[RepeatedNull, {element}]]
displaySyntax[syntaxApplication[syntaxSymbol[HoldComplete[RepeatedNull]], {element_}]] := delimited["", displaySyntax[element], "..."]
(* an expression of the Wolfram Language shows as the Wolfram Language shows it: its atoms as symbols, numbers and
   strings in quotes, its arguments in order, a sequence of them that is no literal spliced in; where a part is none of
   these, it shows as Construct[h, a, ...], the head and the arguments it is built from. The display holds the term, so
   what it shows copies as the term. *)
displaySyntax[syntax : syntaxApplication[syntaxString["Construct"], {_, _}]] /; quotableQ[syntax] := displaySyntax[unquoted[syntax]]
displaySyntax[syntaxApplication[syntaxString["Construct"], {head_, sequence_}]] := syntaxHead[Construct, Prepend[pieceDisplay /@ constructedPieces[sequence], displaySyntax[head]]]
displaySyntax[syntaxString["Construct"]] := syntaxSymbol[HoldComplete[Construct]]
(* the constructor of failures shows as the Wolfram Language writes a failure, Failure[tag, details] *)
displaySyntax[syntaxApplication[syntaxString["failure"], arguments_List]] := syntaxApplication[syntaxSymbol[HoldComplete[Failure]], displaySyntax /@ arguments]
(* a value that is not there shows as Missing[reason, details...], and an association as <|k -> v, ...|>: of a list of
   pairs written out, and as it is put together, key after key *)
displaySyntax[syntaxApplication[syntaxString["missing"], {reason_, details_}]] := syntaxHead[Missing, Prepend[pieceDisplay /@ sequencePieces[details], displaySyntax[reason]]]
displaySyntax[syntax : syntaxApplication[syntaxString["association" | "associationInsert"], _]] /; associationRules[syntax] =!= None :=
	associationDisplay[associationRules[syntax]]
associationPairsQ[pairs_] := listLiteralQ[pairs] && AllTrue[prependedElements[pairs], MatchQ[syntaxApplication[syntaxString["pair"], {_, _}]]]
(* the rules k -> v an association shows, of its pairs written out, then of each key put in; None where it has no such
   form, as an association held in a variable *)
associationRules[syntaxApplication[syntaxString["association"], {pairs_}]] /; associationPairsQ[pairs] :=
	Function[pair, syntaxHead[Rule, displaySyntax /@ Last[pair]]] /@ prependedElements[pairs]
associationRules[syntaxApplication[syntaxString["associationInsert"], {association_, key_, value_}]] :=
	Replace[associationRules[association], rules_List :> Append[rules, syntaxHead[Rule, {displaySyntax[key], displaySyntax[value]}]]]
associationRules[syntaxApplication[syntaxSymbol[HoldComplete[Association]], rules_List]] /; AllTrue[rules, ruleSyntaxQ] := displaySyntax /@ rules
associationRules[_] := None
displaySyntax[syntax : syntaxApplication[syntaxSymbol[HoldComplete[Association]], _List]] /; associationRules[syntax] =!= None :=
	associationDisplay[associationRules[syntax]]
associationDisplay[{}] := syntaxString["\[LeftAssociation]\[RightAssociation]"]
associationDisplay[rules_List] := tupleDisplay["\[LeftAssociation]", rules, "\[RightAssociation]"]
ruleSyntaxQ[syntax_] := MatchQ[syntax, syntaxApplication[syntaxSymbol[HoldComplete[Rule | RuleDelayed]], {_, _}]]
(* a natural number or a string where an expression is expected shows as itself, as it is an expression in the Wolfram
   Language *)
displaySyntax[syntaxApplication[syntaxString["NaturalExpressionCoercion"], {value_}]] := displaySyntax[value]
displaySyntax[syntaxApplication[syntaxString["StringExpressionCoercion"], {value_}]] := displaySyntax[value]
displaySyntax[syntax : syntaxApplication[syntaxString["atom"], {_}]] /; quotableQ[syntax] := displaySyntax[unquoted[syntax]]
(* a quotation shows as the expression it quotes, as the Wolfram Language shows HoldForm[e]; a string in it is a string,
   no name of a constant *)
displaySyntax[syntaxApplication[syntaxSymbol[HoldComplete[HoldForm]], {quoted_}]] := displaySyntax[quoted /. syntaxString[text_String] :> syntaxOther[HoldComplete[text]]]
(* a string in an expression shows in quotes, apart from the names of constants *)
displaySyntax[syntaxOther[HoldComplete[text_String]]] := syntaxString[ToString[text, InputForm]]

(* the syntax of the expression of the Wolfram Language an expression's syntax stands for, or None; the text of a string *)
expressionOfSyntax[syntax_] := If[quotableQ[syntax], unquoted[syntax], None]
stringOfSyntax[syntax_] := Replace[stringText[syntax], Except[_String] -> None]

quotableQ[syntaxApplication[syntaxString["atom"], {atom_}]] := atomSyntax[atom] =!= None
quotableQ[syntaxApplication[syntaxString["Construct"], {head_, sequence_}]] := quotableQ[head] && AllTrue[sequencePieces[sequence], quotablePieceQ]
quotableQ[syntaxApplication[syntaxString["NaturalExpressionCoercion"], {_syntaxInteger}]] := True
quotableQ[syntaxSymbol[_]] := True
quotableQ[_] := False

(* an argument, or a sequence of them: a variable, or the sequence of the elements of a list variable, Sequence @@ l *)
quotablePieceQ[syntaxApplication[syntaxString["sequenceOfList"], {syntaxSymbol[_]}]] := True
quotablePieceQ[piece_] := quotableQ[piece]

(* the elements of a sequence, in order, and each sequence joined in that is no literal: a variable, or the sequence of
   the elements of a list; the arguments of Construct, the empty sequence where there are none *)
sequencePieces[syntaxString["emptySequenceOf"]] := {}
sequencePieces[syntaxApplication[syntaxString["sequenceOfPrepend"], {element_, rest_}]] := Prepend[sequencePieces[rest], element]
sequencePieces[syntaxApplication[syntaxString["sequenceOfJoin"], {first_, rest_}]] := Join[sequencePieces[first], sequencePieces[rest]]
sequencePieces[other_] := {other}

constructedPieces[sequence_] := Replace[sequencePieces[sequence], {} -> {syntaxString["emptySequenceOf"]}]

(* the atom an atom's syntax names, or None: a symbol by its full name, a natural number, a negative integer, a string,
   or another atom by its InputForm *)
atomSyntax[syntaxApplication[syntaxString["naturalAtom"], {n : syntaxInteger[_]}]] := n
atomSyntax[syntaxApplication[syntaxString["negativeAtom"], {syntaxInteger[n_Integer]}]] := syntaxInteger[-n - 1]
atomSyntax[syntaxApplication[syntaxString["symbolAtom"], {name_}]] := Replace[stringText[name], {
	text_String :> Replace[Quiet[ToExpression[text, InputForm, HoldComplete]], {HoldComplete[symbol_Symbol] :> syntaxSymbol[HoldComplete[symbol]], _ -> None}],
	None -> None
}]
atomSyntax[syntaxApplication[syntaxString["stringAtom"], {text_}]] := Replace[stringText[text], {string_String :> syntaxOther[HoldComplete[string]], None -> None}]
atomSyntax[syntaxApplication[syntaxString["otherAtom"], {_, form_}]] := Replace[stringText[form], {
	text_String :> Replace[Quiet[ToExpression[text, InputForm, HoldComplete]], {HoldComplete[other_] :> syntaxOther[HoldComplete[other]], _ -> None}],
	None -> None
}]
atomSyntax[syntaxApplication[syntaxString["stringAtom"], {literal : syntaxString[_]}]] := atomSyntax[literal]
atomSyntax[syntaxString[name_String]] := Replace[Quiet[ToExpression[name, InputForm, HoldComplete]], {
	HoldComplete[symbol_Symbol] /; StringContainsQ[name, "`"] :> syntaxSymbol[HoldComplete[symbol]],
	HoldComplete[n_Integer] :> syntaxInteger[n],
	HoldComplete[text_String] :> syntaxString[text],
	HoldComplete[other_ /; AtomQ[Unevaluated[other]]] :> syntaxOther[HoldComplete[other]],
	_ -> None
}]
atomSyntax[_] := None

(* the text of a string, the list of its character codes, or None *)
stringText[syntaxApplication[syntaxString["string"], {codes_}]] := Replace[codes, {
	_?listLiteralQ :> Replace[prependedElements[codes], {elements : {syntaxInteger[_] ...} :> FromCharacterCode[elements[[All, 1]], "Unicode"], _ -> None}],
	syntaxApplication[syntaxSymbol[HoldComplete[Typed]], {syntaxApplication[syntaxSymbol[HoldComplete[List]], {}], _}] :> "",
	_ -> None
}]
stringText[_] := None

(* a string shows as its text, quoted *)
displaySyntax[syntax : syntaxApplication[syntaxString["string"], {_}]] /; StringQ[stringText[syntax]] := syntaxString[ToString[stringText[syntax], InputForm]]

unquoted[syntaxApplication[syntaxString["atom"], {atom_}]] := atomSyntax[atom]
unquoted[syntaxApplication[syntaxString["Construct"], {head_, sequence_}]] := syntaxApplication[unquoted[head], unquotedPiece /@ sequencePieces[sequence]]
unquoted[syntaxApplication[syntaxString["NaturalExpressionCoercion"], {n_syntaxInteger}]] := n
unquoted[variable_] := variable

unquotedPiece[syntaxApplication[syntaxString["sequenceOfList"], {list_}]] := syntaxHead[Apply, {syntaxSymbol[HoldComplete[Sequence]], list}]
unquotedPiece[piece_] := unquoted[piece]

(* a sequence and its type alike in brackets, [a, b] and [A, B], as a sequence shows *)
displaySyntax[syntaxApplication[syntaxSymbol[HoldComplete[Sequence]], elements_List]] := tupleDisplay["[", displaySyntax /@ elements, "]"]
displaySyntax[syntaxSymbol[HoldComplete[NonNegativeIntegers]]] := syntaxString["\[DoubleStruckCapitalN]"]
displaySyntax[syntaxSymbol[HoldComplete[Naturals]]] /; ! TrueQ[$naturalsBound] := syntaxString["\[DoubleStruckCapitalN]"]
displaySyntax[syntaxSymbol[HoldComplete[Integers]]] := syntaxString["\[DoubleStruckCapitalZ]"]
displaySyntax[syntaxSymbol[HoldComplete[Rationals]]] := syntaxString["\[DoubleStruckCapitalQ]"]
displaySyntax[syntaxSymbol[HoldComplete[Booleans]]] := syntaxString["\[DoubleStruckCapitalB]"]
displaySyntax[syntaxSymbol[HoldComplete[Circle]]] := syntaxString["\[DoubleStruckCapitalS]\:00b9"]
displaySyntax[syntaxSymbol[HoldComplete[IntervalZero]]] := syntaxInteger[0]
displaySyntax[syntaxSymbol[HoldComplete[IntervalOne]]] := syntaxInteger[1]
displaySyntax[name : syntaxSymbol[_] | syntaxString[_]] /; naturalNumberConstantQ[name, "Zero"] := syntaxInteger[0]
(* a variable the term binds shows in the color of a local variable, by its name, as Lean prints one, also when it was
   read in a context the context path leaves out, or in the paclet's own, where the symbol would show its context *)
displaySyntax[syntaxSymbol[name : HoldComplete[symbol_Symbol]]] /; KeyExistsQ[$boundSymbols, name] := typeTooltip[
	styled[If[offPathQ[symbol] || privateNameQ[symbol], syntaxString[SymbolName[Unevaluated[symbol]]], syntaxSymbol[name]], "BoundVariable"],
	Lookup[$boundTypes, name, None]
]
displaySyntax[syntaxSymbol[HoldComplete[symbol_Symbol]]] /; privateNameQ[symbol] := syntaxString[SymbolName[Unevaluated[symbol]]]
displaySyntax[name : syntaxSymbol[held : HoldComplete[_Symbol]]] /; symbolConstantQ[name] := typeTooltip[bold[name], constantTypeSyntax[held]]
(* a constant named by a string shows as the string does, with its type on mouseover *)
displaySyntax[name : syntaxString[text_String]] /; TrueQ[$tooltipsShown] && displayedConstantQ[HoldComplete[text]] := typeTooltip[name, constantTypeSyntax[HoldComplete[text]]]
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
(* TypeSpecifier[{A, B} -> C] reads A → B → C; its rule is read before the arguments are shown, as the arrow of a rule
   shows on its own *)
displaySyntax[syntaxApplication[syntaxSymbol[HoldComplete[TypeSpecifier]], {syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {domains_, codomain_}]}]] :=
	arrowChain[RightArrow, displaySyntax /@ listElements[domains], displaySyntax[codomain]]
(* A -> B, as a function type reads back *)
displayApplication[syntaxSymbol[HoldComplete[Rule]], {domain_, codomain_}] := arrowChain[RightArrow, {domain}, codomain]
displayApplication[syntaxSymbol[HoldComplete[RightTee]], {syntaxApplication[syntaxSymbol[HoldComplete[List]], {}], goal_}] :=
	syntaxHead[Row, {syntaxHead[List, {syntaxString["\[RightTee] "], goal}]}]
displayApplication[syntaxSymbol[HoldComplete[RightTee]], {hypotheses_, goal_}] :=
	syntaxHead[RightTee, {syntaxHead[Row, {syntaxHead[List, listElements[hypotheses]], syntaxString[", "]}], goal}]
displayApplication[syntaxSymbol[HoldComplete[TypeUniverse]], {level_}] := universeDisplay[level]
(* a metavariable left unsolved shows as its name, in the color of what is still to do *)
displayApplication[syntaxSymbol[HoldComplete[Placeholder]], {syntaxString[name_String]}] /; StringStartsQ[name, "?"] := styled[syntaxString[name], "Unsolved"]
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
(* A factor that is itself a fraction is parenthesized in a product of rationals, (x/2) 1 and (1/2) 2 3. A literal n/d
   is the product n d^-1, which shows as the fraction n/d, as Power[d, -1] does; as a factor of a larger product the
   Wolfram Language would merge it with the other factors into one fraction, x/2 and 2 3/2, losing the factor 1
   and the grouping. A lone inverse may merge: x d^-1 is x/d. *)
displayApplication[syntaxString["rationalMultiplication"], {numerator_, syntaxApplication[syntaxSymbol[HoldComplete[Power]], {syntaxInteger[denominator_Integer], syntaxInteger[-1]}]}] /;
	integerSyntaxQ[numerator] := syntaxOther[HoldComplete @@ {literalFraction[integerOfSyntax[numerator], denominator]}]
displayApplication[syntaxString["rationalMultiplication"], arguments_List] := displayApplication[
	syntaxString["integerMultiplication"],
	afterNumbersParenthesized[Replace[literalFractionSyntax /@ arguments, fraction_ ? fractionSyntaxQ :> delimited["(", fraction, ")"], {1}]]
]

(* a literal fraction right after a number is parenthesized, 5 (2/3), which would read as the mixed number 5 2/3 *)
afterNumbersParenthesized[factors_List] := MapThread[
	Function[{factor, previous}, If[ MatchQ[factor, syntaxOther[HoldComplete[_literalFraction]]] && (integerSyntaxQ[previous] || MatchQ[previous, syntaxOther[HoldComplete[_literalFraction]]]),
		delimited["(", factor, ")"],
		factor
	]],
	{factors, Prepend[Most[factors], None]}
]

(* A literal fraction, n d^-1 of integers, as a factor shows as the fraction n/d, which no product merges and which
   needs no parentheses, 1/2 (x + y), but after a number *)
literalFractionSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Times]], {numerator_, syntaxApplication[syntaxSymbol[HoldComplete[Power]], {syntaxInteger[denominator_Integer], syntaxInteger[-1]}]}]] /;
	integerSyntaxQ[numerator] := syntaxOther[HoldComplete @@ {literalFraction[integerOfSyntax[numerator], denominator]}]
literalFractionSyntax[syntax_] := syntax

integerSyntaxQ[syntax_] := IntegerQ[integerOfSyntax[syntax]]
integerOfSyntax[syntaxInteger[n_Integer]] := n
integerOfSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Row]], {syntaxApplication[syntaxSymbol[HoldComplete[List]], {syntaxString["-"], syntaxInteger[n_Integer]}]}]] := -n
integerOfSyntax[_] := None

literalFraction /: MakeBoxes[literalFraction[numerator_Integer, denominator_Integer], form_] := FractionBox[MakeBoxes[numerator, form], MakeBoxes[denominator, form]]

fractionSyntaxQ[syntaxApplication[syntaxSymbol[HoldComplete[Divide]], _]] := True
fractionSyntaxQ[syntaxApplication[syntaxSymbol[HoldComplete[Times]], factors_List]] := AnyTrue[factors, inverseSyntaxQ]
fractionSyntaxQ[_] := False

inverseSyntaxQ[syntaxApplication[syntaxSymbol[HoldComplete[Power]], {_, syntaxInteger[_Integer ? Negative]}]] := True
inverseSyntaxQ[_] := False
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
(* A class of a pair with a literal denominator shows as the fraction it stands for, as computation gives it too.
   These rules read the pair before it is rewritten as a tuple, so they rewrite the syntax, not displayed arguments. *)
displaySyntax[syntaxApplication[
	syntaxSymbol[HoldComplete[QuotientIntroduction]],
	{syntaxString["rationalRelation"], pair : syntaxApplication[syntaxString["pair"], {_, syntaxInteger[_Integer]}]}
]] := displaySyntax[syntaxApplication[syntaxString["rationalOfPair"], {pair}]]
displaySyntax[syntaxApplication[syntaxString["rationalOfPair"], {syntaxApplication[syntaxString["pair"], {numerator_, syntaxInteger[0]}]}]] := displaySyntax[numerator]
(* a literal numerator makes the fraction the rational number itself, which a product takes without parentheses,
   1/2 (x + y); any other shows as a division *)
displaySyntax[syntaxApplication[syntaxString["rationalOfPair"], {syntaxApplication[syntaxString["pair"], {numerator_, syntaxInteger[denominator_Integer]}]}]] :=
	fractionDisplay[displaySyntax[numerator], denominator + 1]

fractionDisplay[numerator_, denominator_Integer] /; integerSyntaxQ[numerator] := syntaxOther[HoldComplete @@ {literalFraction[integerOfSyntax[numerator], denominator]}]
fractionDisplay[numerator_, denominator_Integer] := syntaxHead[Divide, {numerator, syntaxInteger[denominator]}]

(* -x and ↑x, with an argument that is no name or number in parentheses, so x + -y keeps its sign and
   ↑(m + n) its sum *)
prefixed[sign_String, argument_] /; atomicDisplayQ[argument] := syntaxHead[Row, {syntaxHead[List, {syntaxString[sign], argument}]}]
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
(* a constant declared with "Overloads" -> operation shows as the operation, as the integers' operations do *)
displayApplication[head : (syntaxSymbol[_HoldComplete] | syntaxString[_String]), arguments : {_, _}] /; overloadedDisplayQ[head, 2] :=
	displayApplication[syntaxSymbol[HoldComplete @@ {$displayedOverloads[displayedName[head]]}], arguments]
displayApplication[head : (syntaxSymbol[_HoldComplete] | syntaxString[_String]), {argument_}] /; overloadedDisplayQ[head, 1] := prefixed["-", argument]
(* a constant whose head has a notation of the user's, a rule of MakeBoxes or Format, is applied undecorated, so that
   the rule shows it *)
displayApplication[head_syntaxSymbol, arguments_List] /; userNotationQ[head] := syntaxApplication[head, arguments]
displayApplication[head_syntaxString, arguments_List] /; userNotationQ[head] := syntaxApplication[head, arguments]
displayApplication[head_, arguments_List] := With[{shownHead = displaySyntax[head]},
	If[decoratedQ[shownHead], syntaxHead[appliedDisplay, Prepend[arguments, shownHead]], syntaxApplication[shownHead, arguments]]
]

(* a head shown in bold or with its type on mouseover is applied as f[x], where the Wolfram Language would put a head
   that is not a symbol in parentheses, (f)[x] *)
decoratedQ[syntaxApplication[syntaxSymbol[HoldComplete[Style | typeTooltipped]], _]] := True
decoratedQ[_] := False

appliedDisplay /: MakeBoxes[appliedDisplay[head_, arguments___], form_] := RowBox[{
	MakeBoxes[head, form],
	"[",
	Replace[List @@ Map[Function[argument, MakeBoxes[argument, form], HoldAllComplete], Hold[arguments]], {{one_} :> one, several_ :> RowBox[Riffle[several, ","]]}],
	"]"
}]

(* in text, f[x] with its parts unevaluated *)
appliedDisplay /: Format[appliedDisplay[head_, arguments___], OutputForm] :=
	Row[{HoldForm[head], "[", Row[Map[HoldForm, Unevaluated[{arguments}]], ", "], "]"}]

(* the heads that rules of MakeBoxes are given for, MakeBoxes[head[...], form] := ..., which it keeps as its FormatValues *)
notationHeads[] := Cases[FormatValues[MakeBoxes], Verbatim[RuleDelayed][Verbatim[HoldPattern][Verbatim[MakeBoxes][(head : (_Symbol | _String))[___], ___]], _] :> HoldComplete[head]]

userNotationQ[syntaxSymbol[name : HoldComplete[symbol_Symbol]]] := MemberQ[$notationHeads, name] || FormatValues[symbol] =!= {}
userNotationQ[syntaxString[name_String]] := MemberQ[$notationHeads, HoldComplete[name]]
userNotationQ[_] := False

(* a projection of a name shown in color, in bold or with its type on mouseover is x〚1〛, where the Wolfram Language
   would put the styled name in parentheses *)
displaySyntax[syntaxApplication[syntaxSymbol[HoldComplete[Part]], {structure_, indices__}]] := With[{shown = displaySyntax[structure]},
	If[decoratedQ[shown], syntaxHead[partDisplay, Prepend[displaySyntax /@ {indices}, shown]], syntaxApplication[syntaxSymbol[HoldComplete[Part]], Prepend[displaySyntax /@ {indices}, shown]]]
]

partDisplay /: MakeBoxes[partDisplay[structure_, indices___], form_] := RowBox[{
	MakeBoxes[structure, form],
	"\[LeftDoubleBracket]",
	Replace[List @@ Map[Function[index, MakeBoxes[index, form], HoldAllComplete], Hold[indices]], {{one_} :> one, several_ :> RowBox[Riffle[several, ","]]}],
	"\[RightDoubleBracket]"
}]

displayedName[syntaxSymbol[name_HoldComplete]] := name
displayedName[syntaxString[name_String]] := HoldComplete[name]

overloadedDisplayQ[head_, 2] := MemberQ[{Plus, Times, Subtract, Power, LessEqual, Less, GreaterEqual, Greater}, Lookup[$displayedOverloads, Key[displayedName[head]], None]]
overloadedDisplayQ[head_, 1] := Lookup[$displayedOverloads, Key[displayedName[head]], None] === Minus

delimited[left_String, syntax_, right_String] := syntaxHead[Row, {syntaxHead[List, {syntaxString[left], syntax, syntaxString[right]}]}]

bold[syntax_] := syntaxHead[Style, {syntax, syntaxSymbol[HoldComplete[Bold]]}]

(* The colors of a display, each in one place: a bound variable as the front end shows a local variable, a universe level
   dimmed, as bookkeeping, and an unsolved metavariable as a hole shows. *)
$displayColors = <|"BoundVariable" -> RGBColor[0.2, 0.55, 0.2], "Level" -> StandardGray, "Unsolved" -> StandardOrange|>

(* Types on mouseover: a constant shows its declared type and a bound variable the type its binder gives, drawn as a
   term is but without tooltips of their own; a term past $tooltipLeafLimit leaves them out, to keep its boxes small.
   Automatic shows them where a front end draws the boxes, or where the environment variable TYPETHEORY_NOTEBOOK_BOXES
   is "True", as for notebooks built without one and for the tests of the boxes; a terminal prints a message's terms
   from their boxes, and a TooltipBox there as the box it is. *)
$displayTooltips = Automatic
$tooltipLeafLimit = 5000
tooltipsWanted[] := TrueQ[Replace[$displayTooltips, Automatic :> notebookBoxesQ[]]]
notebookBoxesQ[] := $FrontEnd =!= Null || Environment["TYPETHEORY_NOTEBOOK_BOXES"] === "True"
$tooltipsShown = False

(* a TooltipBox alone, where Tooltip would also keep the tooltip's boxes in a TagBox's annotation, twice its size *)
typeTooltipped /: MakeBoxes[typeTooltipped[shown_, RawBoxes[tip_]], form_] := TooltipBox[MakeBoxes[shown, form], tip]

typeTooltip[display_, None] := display
typeTooltip[display_, typeSyntax_] := If[ TrueQ[$tooltipsShown],
	syntaxHead[typeTooltipped, {display, syntaxOther[HoldComplete @@ {RawBoxes[Block[{$displayTooltips = False}, typeTheoryBoxes[typeSyntax, $displayForm]]]}]}],
	display
]

(* the declared type of a constant of the display's environment, read back once a display; None where it has none *)
constantTypeSyntax[held_HoldComplete] := Lookup[$constantTypes, Key[held], $constantTypes[held] = Replace[
	Quiet[catchKernelFailure[constantRecord[displayEnvironment[], held]]],
	{record : KeyValuePattern["Type" -> type_] :> Quiet[Check[delaborate[displayEnvironment[], <||>, type], None]], _ :> None}
]]

styled[syntax_, role_String] := With[{color = $displayColors[role]}, syntaxHead[Style, {syntax, syntaxOther[HoldComplete[color]]}]]

(* an argument written after its function, as in List A, in parentheses unless it is a name or a number *)
juxtaposed[syntax_] /; atomicDisplayQ[syntax] := syntax
juxtaposed[syntax_] := delimited["(", syntax, ")"]

(* a name, a number or a fraction, also in bold or in a color, which an operator before it takes without parentheses *)
atomicDisplayQ[syntaxSymbol[_] | syntaxString[_] | syntaxInteger[_]] := True
(* a literal fraction, its bar delimiting it *)
atomicDisplayQ[syntaxOther[HoldComplete[_literalFraction]]] := True
atomicDisplayQ[syntaxApplication[syntaxSymbol[HoldComplete[Style | typeTooltipped]], {syntax_, _}]] := atomicDisplayQ[syntax]
atomicDisplayQ[_] := False

(* A constant of the display's environment named by a symbol outside System, a type or a function alike, which a variable
   the term binds does not shadow; each name is looked up once a display. *)
symbolConstantQ[syntaxSymbol[held : HoldComplete[symbol_Symbol]]] := And[
	Context[Unevaluated[symbol]] =!= "System`",
	! KeyExistsQ[$boundSymbols, held],
	If[AssociationQ[$symbolConstants], Lookup[$symbolConstants, Key[held], $symbolConstants[held] = displayedConstantQ[held]], displayedConstantQ[held]]
]

displayedConstantQ[held_HoldComplete] := AssociationQ[Quiet[catchKernelFailure[constantRecord[displayEnvironment[], held]]]]

tupleDisplay[left_String, elements_List, right_String] := delimited[left, syntaxHead[Row, {syntaxHead[List, elements], syntaxString[", "]}], right]

(* the elements of head[a, head[b, c]]: a, b and c *)
rightNested[head_Symbol, syntaxApplication[syntaxSymbol[HoldComplete[head_]], {first_, rest_}]] := Prepend[rightNested[head, rest], first]
rightNested[_Symbol, last_] := {last}
rightNested[head_String, syntaxApplication[syntaxString[head_], {first_, rest_}]] := Prepend[rightNested[head, rest], first]
rightNested[_String, last_] := {last}

Scan[Function[pattern, With[{each = pattern}, listLiteralQ[syntax : each] := listLiteralQ[prependedRest[syntax]]]], $prependSyntaxPatterns]
listLiteralQ[syntaxString["{}"]] := True
listLiteralQ[syntaxApplication[syntaxSymbol[HoldComplete[List]], _]] := True
(* the elements give the type an ascribed empty list states *)
listLiteralQ[syntaxApplication[syntaxSymbol[HoldComplete[Typed]], {syntaxString["{}"] | syntaxApplication[syntaxSymbol[HoldComplete[List]], {}], _}]] := True
listLiteralQ[_] := False

prependedElement[syntaxApplication[syntaxString["Prepend"], {element_, _}]] := element
prependedElement[syntaxApplication[syntaxApplication[syntaxSymbol[HoldComplete[Prepend]], {element_}], {_}]] := element
prependedElement[syntaxApplication[syntaxSymbol[HoldComplete[Prepend]], {_, element_}]] := element

prependedRest[syntaxApplication[syntaxString["Prepend"], {_, rest_}]] := rest
prependedRest[syntaxApplication[syntaxApplication[syntaxSymbol[HoldComplete[Prepend]], {_}], {rest_}]] := rest
prependedRest[syntaxApplication[syntaxSymbol[HoldComplete[Prepend]], {rest_, _}]] := rest

(* the elements of a list literal, Prepend[x][rest] being x and then the elements of rest *)
Scan[Function[pattern, With[{each = pattern}, prependedElements[syntax : each] := Prepend[prependedElements[prependedRest[syntax]], prependedElement[syntax]]]], $prependSyntaxPatterns]
prependedElements[syntaxApplication[syntaxSymbol[HoldComplete[List]], elements_List]] := elements
prependedElements[_] := {}

sequenceLiteralQ[syntaxApplication[syntaxString["sequencePrepend"], {_, rest_}]] := sequenceLiteralQ[rest]
sequenceLiteralQ[syntaxString["emptySequence"]] := True
sequenceLiteralQ[_] := False

(* a dependent sum over a function of one variable shows its binder, as ∀ does *)
displayApplication[
	syntaxSymbol[HoldComplete[DependentSum]],
	{_, syntaxApplication[syntaxSymbol[HoldComplete[RightTeeArrow]], {binder : syntaxApplication[syntaxSymbol[HoldComplete[Colon]], _], body_}]}
] := syntaxHead[NotExists, {binder, body}]

(* a subtype of a predicate of one variable shows as Lean shows it, {x ∶ A // p} *)
displayApplication[
	syntaxSymbol[HoldComplete[Subtype]],
	{syntaxApplication[syntaxSymbol[HoldComplete[RightTeeArrow]], {binder : syntaxApplication[syntaxSymbol[HoldComplete[Colon]], _], body_}]}
] := delimited["{", syntaxHead[Row, {syntaxHead[List, {binder, syntaxString[" // "], body}]}], "}"]

(* several binders are each parenthesized, unless their brackets already delimit them *)
binderRow[{binder_}] := binder
(* a space the front end and a page drawn from it keep, which a plain one between two names is not *)
binderRow[binders_List] := syntaxHead[Row, {
	syntaxHead[List, Replace[binders, colon : syntaxApplication[syntaxSymbol[HoldComplete[Colon]], _] :> delimited["(", colon, ")"], {1}]],
	syntaxString["\[NonBreakingSpace]"]
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
sortDisplay[keyword_String, level_] := syntaxHead[Row, {syntaxHead[List, {syntaxString[keyword], styled[level, "Level"]}], syntaxString[" "]}]

levelArgumentDisplay[level : syntaxApplication[syntaxSymbol[HoldComplete[Plus]], _]] := delimited["(", level, ")"]
levelArgumentDisplay[syntaxApplication[syntaxSymbol[HoldComplete[head : Max | ImpredicativeMaximum]], levels_List]] := delimited[
	"(",
	syntaxHead[Row, {syntaxHead[List, Prepend[levelArgumentDisplay /@ levels, syntaxString[Replace[head, {Max -> "max", ImpredicativeMaximum -> "imax"}]]]], syntaxString[" "]}],
	")"
]
levelArgumentDisplay[level_] := level


(* ::Subsection:: *)
(*Proofs*)


(* the display is interpretable: copied or evaluated again it is the proof. It holds a handle to the proof, a symbol of
   the session whose value it is, as the proof holds one to its environment, not the proof itself: a proof term shares its
   parts, which a notebook would write out each time they occur, hundreds of megabytes for a proof by "Ring" *)
TypeTheoryProof /: MakeBoxes[proof : TypeTheoryProof[data_Association], form : StandardForm | TraditionalForm] := With[
	{boxes = withDisplayEnvironment[data["Environment"], ToBoxes[proofPanel[data, form], form]], name = storedProofName[proof]},
	ToExpression[name, InputForm, Function[handle, InterpretationBox[boxes, handle], HoldAllComplete]]
]

$storedProofCount = 0

storedProofName[proof_] := With[{name = Context[$storedProofCount] <> "storedProof" <> ToString[++$storedProofCount]},
	ToExpression[name, InputForm, Function[handle, handle = proof, HoldAllComplete]];
	name
]

proofPanel[data_, form_] := Framed[
	Column[Prepend[Function[goal, goalPanel[data, goal, form]] /@ data["Goals"], proofHeader[Length[data["Goals"]], Length[Lookup[data, "Holes", <||>]]]], Spacings -> 1.2],
	FrameStyle -> LightDarkSwitched[GrayLevel[0.8], GrayLevel[0.35]],
	RoundingRadius -> 4,
	FrameMargins -> 8
]

proofHeader[0, 0] := Style["Proof complete", Bold, StandardGreen]
proofHeader[0, holes_Integer] := Row[{Style["Proof complete", Bold, StandardGreen], Style["  with " <> countText[holes, "hole"], StandardOrange]}]
proofHeader[goals_Integer, 0] := Row[{Style["Proof", Bold], Style["  " <> countText[goals, "goal"], StandardGray]}]
proofHeader[goals_Integer, holes_Integer] := Row[{Style["Proof", Bold], Style["  " <> countText[goals, "goal"], StandardGray], Style[", " <> countText[holes, "hole"], StandardOrange]}]

countText[1, noun_String] := "1 " <> noun
countText[n_Integer, noun_String] := ToString[n] <> " " <> noun <> "s"

(* a hole shows as hole, with its annotation as a tooltip, and stays the hole behind the display *)
TypeTheoryHole /: MakeBoxes[hole : TypeTheoryHole[annotation___], form : StandardForm | TraditionalForm] /; Length[{annotation}] <= 1 := With[
	{
		tooltip = Replace[{annotation}, {{} -> "\"no annotation\"", {given_} :> MakeBoxes[given, form]}],
		color = StandardOrange
	},
	InterpretationBox[TooltipBox[StyleBox["hole", FontSlant -> Italic, FontColor -> color], tooltip], hole]
]

goalPanel[data_, goal_, form_] := Replace[Quiet @ catchKernelFailure[goalDisplaySyntax[data, goal]], {
	{case_, hypotheses_List, target_} :> Block[{$goalSymbols = AssociationMap[True&, Catenate[binderSymbol /@ hypotheses]], $goalTypes = Association[Catenate[binderTyping /@ hypotheses]]}, Column[Join[
		Replace[case, {None -> {}, HoldComplete[name_] :> {Style[Row[{"case ", HoldForm[name]}], Italic, StandardGray]}}],
		Function[hypothesis, RawBoxes[typeTheoryBoxes[hypothesis, form]]] /@ hypotheses,
		{Row[{Style["\[RightTee] ", Bold], RawBoxes[typeTheoryBoxes[target, form]]}]}
	]]],
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
		rows = inDeclarationEnvironment[declaration, Join[
			Function[heading, Join[{StyleBox[keyword, FontWeight -> Bold, FontColor -> StandardBlue]}, declarationRow[heading, form]]] /@ headings,
			Function[constructor, Join[{"|"}, declarationRow[constructor, form]]] /@ constructors
		]]
	},
	InterpretationBox[GridBox[rows, GridBoxAlignment -> {"Columns" -> {{Left}}}, GridBoxSpacings -> {"Columns" -> {{0.6}}}], declaration]
]

(* A declaration has no environment of its own, so it shows in the default one; one that TypeTheoryFormalize made shows in
   the environment it was made for, so that its constants are bold and have their types on mouseover. The table only
   decides a display. *)
$declarationEnvironments = <||>

rememberDisplayEnvironment[declarations_List, environment_] := (
	Scan[Function[declaration, $declarationEnvironments[Hash[declaration]] = environment], declarations];
	declarations
)
rememberDisplayEnvironment[other_, _] := other

SetAttributes[inDeclarationEnvironment, HoldRest]
inDeclarationEnvironment[declaration_, rows_] := Replace[Lookup[$declarationEnvironments, Hash[declaration], None], {
	None :> rows,
	environment_ :> withDisplayEnvironment[environment, rows]
}]

declarationRow[{name_, type_}, form_] := {nameBoxes[name, form], ":", typeTheoryBoxes[type, form]}
declarationRow[{name_, None, value_}, form_] := {nameBoxes[name, form], ":=", typeTheoryBoxes[value, form]}
declarationRow[{name_, type_, value_}, form_] := {nameBoxes[name, form], ":", RowBox[{typeTheoryBoxes[type, form], " := ", typeTheoryBoxes[value, form]}]}

(* a declared name shows as itself: the constructor "zero" is not shown as 0 where it is declared *)
nameBoxes[name_, form_] := Block[{$displayedNaturalNumbers = <||>}, typeTheoryBoxes[name, form]]


(* ::Subsection:: *)
(*Proof trees*)


TypeTheoryProofTree /: MakeBoxes[tree : TypeTheoryProofTree[_String, _, _List], form : StandardForm | TraditionalForm] :=
	InterpretationBox[#, tree] & [derivationBoxes[tree, form]]

$ruleLabels = <|
	"ImpliesIntro" -> "\[RightArrow]I", "ImpliesElim" -> "\[RightArrow]E", "AndIntro" -> "\[And]I", "AndElim" -> "\[And]E",
	"OrIntro" -> "\[Or]I", "OrElim" -> "\[Or]E", "FalseElim" -> "\[UpTee]E"
|>

derivationBoxes[TypeTheoryProofTree["Assumption", claim_, {}], form_] := MakeBoxes[claim, form]
(* the script level is held, so that a deep derivation keeps one size *)
derivationBoxes[TypeTheoryProofTree[rule_String, claim_, premises_List], form_] := RowBox[{
	StyleBox[
		FractionBox[
			If[premises === {}, "", RowBox[Riffle[Map[Function[premise, derivationBoxes[premise, form]], premises], "\[ThickSpace]\[ThickSpace]\[ThickSpace]"]]],
			MakeBoxes[claim, form]
		],
		ScriptLevel -> 0,
		AllowScriptLevelChange -> False
	],
	StyleBox[Lookup[$ruleLabels, rule, rule], FontSize -> 10]
}]
