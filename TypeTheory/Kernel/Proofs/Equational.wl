(* ::Package:: *)

(*
Equational: proofs of equations from equational hypotheses, by replaying a proof that Wolfram's
FindEquationalProof finds.

The goal s == t and the hypotheses of the form ForAll[{x1, ...}, l == r], all equations of one type,
are written as Wolfram expressions: each head, a constant or a variable of the context applied to
arguments, becomes a symbol of its own, and each bound variable a variable. FindEquationalProof finds a
proof by completion, a list of steps, each with the rewrite rules it used and where. Every step is
replayed: the equation it derives is computed again, checked against the statement the proof gives it,
and proved, a lemma for all values of its variables, from the lemmas before it.

	Axiom              a hypothesis, perhaps turned around, its variables renamed
	CriticalPairLemma  a term with two rewrites: the rule of one lemma at its root, and the rule of
	                   another at a position, their left sides unified; the two results are equal
	SubstitutionLemma  a lemma with one side rewritten at a position by the rule of another
	Hypothesis         the goal; the steps from it rewrite its sides until they are the same term
	Conclusion         the goal with two sides that are the same term

A lemma of the goal is no lemma for all values: its sides carry proofs of s, or t, equal to them, and
the conclusion joins the two. The kernel checks the proof again, so a mistake makes it fail to check.

	equation   {left, right, proof}, Wolfram expressions and a core proof of the equation of their terms
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[equationalProof]


(* ::Section:: *)
(*Usage Messages*)


equationalProof::usage = "equationalProof[environment, context, {type, left, right}, {{id, binderCount}, ...}] gives a core proof of left == right in type from the hypotheses id of \
the context, each an equation of type for all values of its binderCount variables, by replaying a proof that Wolfram's FindEquationalProof finds; or a string that says why there is none."


(* ::Section:: *)
(*Function Definitions*)


(* the state of one replay: the environment, the local context, the type and its level, the
   translation of heads to symbols and back, and the lemmas proved *)
$replayEnvironment = None
$replayContext = <||>
$replayType = None
$replayLevel = 0
$symbolOfHead = <||>
$headOfSymbol = <||>
$goalSides = {}
$hypothesisConstants = <||>

equationalProof[environment_, context_, {type_, left_, right_}, hypotheses_List] := Block[
	{
		$replayEnvironment = environment,
		$replayContext = context,
		$replayType = type,
		$replayLevel = sortLevel[environment, context, type],
		$symbolOfHead = <||>,
		$headOfSymbol = <||>,
		$goalSides = {},
		$hypothesisConstants = <||>
	},
	Catch[
		$goalSides = {wolframTerm[left, <||>], wolframTerm[right, <||>]};
		With[{axioms = DeleteCases[Function[hypothesis, hypothesisAxiom @@ hypothesis] /@ hypotheses, None]},
			replayed[$goalSides, axioms, TimeConstrained[Quiet @ FindEquationalProof[Equal @@ $goalSides, Function[axiom, axiom["Axiom"]] /@ axioms], 30, $Aborted]]
		],
		$replayFailure
	]
]

replayFailure[reason_String] := Throw[reason, $replayFailure]


(* ::Subsection:: *)
(*Translation*)


(* <|"Id" -> id, "Variables" -> {variable, ...}, "Axiom" -> ForAll[...]|>, the hypothesis a lemma for all values of its variables;
   None for one whose two sides are the same term, which says nothing *)
hypothesisAxiom[id_, binderCount_Integer] := Module[{type = $replayContext[id]["Type"], ids = {}, variables},
	Do[
		type = Replace[type, {
			dependentFunctionType[_, domain_, codomain_, _] :> With[{fresh = freshFreeVariable[]},
				ids = Append[ids, fresh];
				instantiateBoundVariable[codomain, freeVariable[fresh]]
			]
		}],
		binderCount
	];
	variables = Table[Symbol["TypeTheoryEquational`x" <> ToString[id] <> "x" <> ToString[k]], {k, binderCount}];
	Replace[type, {
		application[application[application[constantReference[HoldComplete[Equal], _], _], l_], r_] :> With[
			{variableOf = AssociationThread[ids, variables]},
			{sides = {wolframTerm[l, variableOf], wolframTerm[r, variableOf]}, bound = variables},
			If[ First[sides] === Last[sides],
				None,
				(* ForAll holds its arguments, so the variables and sides go in as values *)
				<|"Id" -> id, "Variables" -> bound, "Axiom" -> If[bound === {}, Equal @@ sides, With[{equation = Equal @@ sides}, ForAll[bound, equation]]]|>
			]
		],
		_ :> replayFailure["a hypothesis is not an equation"]
	}]
]

(* a head applied to arguments becomes a symbol applied to them; a variable of the hypothesis becomes its
   variable, and may not be applied *)
wolframTerm[term_, variableOf_Association] := Replace[applicationSpine[term], {
	{freeVariable[id_], {}} /; KeyExistsQ[variableOf, id] :> variableOf[id],
	{freeVariable[id_], _} /; KeyExistsQ[variableOf, id] :> replayFailure["a variable of a hypothesis is applied"],
	{head_, arguments_} :> With[{symbol = symbolOf[head, variableOf]}, If[arguments === {}, symbol, symbol @@ (Function[argument, wolframTerm[argument, variableOf]] /@ arguments)]]
}]

(* a head that mentions a variable of the hypothesis cannot be a constant *)
symbolOf[head_, variableOf_Association] := (
	If[ ! FreeQ[head, freeVariable[Alternatives @@ Keys[variableOf]]] || looseBoundRange[head] > 0,
		replayFailure["a hypothesis has a term that is not a head applied to terms"]
	];
	Lookup[$symbolOfHead, Key[head], With[{symbol = Symbol["TypeTheoryEquational`f" <> ToString[Length[$symbolOfHead] + 1]]},
		$symbolOfHead[head] = symbol;
		$headOfSymbol[symbol] = head;
		symbol
	]]
)

(* the core term of a Wolfram expression, its variables the free variables given; a variable without
   one, which a step's rewrites drop, stands for any term of the type, the goal's left side *)
coreTerm[expression_, freeOf_Association] := Replace[expression, {
	variable_Symbol /; KeyExistsQ[freeOf, variable] :> freeOf[variable],
	symbol_Symbol /; KeyExistsQ[$headOfSymbol, symbol] :> $headOfSymbol[symbol],
	(head_Symbol)[arguments___] /; KeyExistsQ[$headOfSymbol, head] :> makeApplication[$headOfSymbol[head], Function[argument, coreTerm[argument, freeOf]] /@ {arguments}],
	_Symbol :> coreTerm[First[$goalSides], <||>],
	_ :> replayFailure["a step of the proof has a term outside the goal and the hypotheses"]
}]


(* ::Subsection:: *)
(*Equations of the type*)


equalityConstant[name_] := constantReference[HoldComplete[name], {$replayLevel}]

reflexivityProof[term_] := makeApplication[equalityConstant[EqualityReflexivity], {$replayType, term}]

symmetricProof[left_, right_, proof_] := makeApplication[equalityConstant[EqualitySymmetry], {$replayType, left, right, proof}]

transitiveProof[left_, middle_, right_, proof_, otherProof_] := makeApplication[equalityConstant[EqualityTransitivity], {$replayType, left, middle, right, proof, otherProof}]

(* context[left] == context[right] from left == right, for core terms in the local context *)
congruenceProof[contextBody_, left_, right_, proof_, local_Association] := With[
	{
		innerType = inferType[$replayEnvironment, local, left],
		outerType = inferType[$replayEnvironment, local, instantiateBoundVariable[contextBody, left]]
	},
	makeApplication[
		constantReference[HoldComplete[EqualityCongruence], {sortLevel[$replayEnvironment, local, innerType], sortLevel[$replayEnvironment, local, outerType]}],
		{innerType, outerType, left, right, lambdaAbstraction[HoldComplete[x], innerType, contextBody, "Explicit"], proof}
	]
]


(* ::Subsection:: *)
(*Replay*)


replayed[goal_, axioms_List, proof_ProofObject] := Module[{lemmas = <||>, steps = Normal[proof["ProofDataset"]], conclusion = None},
	KeyValueMap[
		Function[{key, step}, lemmas[key] = Replace[
			Catch[replayedStep[First[key], step, lemmas, axioms, goal], $replayFailure, Function[{reason, tag}, {$replayFailure, reason}]],
			{$replayFailure, reason_} :> replayFailure[reason <> " (" <> StringRiffle[ToString /@ key, " "] <> ")"]
		]],
		steps
	];
	conclusion = SelectFirst[Keys[lemmas], Function[key, First[key] === "Conclusion"], None];
	If[conclusion === None, replayFailure["the proof has no conclusion"], lemmas[conclusion]["GoalProof"]]
]
replayed[_, _, $Aborted] := replayFailure["FindEquationalProof finds no proof in 30 seconds"]
replayed[_, _, other_] := replayFailure["FindEquationalProof finds no proof, and gives " <> ToString[Short[other, 2]]]

statementSides[HoldForm[Equal[left_, right_]]] := {left, right}
statementSides[_] := replayFailure["a step states no equation"]

(* the variables of a statement: the symbols that are not heads of the goal or the hypotheses *)
statementVariables[sides_List] := Sort @ DeleteDuplicates @ Cases[sides, symbol_Symbol /; ! KeyExistsQ[$headOfSymbol, symbol] && symbol =!= List, {0, Infinity}, Heads -> True]

replayedStep["Axiom", step_, lemmas_, axioms_List, _] := With[{sides = statementSides[step["Statement"]]},
	Replace[
		SelectFirst[
			Function[axiom, {axiom, renamingMatch[sides, axiomSides[axiom], axiom["Variables"]]}] /@ axioms,
			Function[pair, Last[pair] =!= None],
			None
		],
		{
			{axiom_, matched_} :> axiomLemma[sides, axiom, matched],
			None :> replayFailure["an axiom of the proof is none of the hypotheses"]
		}
	]
]

(* FindEquationalProof reads the goal's symbols as variables, and names them anew in the hypothesis; there
   they stand for the goal's heads, constants of the steps from the hypothesis alone *)
replayedStep["Hypothesis", step_, _, _, goal_List] := With[{sides = statementSides[step["Statement"]]},
	{renamed = renamedSymbols[sides, goal], turned = renamedSymbols[Reverse[sides], goal]},
	If[renamed === None && turned === None, replayFailure["the hypothesis of the proof is not the goal"]];
	$hypothesisConstants = Association[Function[pair, First[pair] -> $headOfSymbol[Last[pair]]] /@ If[renamed =!= None, renamed, turned]];
	<|
		"Sides" -> sides,
		"Goal" -> True,
		"Origins" -> If[renamed =!= None, {1, 2}, {2, 1}],
		"Proofs" -> Function[term, reflexivityProof[coreTerm[term, $hypothesisConstants]]] /@ sides
	|>
]

(* {statement symbol -> goal symbol, ...} where the statement is the goal with symbols named anew, or None *)
renamedSymbols[statement_, goal_] := Catch[DeleteDuplicates @ renamings[statement, goal], $notRenamed]

renamings[same_, same_] := {}
renamings[symbol_Symbol, goalSymbol_Symbol] /; KeyExistsQ[$headOfSymbol, goalSymbol] := {symbol -> goalSymbol}
renamings[{first_, rest___}, {goalFirst_, goalRest___}] /; Length[{rest}] === Length[{goalRest}] := Join[renamings[first, goalFirst], renamings[{rest}, {goalRest}]]
renamings[{}, {}] := {}
renamings[(head_)[arguments___], (head_)[goalArguments___]] /; Length[{arguments}] === Length[{goalArguments}] := renamings[{arguments}, {goalArguments}]
renamings[_, _] := Throw[None, $notRenamed]

replayedStep["CriticalPairLemma", step_, lemmas_, _, _] := With[{facts = step["Proof"], sides = statementSides[step["Statement"]]},
	lemmaFromEquation[sides, criticalPair[lemmas[stepKey[facts["Construct"]]], facts["Orientation"], facts["Rule"], lemmas[stepKey[facts["MatchingConstruct"]]], facts["MatchingOrientation"], facts["MatchingRule"], facts["Position"]]]
]

replayedStep[kind : "SubstitutionLemma" | "Conclusion", step_, lemmas_, _, _] := With[{facts = step["Proof"], sides = statementSides[step["Statement"]]},
	With[{input = lemmas[stepKey[facts["Input"]]]},
		If[ TrueQ[input["Goal"]],
			goalSubstitution[kind, sides, input, facts["InputOrientation"], facts["Side"], facts["Position"], lemmas[stepKey[facts["Construct"]]], facts["Orientation"], facts["Rule"]],
			lemmaFromEquation[sides, substitution[input, facts["InputOrientation"], facts["Side"], facts["Position"], lemmas[stepKey[facts["Construct"]]], facts["Orientation"], facts["Rule"]]]
		]
	]
]

replayedStep[kind_, _, _, _, _] := replayFailure["the proof has a step of a kind not replayed: " <> ToString[kind]]

stepKey[{kind_String, index_Integer}] := {kind, index}

axiomSides[axiom_Association] := Replace[axiom["Axiom"], {ForAll[_, Equal[l_, r_]] :> {l, r}, Equal[l_, r_] :> {l, r}}]


(* ::Subsubsection:: *)
(*Lemmas for all values*)


(* A lemma for all values of its variables: <|"Sides" -> {l, r}, "Variables" -> {v, ...}, "Proof" -> λ v ... . proof|>.
   Its instance for terms of other variables is its proof applied to their core terms. *)

(* {pattern bindings, flipped} where sides are an instance of target, or of target turned around, the variables those of target *)
renamingMatch[sides_List, target_List, variables_List] := With[{pattern = target /. Thread[variables -> (Pattern[#, Blank[]] & /@ variables)]},
	Which[
		MatchQ[sides, pattern], {Replace[sides, pattern :> variables], False},
		MatchQ[sides, Reverse[pattern]], {Replace[sides, Reverse[pattern] :> variables], True},
		True, None
	]
]

(* the lemma of an axiom: the hypothesis applied to the axiom's terms for its variables *)
axiomLemma[sides_List, axiom_Association, {values_List, flipped_}] := lemmaOver[sides, Function[{freeOf, local},
	With[{proof = makeApplication[freeVariable[axiom["Id"]], Function[value, coreTerm[value, freeOf]] /@ values]},
		If[flipped, symmetricProof[coreTerm[Last[sides], freeOf], coreTerm[First[sides], freeOf], proof], proof]
	]
]]

(* the lemma of the equation computed for a step, checked against the step's statement *)
lemmaFromEquation[sides_List, equation_Association] := Replace[renamingMatch[sides, equation["Sides"], equation["Variables"]], {
	None :> replayFailure["a step derives an equation other than the one it states"],
	{values_List, flipped_} :> lemmaOver[sides, Function[{freeOf, local},
		With[{proof = equation["Proof"][AssociationThread[equation["Variables"], Function[value, coreTerm[value, freeOf]] /@ values], local]},
			If[flipped, symmetricProof[coreTerm[Last[sides], freeOf], coreTerm[First[sides], freeOf], proof], proof]
		]
	]]
}]

(* the proof of the sides for all values of their variables: body builds it from the free variables
   standing for them, in the context extended by them *)
lemmaOver[sides_List, body_] := With[{variables = statementVariables[sides]},
	With[{ids = Table[freshFreeVariable[], Length[variables]]},
		{local = Fold[Function[{context, id}, extendContext[context, id, HoldComplete[v], $replayType, "Explicit"]], $replayContext, ids]},
		<|"Sides" -> sides, "Variables" -> variables, "Proof" -> makeLambda[local, ids, body[AssociationThread[variables, freeVariable /@ ids], local]]|>
	]
]

(* the lemma's proof for the sides with values for its variables, terms over other variables *)
instanceProof[lemma_Association, valueOf_Association, freeOf_Association] :=
	makeApplication[lemma["Proof"], Function[variable, coreTerm[Lookup[valueOf, variable, variable], freeOf]] /@ lemma["Variables"]]

(* {l, r} of a rule, as Wolfram expressions, its patterns' names the variables; the rule names its
   variables in its own order, not the lemma's *)
ruleSides[rule_Rule] := {First[rule] /. Verbatim[Pattern][name_, Verbatim[Blank][]] :> name, Last[rule]}

ruleVariables[rule_Rule] := DeleteDuplicates @ Cases[First[rule], Verbatim[Pattern][name_, _] :> name, {0, Infinity}, Heads -> True]

(* a proof of left == right, an instance of the lemma turned as orientation says, the lemma's variables
   found by matching its sides against the instance *)
orientedInstanceProof[lemma_Association, orientation_Integer, {left_, right_}, freeOf_Association] := With[
	{oriented = If[orientation === 1, lemma["Sides"], Reverse[lemma["Sides"]]], variables = lemma["Variables"]},
	{patterned = oriented /. Thread[variables -> (Pattern[#, Blank[]] & /@ variables)]},
	If[ ! MatchQ[{left, right}, patterned],
		replayFailure["a rule is no instance of its lemma"],
		(* the variables go into the rule as values, for its right side to name them *)
		With[{proof = instanceProof[lemma, AssociationThread[variables, Replace[{left, right}, patterned :> variables]], freeOf]},
			If[orientation === 1, proof, symmetricProof[coreTerm[right, freeOf], coreTerm[left, freeOf], proof]]
		]
	]
]

(* an equation computed by a step: <|"Sides", "Variables", "Proof" -> Function[{values, local}, proof]|>, values the free variables of its variables *)
criticalPair[construct_Association, orientation_Integer, rule_Rule, matching_Association, matchingOrientation_Integer, matchingRule_Rule, position_List] := Module[
	{l1, r1, l2, r2, renaming, σ, overlap, first, second, variables},
	{l1, r1} = ruleSides[rule];
	renaming = AssociationThread[ruleVariables[matchingRule], Table[Symbol["TypeTheoryEquational`y" <> ToString[k]], {k, Length[ruleVariables[matchingRule]]}]];
	{l2, r2} = ruleSides[matchingRule] /. renaming;
	σ = unified[subtermAt[l1, position], l2, Join[ruleVariables[rule], Values[renaming]]];
	If[σ === None, replayFailure["the rules of a critical pair do not overlap"]];
	overlap = l1 /. σ;
	first = r1 /. σ;
	second = If[position === {}, r2 /. σ, ReplacePart[overlap, position -> (r2 /. σ)]];
	variables = statementVariables[{first, second}];
	<|
		"Sides" -> {first, second},
		"Variables" -> variables,
		"Proof" -> Function[{freeOf, local}, With[
			{
				overlapTerm = coreTerm[overlap, freeOf],
				firstTerm = coreTerm[first, freeOf],
				secondTerm = coreTerm[second, freeOf],
				firstProof = orientedInstanceProof[construct, orientation, {overlap, first}, freeOf],
				secondProof = positionedProof[overlap, position, matching, matchingOrientation, {l2, r2}, σ, freeOf, local]
			},
			transitiveProof[firstTerm, overlapTerm, secondTerm, symmetricProof[overlapTerm, firstTerm, firstProof], secondProof]
		]]
	|>
]

(* the step's input with side rewritten at the position by the rule *)
substitution[input_Association, inputOrientation_Integer, side_Integer, position_List, construct_Association, orientation_Integer, rule_Rule] := Module[
	{sides, rewritten, σ, result},
	sides = If[inputOrientation === 1, input["Sides"], Reverse[input["Sides"]]];
	{rewritten, σ} = rewrittenAt[If[side === 1, First[sides], Last[sides]], position, rule];
	result = If[side === 1, {rewritten, Last[sides]}, {First[sides], rewritten}];
	<|
		"Sides" -> result,
		"Variables" -> input["Variables"],
		"Proof" -> Function[{freeOf, local}, Module[{inputProof, stepProof, u, v},
			{u, v} = Function[term, coreTerm[term, freeOf]] /@ sides;
			inputProof = With[{proof = instanceProof[input, <||>, freeOf]}, If[inputOrientation === 1, proof, symmetricProof[v, u, proof]]];
			stepProof = positionedProof[If[side === 1, First[sides], Last[sides]], position, construct, orientation, ruleSides[rule], σ, freeOf, local];
			If[ side === 1,
				transitiveProof[coreTerm[rewritten, freeOf], u, v, symmetricProof[u, coreTerm[rewritten, freeOf], stepProof], inputProof],
				transitiveProof[u, v, coreTerm[rewritten, freeOf], inputProof, stepProof]
			]
		]]
	|>
]

(* {the term rewritten at the position by the rule, the substitution} *)
rewrittenAt[term_, position_List, rule_Rule] := With[
	{sub = subtermAt[term, position], patterned = First[rule], names = DeleteDuplicates @ Cases[First[rule], Verbatim[Pattern][name_, _] :> name, {0, Infinity}, Heads -> True]},
	If[ ! MatchQ[sub, patterned],
		replayFailure["a rule does not apply where a step rewrites"],
		With[{σ = AssociationThread[names, Replace[sub, patterned :> names]]},
			{If[position === {}, Last[rule] /. σ, ReplacePart[term, position -> (Last[rule] /. σ)]], σ}
		]
	]
]

(* term == term with the subterm at the position rewritten by the rule {l, r} under σ, the lemma turned as
   orientation says *)
positionedProof[term_, position_List, lemma_Association, orientation_Integer, {ruleLeft_, ruleRight_}, σ_Association, freeOf_Association, local_Association] := With[
	{left = ruleLeft /. σ, right = ruleRight /. σ},
	{proof = orientedInstanceProof[lemma, orientation, {left, right}, freeOf]},
	If[ position === {},
		proof,
		congruenceProof[
			coreTerm[ReplacePart[term, position -> $hole], Append[freeOf, $hole -> boundVariable[0]]],
			coreTerm[left, freeOf],
			coreTerm[right, freeOf],
			proof,
			local
		]
	]
]

$hole = Symbol["TypeTheoryEquational`hole"]

(* the subterm at a position, {} being the whole term, which Extract would read as no positions *)
subtermAt[term_, {}] := term
subtermAt[term_, position_List] := Extract[term, position]


(* ::Subsubsection:: *)
(*Lemmas of the goal*)


(* A lemma of the goal: <|"Sides" -> {u, v}, "Goal" -> True, "Origins" -> {i, j}, "Proofs" -> {proof of side i of the goal == u, proof of side j == v}|>.
   A step rewrites a side, and the conclusion, whose sides are the same, joins the proofs into one of
   the goal. *)
goalSubstitution[kind_, sides_List, input_Association, inputOrientation_Integer, side_Integer, position_List, construct_Association, orientation_Integer, rule_Rule] := Module[
	{oriented, origins, proofs, rewritten, σ, result, stepProof, original, newProofs},
	oriented = If[inputOrientation === 1, input["Sides"], Reverse[input["Sides"]]];
	origins = If[inputOrientation === 1, input["Origins"], Reverse[input["Origins"]]];
	proofs = If[inputOrientation === 1, input["Proofs"], Reverse[input["Proofs"]]];
	original = If[side === 1, First[oriented], Last[oriented]];
	{rewritten, σ} = rewrittenAt[original, position, rule];
	result = If[side === 1, {rewritten, Last[oriented]}, {First[oriented], rewritten}];
	stepProof = positionedProof[original, position, construct, orientation, ruleSides[rule], σ, $hypothesisConstants, $replayContext];
	newProofs = MapAt[
		Function[proof, transitiveProof[coreTerm[goalSide[sideOf[origins, side]], <||>], coreTerm[original, $hypothesisConstants], coreTerm[rewritten, $hypothesisConstants], proof, stepProof]],
		proofs,
		side
	];
	Which[
		kind === "Conclusion" && First[result] === Last[result],
			conclusionProof[First[result], origins, newProofs],
		kind === "Conclusion",
			replayFailure["the conclusion of the proof has two sides"],
		result === sides,
			<|"Sides" -> result, "Goal" -> True, "Origins" -> origins, "Proofs" -> newProofs|>,
		Reverse[result] === sides,
			<|"Sides" -> sides, "Goal" -> True, "Origins" -> Reverse[origins], "Proofs" -> Reverse[newProofs]|>,
		True,
			replayFailure["a step derives an equation other than the one it states"]
	]
]

sideOf[pair_List, 1] := First[pair]
sideOf[pair_List, 2] := Last[pair]

goalSide[index_Integer] := sideOf[$goalSides, index]

(* s == t from s == w and t == w, or the same with the sides of the goal turned around *)
conclusionProof[common_, origins_List, proofs_List] := With[{s = coreTerm[goalSide[1], <||>], t = coreTerm[goalSide[2], <||>], w = coreTerm[common, $hypothesisConstants]},
	<|"GoalProof" -> If[ origins === {1, 2},
		transitiveProof[s, w, t, First[proofs], symmetricProof[t, w, Last[proofs]]],
		transitiveProof[s, w, t, Last[proofs], symmetricProof[t, w, First[proofs]]]
	]|>
]


(* ::Subsection:: *)
(*Unification*)


(* the most general substitution of the variables that makes a and b the same, or None *)
unified[a_, b_, variables_List] := Catch[Fold[Function[{σ, pair}, unifiedPair[First[pair] /. σ, Last[pair] /. σ, σ, variables]], <||>, {{a, b}}], $notUnified]

unifiedPair[a_, b_, σ_, _] /; a === b := σ
unifiedPair[a_Symbol, b_, σ_, variables_] /; MemberQ[variables, a] := bound[a, b, σ]
unifiedPair[a_, b_Symbol, σ_, variables_] /; MemberQ[variables, b] := bound[b, a, σ]
unifiedPair[(head_)[arguments___], (head_)[otherArguments___], σ_, variables_] /; Length[{arguments}] === Length[{otherArguments}] :=
	Fold[Function[{accumulated, pair}, unifiedPair[First[pair] /. accumulated, Last[pair] /. accumulated, accumulated, variables]], σ, Transpose[{{arguments}, {otherArguments}}]]
unifiedPair[_, _, _, _] := Throw[None, $notUnified]

bound[variable_, value_, σ_] := If[ ! FreeQ[value, variable],
	Throw[None, $notUnified],
	Append[(# /. variable -> value) & /@ σ, variable -> value]
]
