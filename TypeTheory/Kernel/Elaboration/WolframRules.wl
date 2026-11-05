(* ::Package::"Tags"-><|"BadSymbol" -> <|"Match" -> <|Enabled -> False|>|>|>:: *)

(*
WolframRules: the rules of a Wolfram Language symbol as a term of TypeTheoryEnvironment["WolframLanguage"], what
TypeTheoryFormalize[f, "Meaning" -> "Rules"] declares.

The rules of f, its DownValues, are a definition of type Expressions -> Option[Expressions]: the expression f[...]
rewrites to by the first rule that matches it, "none" where none does and the expression stays as it is. It is

	Function[{Typed[expression, Expressions]}, MatchFirst[MatchSum[rule1, MatchSum[rule2, ...]]]]

each rule a Match of the expressions its right side gives, quoted, its pattern variables the parts they match. The
left side of each rule is translated from the pattern itself, construct by construct:

	_, _h, x_                          the part itself, a Condition on SameQ of its Head and h, the part bound to x
	a literal expression               a Condition on SameQ of the part and the expression, quoted
	h[p1, p2, ...]                     a normal expression: a Condition on its length, then each part by MatchPart
	__, ___, p.., p..., OptionsPattern a prefix of the arguments, every split by "splits" tried, shortest first, or
	                                   longest first under Longest; a named one binds the list of its expressions
	PatternSequence, OrderlessPatternSequence   patterns that take a run of arguments, in turn or in every order
	p | q, Except, p /; c, p?t         MatchSum of the alternatives, a Condition on MatchQ, on SameQ of the
	                                   ExpressionValue of the condition, quoted, and True
	p : d, x_.                         MatchSum of the argument given and the default
	an Orderless head, a Flat head     the arguments in every order, by "permutations"; a pattern for one argument
	                                   also takes a run of two or more, wrapped in the head
	HoldPattern, Verbatim              the pattern inside it, the expression inside it as a literal

The matches are those of the Wolfram Language, in its order, so the first is the rule it applies, but an Association is
an atom and KeyValuePattern does not translate. A name met a second time is a Condition on SameQ; a repeated pattern
that binds names binds them at its first repetition. Every symbol and every atom but a natural number is an axiom of
type Atoms, named by its full name or its InputForm, declared where a rule uses it. The right side is quoted as it is:
the rules give one step of evaluation, and the Wolfram Language evaluates the result further.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[rulesDeclarations]
PackageScoped[rulesMatchFunction]


(* ::Section:: *)
(*Usage Messages*)


rulesMatchFunction::usage = "rulesMatchFunction[{HoldComplete[rule], ...}] gives HoldComplete of the term of type Expressions -> Match[Expressions] whose results are those of the rules at an expression, in order, or {\"Untranslatable\", rule} for the first rule that does not translate."
rulesDeclarations::usage = "rulesDeclarations[environment, HoldComplete[symbol]] gives the declarations of the rules of symbol: the atoms they use, then the definition of type Expressions -> Option[Expressions] named \"DownValues[symbol]\"."


(* ::Section:: *)
(*Function Definitions*)


rulesDeclarations[environment_, held : HoldComplete[symbol_Symbol]] := Which[
	! constantDeclaredQ[environment, HoldComplete[MatchFirst]],
		kernelFailure["RulesEnvironment", "The rules of `1` are terms of TypeTheoryEnvironment[\"WolframLanguage\"], which has Expressions and MatchFirst.", {HoldForm[symbol]}],
	True,
		Replace[Reap[translatedRules[held], atomDeclaration], {
			{value_HoldComplete, atoms_} :> With[{declarations = Append[missingDeclarations[environment, DeleteDuplicates[Catenate[Catenate[atoms]]]], rulesDefinition[held, value]]},
				If[ FailureQ[Quiet[TypeTheoryEnvironment[environment, declarations]]],
					kernelFailure["Unformalizable", "The rules of `1` translate to a term that does not check.", {HoldForm[symbol]}],
					declarations
				]
			],
			{{"Untranslatable", rule_}, _} :> kernelFailure["Untranslatable", "The rule `1` does not translate: its pattern has a part without a counterpart in matches.", {rule}]
		}]
]

(* by the symbol's name, without its context, which is where it was defined and would change the name with it; the atoms
   keep their full names, as two symbols of one name in two contexts are different expressions *)
rulesName[HoldComplete[symbol_Symbol]] := "DownValues[" <> SymbolName[Unevaluated[symbol]] <> "]"

rulesDefinition[held_, HoldComplete[value_]] := With[{name = rulesName[held]}, TypeTheoryDefinition[name, Typed[value, Expressions -> Option[Expressions]]]]

(* the value of the rules, or {"Untranslatable", rule} for the first rule that does not translate *)
translatedRules[HoldComplete[symbol_Symbol]] := Catch[
	Replace[Function[statement, ruleMatch[fullName[symbol], statement]] /@ definitionStatements[symbol], {
		{} :> HoldComplete[Function[{Typed[expression, Expressions]}, Typed["none", Option[Expressions]]]],
		matches_List :> Replace[Fold[Function[{rest, match}, Replace[{match, rest}, {HoldComplete[m_], HoldComplete[r_]} :> HoldComplete[MatchSum[m, r]]]], Reverse[matches]], {
			HoldComplete[sum_] :> HoldComplete[Function[{Typed[expression, Expressions]}, MatchFirst[sum]]]
		}]
	}],
	untranslatableRule
]

(* rules written as a term, lhs -> rhs and lhs :> rhs, as Replace takes them: the function from an expression to the
   results of every rule that matches it, in order, the left side of each matched as a whole, head included *)
rulesMatchFunction[rules_List] := Catch[
	Replace[Function[rule, standaloneRuleMatch[rule]] /@ rules, {
		{} :> HoldComplete[Function[{Typed[expression, Expressions]}, Typed[{}, Match[Expressions]]]],
		matches_List :> Replace[sumOf[matches], HoldComplete[sum_] :> HoldComplete[Function[{Typed[expression, Expressions]}, sum]]]
	}],
	untranslatableRule
]

standaloneRuleMatch[HoldComplete[(Rule | RuleDelayed)[lhs_, rhs_]]] := Replace[
	Catch[Block[{$partCount = 0}, patternMatch[HoldComplete[lhs], HoldComplete[expression], $rootEnvironment, ruleFinal[HoldComplete[rhs]]]], untranslatable],
	Except[_HoldComplete] :> Throw[{"Untranslatable", HoldForm[lhs :> rhs]}, untranslatableRule]
]

(* the match of one rule: its left side, a pattern, matched at the expression, then its right side, quoted, as one value *)
ruleMatch[_String, HoldComplete[SetDelayed[Verbatim[HoldPattern][lhs_], rhs_]]] := Replace[
	Catch[Block[{$partCount = 0}, topMatch[HoldComplete[lhs], ruleFinal[HoldComplete[rhs]]]], untranslatable],
	Except[_HoldComplete] :> Throw[{"Untranslatable", HoldForm[lhs := rhs]}, untranslatableRule]
]

(* a right side lhs := value /; test is the value where the test is True *)
ruleFinal[HoldComplete[Verbatim[Condition][value_, test_]]] := Function[environment,
	conditioned[valuesOf[quoted[HoldComplete[value], environment]], truthTest[HoldComplete[test], environment]]
]
ruleFinal[value_HoldComplete] := Function[environment, valuesOf[quoted[value, environment]]]

valuesOf[HoldComplete[e_]] := HoldComplete[MatchValue[e]]

(* the names bound so far and the variables of the parts matched, each {HoldComplete[variable], kind}, kind "Expression"
   or "Sequence"; the expression the rules are applied to is the variable expression *)
$rootEnvironment = <|"Names" -> <||>, "Locals" -> <|"expression" -> {HoldComplete[expression], "Expression"}|>|>

$partCount = 0

freshVariable[name_String] := ToExpression[Context[expression] <> name <> ToString[++$partCount], InputForm, HoldComplete]

withLocal[environment_, HoldComplete[variable_], kind_String] := Join[environment, <|"Locals" -> Append[environment["Locals"], ToString[Unevaluated[variable], InputForm] -> {HoldComplete[variable], kind}]|>]
withName[environment_, name_String, binding : {HoldComplete[variable_], kind_String}] := withLocal[Join[environment, <|"Names" -> Append[environment["Names"], name -> binding]|>], HoldComplete[variable], kind]

SetAttributes[heldList, HoldAllComplete]
heldList[elements___] := HoldComplete /@ Unevaluated[{elements}]


(* ::Subsection:: *)
(*Patterns*)


(* The match of a pattern at an expression, a variable of type Expressions, continued by a function of the environment,
   which gives the match of what follows. A pattern that matches in several ways has a MatchSum of its ways, in the order
   the Wolfram Language tries them: the splits of a sequence, shortest first, the permutations of the arguments of an
   Orderless head, and an Optional argument given before it is left out. *)

(* the left side of a rule of f is f[...], whose head need not be tested *)
topMatch[HoldComplete[head_Symbol[arguments___]], final_] := argumentsMatch[HoldComplete[expression], HoldComplete[head], heldList[arguments], $rootEnvironment, final]

patternMatch[HoldComplete[Verbatim[HoldPattern][p_]], v_, environment_, k_] := patternMatch[HoldComplete[p], v, environment, k]
patternMatch[HoldComplete[Verbatim[Blank][]], _, environment_, k_] := k[environment]
patternMatch[HoldComplete[Verbatim[Blank][head_]], v_, environment_, k_] := conditioned[k[environment], sameTest[headOf[v], headAtom[HoldComplete[head], environment]]]
patternMatch[HoldComplete[Verbatim[Pattern][x_Symbol, p_]], v_, environment_, k_] := With[{name = fullName[x]}, Replace[environment["Names"][name], {
	{bound_HoldComplete, "Expression"} :> patternMatch[HoldComplete[p], v, environment, Function[inner, conditioned[k[inner], sameTest[v, bound]]]],
	{_, "Sequence"} :> Throw[None, untranslatable],
	_Missing :> patternMatch[HoldComplete[p], v, withName[environment, name, {v, "Expression"}], k]
}]]
patternMatch[HoldComplete[Verbatim[Condition][p_, c_]], v_, environment_, k_] :=
	patternMatch[HoldComplete[p], v, environment, Function[inner, conditioned[k[inner], truthTest[HoldComplete[c], inner]]]]
patternMatch[HoldComplete[Verbatim[PatternTest][p_, test_]], v_, environment_, k_] :=
	patternMatch[HoldComplete[p], v, environment, Function[inner, conditioned[k[inner], truthTest[applied[HoldComplete[test], v], inner]]]]
patternMatch[HoldComplete[Verbatim[Alternatives][alternatives__]], v_, environment_, k_] :=
	sumOf[Function[alternative, patternMatch[alternative, v, environment, k]] /@ heldList[alternatives]]
patternMatch[HoldComplete[Verbatim[Except][c_]], v_, environment_, k_] := conditioned[k[environment], notTest[matchTest[patternMatch[HoldComplete[c], v, environment, Function[inner, valuesOf[v]]]]]]
patternMatch[HoldComplete[Verbatim[Except][c_, p_]], v_, environment_, k_] :=
	conditioned[patternMatch[HoldComplete[p], v, environment, k], notTest[matchTest[patternMatch[HoldComplete[c], v, environment, Function[inner, valuesOf[v]]]]]]
patternMatch[HoldComplete[Verbatim[Verbatim][e_]], v_, environment_, k_] := conditioned[k[environment], sameTest[v, quoted[HoldComplete[e], environment]]]
patternMatch[HoldComplete[(Verbatim[Optional] | Verbatim[Longest] | Verbatim[Shortest] | Verbatim[PatternSequence])[p_, ___]], v_, environment_, k_] := patternMatch[HoldComplete[p], v, environment, k]
(* any other pattern: an expression without a pattern in it is matched by itself, and a normal expression h[a, ...] by
   its head, a symbol tested at once, then its arguments *)
patternMatch[held : HoldComplete[p_], v_, environment_, k_] := Which[
	sequencePatternQ[held] || ! FreeQ[Unevaluated[p], _KeyValuePattern],
		Throw[None, untranslatable],
	literalQ[held],
		conditioned[k[environment], sameTest[v, quoted[held, environment]]],
	MatchQ[held, HoldComplete[_Symbol[___]]],
		Replace[held, HoldComplete[head_[arguments___]] :>
			argumentsMatch[v, HoldComplete[head], heldList[arguments], environment, k, sameTest[headOf[v], headAtom[HoldComplete[head], environment]]]],
	MatchQ[held, HoldComplete[_[___]]],
		Replace[held, HoldComplete[head_[arguments___]] :> With[{variable = partVariable[HoldComplete[head], environment, "head"]},
			partTerm[v, 0, variable, patternMatch[HoldComplete[head], variable, withLocal[environment, variable, "Expression"], Function[inner, argumentsMatch[v, None, heldList[arguments], inner, k]]]]
		]],
	True,
		Throw[None, untranslatable]
]

(* the arguments of the expression v against the patterns: a fixed number of them, parts at positions, or a list with
   sequences matched by its splits; the arguments of an Orderless head in every order *)
argumentsMatch[v_, head_, patterns_List, environment_, k_] := argumentsMatch[v, head, patterns, environment, k, None]
argumentsMatch[v_, head_, patterns0_List, environment_, k_, headTest_] := With[{patterns = defaultsFilled[head, patterns0], attributes = headAttributes[head]},
	Which[
		MemberQ[attributes, Orderless],
			With[{permuted = freshVariable["arguments"]},
				conditioned[
					bindTerm[Replace[v, HoldComplete[e_] :> HoldComplete["permutations"[Arguments[e]]]], permuted, HoldComplete[{Expressions}],
						listMatch[patterns, permuted, withLocal[environment, permuted, "Sequence"], k, flatHead[head, attributes]]],
					andTests[notAtom[v], headTest]
				]
			],
		fixedArgumentsQ[patterns] && ! MemberQ[attributes, Flat],
			fixedArguments[v, patterns, environment, k, headTest],
		True,
			conditioned[listMatch[patterns, Replace[v, HoldComplete[e_] :> HoldComplete[Arguments[e]]], environment, k, flatHead[head, attributes]], andTests[notAtom[v], headTest]]
	]
]

notAtom[HoldComplete[e_]] := HoldComplete[Not[AtomQ[e]]]
andTests[test_, None] := test
andTests[HoldComplete[a_], HoldComplete[b_]] := HoldComplete[And[a, b]]

headAttributes[HoldComplete[head_Symbol]] := Attributes[head]
headAttributes[_] := {}
flatHead[HoldComplete[head_Symbol], attributes_] /; MemberQ[attributes, Flat] := HoldComplete[head]
flatHead[_, _] := None

(* x_. takes the default of its head at its position, Default[f, i, n], Default[f, i] or Default[f] *)
defaultsFilled[head_, patterns_List] := MapIndexed[Function[{pattern, position}, Replace[pattern, {
	HoldComplete[Verbatim[Optional][p_]] :> Replace[defaultValue[head, First[position], Length[patterns]], {HoldComplete[d_] :> HoldComplete[Optional[p, d]], None :> HoldComplete[Optional[p]]}],
	other_ :> other
}]], patterns]
defaultValue[HoldComplete[head_Symbol], i_Integer, n_Integer] := Replace[
	Select[{HoldComplete @@ {Default[head, i, n]}, HoldComplete @@ {Default[head, i]}, HoldComplete @@ {Default[head]}}, FreeQ[#, Default] &],
	{{d_, ___} :> d, {} :> None}
]
defaultValue[_, _, _] := None

(* a pattern that takes a sequence of arguments, and one that takes a run of them in one way, which a fixed number of
   arguments around it leaves no choice for *)
sequencePatternQ[HoldComplete[Verbatim[Pattern][_Symbol, p_]]] := sequencePatternQ[HoldComplete[p]]
sequencePatternQ[HoldComplete[(Verbatim[Condition] | Verbatim[HoldPattern] | Verbatim[Longest] | Verbatim[Shortest])[p_, ___]]] := sequencePatternQ[HoldComplete[p]]
sequencePatternQ[HoldComplete[_BlankSequence | _BlankNullSequence | _Repeated | _RepeatedNull | _PatternSequence | _OrderlessPatternSequence | _OptionsPattern]] := True
sequencePatternQ[HoldComplete[Verbatim[Alternatives][alternatives__]]] := AnyTrue[heldList[alternatives], sequencePatternQ]
sequencePatternQ[_] := False

simpleSequenceQ[HoldComplete[Verbatim[Pattern][_Symbol, p_]]] := simpleSequenceQ[HoldComplete[p]]
simpleSequenceQ[HoldComplete[(Verbatim[HoldPattern] | Verbatim[Longest] | Verbatim[Shortest])[p_]]] := simpleSequenceQ[HoldComplete[p]]
simpleSequenceQ[HoldComplete[_BlankSequence | _BlankNullSequence | _OptionsPattern]] := True
simpleSequenceQ[HoldComplete[(Verbatim[Repeated] | Verbatim[RepeatedNull])[p_, ___]]] := FreeQ[Unevaluated[p], _Pattern]
simpleSequenceQ[HoldComplete[Verbatim[Pattern][_Symbol, (Verbatim[Repeated] | Verbatim[RepeatedNull])[p_, ___]]]] := FreeQ[Unevaluated[p], _Pattern]
simpleSequenceQ[_] := False

fixedArgumentsQ[patterns_List] := With[{sequences = Select[patterns, sequencePatternQ]},
	sequences === {} || (Length[sequences] == 1 && simpleSequenceQ[First[sequences]] && FreeQ[patterns, HoldComplete[_Optional]])
] && FreeQ[patterns, HoldComplete[_Optional]]

literalQ[HoldComplete[p_]] := FreeQ[Unevaluated[p],
	_Pattern | _Blank | _BlankSequence | _BlankNullSequence | _Alternatives | _Condition | _PatternTest | _Except | _Optional |
	_Repeated | _RepeatedNull | _PatternSequence | _OrderlessPatternSequence | _Longest | _Shortest | _Verbatim | _HoldPattern |
	_KeyValuePattern | _OptionsPattern
]

(* a fixed number of arguments, each at its position, or with one sequence among them, the arguments between those
   before it and those after *)
fixedArguments[v_, patterns_List, environment_, k_, headTest_] := With[
	{n = Length[patterns], s = FirstPosition[patterns, _?sequencePatternQ, {None}, {1}][[1]]},
	If[ s === None,
		conditioned[partsMatch[v, patterns, Range[n], environment, k], andTests[lengthTest[v, lengthEquals[n]], headTest]],
		conditioned[
			partsMatch[v, Delete[patterns, s], Join[Range[s - 1], Range[s - n, -1]], environment,
				Function[inner, sequenceMatch[lengthChecked[patterns[[s]]], Evaluate[sequenceTerm[v, s, n - s]], inner, k]]],
			andTests[lengthTest[v, lengthAtLeast[n - 1 + minimumLength[patterns[[s]]]]], headTest]
		]
	]
]

(* the sequence among fixed arguments, whose least length the length of the arguments checks already *)
lengthChecked[held_HoldComplete] := Replace[held, {Verbatim[BlankSequence][h___] :> BlankNullSequence[h], Verbatim[Repeated][q_] :> RepeatedNull[q]}, {1, 2}]

lengthEquals[n_Integer] := Function[e, HoldComplete[Decide[Length[Arguments[e]] == n]], HoldAllComplete]
lengthAtLeast[0] := Function[e, HoldComplete[True], HoldAllComplete]
lengthAtLeast[n_Integer] := Function[e, HoldComplete[Decide[n <= Length[Arguments[e]]]], HoldAllComplete]

minimumLength[HoldComplete[(Verbatim[Pattern] | Verbatim[HoldPattern] | Verbatim[Longest] | Verbatim[Shortest])[___, p_]]] := minimumLength[HoldComplete[p]]
minimumLength[HoldComplete[_BlankSequence | _Repeated]] := 1
minimumLength[_] := 0

(* the parts at the positions, a negative position counted from the end, each matched by its pattern in turn *)
partsMatch[_, {}, {}, environment_, k_] := k[environment]
partsMatch[v_, {pattern_, patterns___}, {position_, positions___}, environment_, k_] := With[{variable = partVariable[pattern, environment, "part"]},
	partTerm[v, position, variable, patternMatch[pattern, variable, withLocal[environment, variable, "Expression"], Function[inner, partsMatch[v, {patterns}, {positions}, inner, k]]]]
]

(* the variable of a part: the name of the pattern that binds it, where that name is free, or a new one *)
partVariable[HoldComplete[(Verbatim[Pattern])[x_Symbol, _]], environment_, _] /; ! KeyExistsQ[environment["Names"], fullName[x]] := HoldComplete[x]
partVariable[HoldComplete[(Verbatim[Condition] | Verbatim[PatternTest] | Verbatim[HoldPattern])[p_, ___]], environment_, base_] := partVariable[HoldComplete[p], environment, base]
partVariable[_, _, base_String] := freshVariable[base]

partTerm[HoldComplete[v_], k_Integer, HoldComplete[variable_], HoldComplete[body_]] /; k >= 0 := HoldComplete[MatchPart[v, k, Function[{Typed[variable, Expressions]}, body]]]
partTerm[HoldComplete[v_], k_Integer, HoldComplete[variable_], HoldComplete[body_]] := With[{index = -k - 1},
	HoldComplete[MatchBind["matchElement"[Reverse[Arguments[v]], index], Function[{Typed[variable, Expressions]}, body]]]
]

bindTerm[HoldComplete[m_], HoldComplete[variable_], HoldComplete[type_], HoldComplete[body_]] := HoldComplete[MatchBind[m, Function[{Typed[variable, type]}, body]]]


(* ::Subsection:: *)
(*Sequences of arguments*)


(* the patterns against a list of expressions, each taking its arguments in turn, the list used up at the end *)
listMatch[{}, HoldComplete[l_], environment_, k_, _] := conditioned[k[environment], HoldComplete[Decide[Length[l] == 0]]]
listMatch[{HoldComplete[Verbatim[PatternSequence][elements___]], rest___}, l_, environment_, k_, flat_] := listMatch[Join[heldList[elements], {rest}], l, environment, k, flat]
listMatch[{HoldComplete[Verbatim[HoldPattern][p_]], rest___}, l_, environment_, k_, flat_] := listMatch[{HoldComplete[p], rest}, l, environment, k, flat]
listMatch[{pattern_HoldComplete, rest___}, l_, environment_, k_, flat_] :=
	elementMatch[pattern, l, environment, Function[{inner, remaining}, listMatch[{rest}, remaining, inner, k, flat]], flat]

(* the arguments one pattern takes from the front of a list: k[environment, the rest of the list] *)
elementMatch[HoldComplete[Verbatim[Condition][p_, c_]], l_, environment_, k_, flat_] :=
	elementMatch[HoldComplete[p], l, environment, Function[{inner, remaining}, conditioned[k[inner, remaining], truthTest[HoldComplete[c], inner]]], flat]
elementMatch[HoldComplete[Verbatim[HoldPattern][p_]], l_, environment_, k_, flat_] := elementMatch[HoldComplete[p], l, environment, k, flat]
elementMatch[HoldComplete[Verbatim[Alternatives][alternatives__]], l_, environment_, k_, flat_] /; sequencePatternQ[HoldComplete[Alternatives[alternatives]]] :=
	sumOf[Function[alternative, elementMatch[alternative, l, environment, k, flat]] /@ heldList[alternatives]]
(* an Optional argument is given, or left out for its default *)
elementMatch[HoldComplete[Verbatim[Optional][p_, d_]], l_, environment_, k_, flat_] := sumOf[{
	elementMatch[HoldComplete[p], l, environment, k, flat],
	defaultMatch[HoldComplete[p], HoldComplete[d], environment, Function[inner, k[inner, l]]]
}]
(* x_. of a head without a default must be given *)
elementMatch[HoldComplete[Verbatim[Optional][p_]], l_, environment_, k_, flat_] := elementMatch[HoldComplete[p], l, environment, k, flat]
elementMatch[HoldComplete[Verbatim[Longest][p_]], l_, environment_, k_, _] := splitMatch[HoldComplete[p], l, environment, k, "longestSplits"]
elementMatch[HoldComplete[Verbatim[Shortest][p_]], l_, environment_, k_, _] := splitMatch[HoldComplete[p], l, environment, k, "splits"]
elementMatch[pattern_HoldComplete, l_, environment_, k_, flat_] := If[sequencePatternQ[pattern], splitMatch[pattern, l, environment, k, "splits"], singleMatch[pattern, l, environment, k, flat]]

(* one argument, the first of the list; under a Flat head, also a run of two or more wrapped in it *)
singleMatch[pattern_HoldComplete, HoldComplete[l_], environment_, k_, flat_] := With[{variable = partVariable[pattern, environment, "part"]},
	sumOf[{
		bindTerm[HoldComplete["matchElement"[l, 0]], variable, HoldComplete[Expressions],
			patternMatch[pattern, variable, withLocal[environment, variable, "Expression"], Function[inner, k[inner, HoldComplete[Drop[l, 1]]]]]],
		If[flat === None, Nothing, flatRunMatch[pattern, HoldComplete[l], environment, k, flat]]
	}]
]

flatRunMatch[pattern_, HoldComplete[l_], environment_, k_, HoldComplete[head_]] := With[{pair = freshVariable["split"], run = freshVariable["run"]},
	bindTerm[HoldComplete["splits"[l]], pair, HoldComplete[CartesianProductType[{Expressions}, {Expressions}]],
		Replace[pair, HoldComplete[p_] :> conditioned[
			bindTerm[HoldComplete[MatchValue["normal"[HoldForm[head], p[[1]]]]], run, HoldComplete[Expressions],
				patternMatch[pattern, run, withLocal[environment, run, "Expression"], Function[inner, k[inner, HoldComplete[p[[2]]]]]]],
			HoldComplete[Decide[2 <= Length[p[[1]]]]]
		]]
	]
]

(* the default of a pattern left out: its name, if it has one, bound to the default *)
defaultMatch[HoldComplete[(Verbatim[Condition] | Verbatim[PatternTest] | Verbatim[HoldPattern])[p_, ___]], d_, environment_, k_] := defaultMatch[HoldComplete[p], d, environment, k]
defaultMatch[HoldComplete[Verbatim[Pattern][x_Symbol, _]], HoldComplete[d_], environment_, k_] := With[{name = fullName[x]},
	bindTerm[valuesOf[quoted[HoldComplete[d], environment]], HoldComplete[x], HoldComplete[Expressions], k[withName[environment, name, {HoldComplete[x], "Expression"}]]]
]
defaultMatch[_, _, environment_, k_] := k[environment]

(* a sequence pattern takes a prefix of the list, every split tried in order *)
splitMatch[pattern_, HoldComplete[l_], environment_, k_, splits_String] := With[{pair = freshVariable["split"]},
	bindTerm[HoldComplete[splits[l]], pair, HoldComplete[CartesianProductType[{Expressions}, {Expressions}]],
		Replace[pair, HoldComplete[p_] :> sequenceMatch[pattern, HoldComplete[p[[1]]], withLocal[environment, pair, "Pair"], Function[inner, k[inner, HoldComplete[p[[2]]]]]]]
	]
]

(* a sequence pattern against the whole of a list *)
sequenceMatch[HoldComplete[Verbatim[Pattern][x_Symbol, p_]], s_, environment_, k_] := With[{name = fullName[x]},
	If[KeyExistsQ[environment["Names"], name], Throw[None, untranslatable]];
	sequenceMatch[HoldComplete[p], s, environment, Function[inner,
		bindTerm[Replace[s, HoldComplete[e_] :> HoldComplete[MatchValue[Typed[e, {Expressions}]]]], HoldComplete[x], HoldComplete[{Expressions}],
			k[withName[inner, name, {HoldComplete[x], "Sequence"}]]]
	]]
]
sequenceMatch[HoldComplete[Verbatim[Condition][p_, c_]], s_, environment_, k_] := sequenceMatch[HoldComplete[p], s, environment, Function[inner, conditioned[k[inner], truthTest[HoldComplete[c], inner]]]]
sequenceMatch[HoldComplete[(Verbatim[HoldPattern] | Verbatim[Longest] | Verbatim[Shortest])[p_]], s_, environment_, k_] := sequenceMatch[HoldComplete[p], s, environment, k]
sequenceMatch[HoldComplete[Verbatim[BlankSequence][]], s_, environment_, k_] := conditioned[k[environment], lengthOfAtLeast[s, 1]]
sequenceMatch[HoldComplete[Verbatim[BlankSequence][head_]], s_, environment_, k_] :=
	conditioned[k[environment], andTests[lengthOfAtLeast[s, 1], everyHead[s, headAtom[HoldComplete[head], environment], True]]]
sequenceMatch[HoldComplete[Verbatim[BlankNullSequence][]], _, environment_, k_] := k[environment]
sequenceMatch[HoldComplete[Verbatim[BlankNullSequence][head_]], s_, environment_, k_] := conditioned[k[environment], everyHead[s, headAtom[HoldComplete[head], environment], True]]
(* a repeated pattern that binds names binds them at its first repetition, and every other must bind the same *)
sequenceMatch[HoldComplete[(Verbatim[Repeated] | Verbatim[RepeatedNull])[p_, spec___]], HoldComplete[s_], environment_, k_] /; ! FreeQ[Unevaluated[p], _Pattern] :=
	With[{first = freshVariable["first"]},
		conditioned[
			bindTerm[HoldComplete["matchElement"[s, 0]], first, HoldComplete[Expressions],
				patternMatch[HoldComplete[p], first, withLocal[environment, first, "Expression"], Function[inner, conditioned[k[inner], everyMatch[HoldComplete[p], HoldComplete[Drop[s, 1]], inner]]]]],
			repetitionsTest[HoldComplete[s], {spec}, 1]
		]
	]
sequenceMatch[HoldComplete[Verbatim[Repeated][p_, spec___]], s_, environment_, k_] := conditioned[k[environment], andTests[repetitionsTest[s, {spec}, 1], everyMatch[HoldComplete[p], s, environment]]]
sequenceMatch[HoldComplete[Verbatim[RepeatedNull][p_, spec___]], s_, environment_, k_] := conditioned[k[environment], andTests[repetitionsTest[s, {spec}, 0], everyMatch[HoldComplete[p], s, environment]]]
sequenceMatch[HoldComplete[Verbatim[OptionsPattern][___]], s_, environment_, k_] := conditioned[k[environment], everyMatch[HoldComplete[_Rule | _RuleDelayed | _List], s, environment]]
sequenceMatch[HoldComplete[Verbatim[PatternSequence][elements___]], s_, environment_, k_] := listMatch[heldList[elements], s, environment, k, None]
sequenceMatch[HoldComplete[Verbatim[OrderlessPatternSequence][elements___]], HoldComplete[s_], environment_, k_] := With[{permuted = freshVariable["arguments"]},
	bindTerm[HoldComplete["permutations"[s]], permuted, HoldComplete[{Expressions}], listMatch[heldList[elements], permuted, withLocal[environment, permuted, "Sequence"], k, None]]
]
sequenceMatch[HoldComplete[Verbatim[Alternatives][alternatives__]], s_, environment_, k_] := sumOf[Function[alternative, sequenceMatch[alternative, s, environment, k]] /@ heldList[alternatives]]
(* a pattern of one expression as a sequence takes exactly one *)
sequenceMatch[pattern_HoldComplete, s_, environment_, k_] := listMatch[{pattern}, s, environment, k, None]

lengthOfAtLeast[HoldComplete[s_], n_Integer] := HoldComplete[Decide[n <= Length[s]]]
repetitionsTest[s_, {}, minimum_] := If[minimum == 0, None, lengthOfAtLeast[s, minimum]]
repetitionsTest[HoldComplete[s_], {max_Integer}, minimum_] := HoldComplete[Decide[minimum <= Length[s] && Length[s] <= max]]
repetitionsTest[HoldComplete[s_], {{n_Integer}}, _] := HoldComplete[Decide[Length[s] == n]]
repetitionsTest[HoldComplete[s_], {{min_Integer, max_Integer}}, _] := HoldComplete[Decide[min <= Length[s] && Length[s] <= max]]
repetitionsTest[HoldComplete[s_], {{min_Integer, Infinity}}, _] := HoldComplete[Decide[min <= Length[s]]]
repetitionsTest[_, _, _] := Throw[None, untranslatable]

andTests[None, test_] := test

(* whether every expression of a list matches a pattern whose names are bound already *)
everyMatch[HoldComplete[p_], HoldComplete[s_], environment_] := With[{first = freshVariable["element"], others = freshVariable["others"], result = freshVariable["result"]},
	If[! SubsetQ[Keys[environment["Names"]], Cases[Unevaluated[p], Verbatim[Pattern][x_Symbol, _] :> fullName[x], {0, Infinity}]], Throw[None, untranslatable]];
	Replace[{first, others, result, matchTest[patternMatch[HoldComplete[p], first, withLocal[environment, first, "Expression"], Function[inner, valuesOf[first]]]]}, {
		{HoldComplete[f_], HoldComplete[o_], HoldComplete[r_], HoldComplete[t_]} :> HoldComplete[InductiveRecursor[List][
			Function[{Typed[list, {Expressions}]}, Booleans], True, Function[{Typed[f, Expressions], Typed[o, {Expressions}], Typed[r, Booleans]}, And[t, r]], s
		]]
	}]
]


(* ::Subsection:: *)
(*Terms*)


sumOf[{m_HoldComplete}] := m
sumOf[{HoldComplete[a_], rest__}] := Replace[sumOf[{rest}], HoldComplete[b_] :> HoldComplete[MatchSum[a, b]]]

conditioned[HoldComplete[m_], HoldComplete[b_]] := HoldComplete[Condition[m, b]]
conditioned[m_HoldComplete, None] := m
sameTest[HoldComplete[a_], HoldComplete[b_]] := HoldComplete[SameQ[a, b]]
matchTest[HoldComplete[m_]] := HoldComplete[MatchQ[m]]
notTest[HoldComplete[t_]] := HoldComplete[Not[t]]
headOf[HoldComplete[e_]] := HoldComplete[Head[e]]

(* a condition or a test as the expression it evaluates, quoted, whose value must be True *)
truthTest[test_HoldComplete, environment_] := sameTest[Replace[quoted[test, environment], HoldComplete[e_] :> HoldComplete[ExpressionValue[e]]], atomTerm["System`True"]]
applied[HoldComplete[f_], HoldComplete[v_]] := HoldComplete[f[v]]

(* the head of a pattern, an atom: a symbol by its full name *)
headAtom[HoldComplete[head_Symbol], _] := atomTerm[fullName[head]]
headAtom[head_HoldComplete, environment_] := quoted[head, environment]

(* a normal expression whose length passes the test *)
lengthTest[HoldComplete[e_], test_] := Replace[test[e], {HoldComplete[True] :> HoldComplete[Not[AtomQ[e]]], HoldComplete[t_] :> HoldComplete[And[Not[AtomQ[e]], t]]}]

(* the arguments of a part from the from-th to the after-th from the end, exclusive *)
sequenceTerm[HoldComplete[e_], 1, 0] := HoldComplete[Arguments[e]]
sequenceTerm[HoldComplete[e_], from_Integer, 0] := With[{dropped = from - 1}, HoldComplete[Drop[Arguments[e], dropped]]]
sequenceTerm[HoldComplete[e_], from_Integer, after_Integer] := With[{dropped = from - 1}, HoldComplete[Reverse[Drop[Reverse[Drop[Arguments[e], dropped]], after]]]]

(* whether every expression of a sequence has the head, or none has *)
everyHead[HoldComplete[s_], HoldComplete[head_], True] := HoldComplete[InductiveRecursor[List][
	Function[{Typed[list, {Expressions}]}, Booleans], True, Function[{Typed[first, Expressions], Typed[others, {Expressions}], Typed[result, Booleans]}, And[SameQ[Head[first], head], result]], s
]]


(* ::Subsection:: *)
(*Quoting*)


(* an expression as a term of type Expressions, HoldForm[e], which elaboration quotes: its pattern variables the parts
   they match, a sequence variable alone the expression Sequence[...] of its expressions, and every symbol and atom but a
   natural number an axiom, declared with the rules *)
quoted[HoldComplete[e_Symbol], environment_] /; MatchQ[environment["Names"][fullName[e]], {_, "Sequence"}] :=
	quoted[HoldComplete[Sequence[e]], environment]
quoted[held_HoldComplete, environment_] := Replace[renamed[held, environment], renamedHeld : HoldComplete[e_] :> (
	declareAtoms[renamedHeld, environment];
	HoldComplete[HoldForm[e]]
)]

(* each pattern variable as the variable of the part it matches *)
renamed[held_HoldComplete, environment_] := ReplaceAll[held, KeyValueMap[
	Function[{name, binding}, Replace[{ToExpression[name, InputForm, HoldComplete], First[binding]}, {HoldComplete[source_], HoldComplete[variable_]} :> (HoldPattern[source] :> variable)]],
	environment["Names"]
]]

(* the atoms of a quotation are data of the type Atoms, a symbol by its name, which nothing needs to declare *)
declareAtoms[_, _] := Null

(* the atom of a symbol, by its full name, quoted *)
atomTerm[name_String] := ToExpression[name, InputForm, Function[symbol, HoldComplete[HoldForm[symbol]], HoldAllComplete]]
