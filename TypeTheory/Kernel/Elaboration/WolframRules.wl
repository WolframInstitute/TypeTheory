(* ::Package:: *)

(*
WolframRules: the rules of a Wolfram Language symbol as a term of TypeTheoryEnvironment["WolframLanguage"], what
TypeTheoryFormalize[f, "Meaning" -> "Rules"] declares.

The rules of f, its DownValues, are a definition of type Expressions -> Option[Expressions]: the expression f[...]
rewrites to by the first rule that matches it, OptionNone where none does and the expression stays as it is. It is

	Function[{Typed[expression, Expressions]}, MatchFirst[MatchSum[rule1, MatchSum[rule2, ...]]]]

each rule a Match of the expressions its right side gives, quoted, its pattern variables the parts they match. The
left side of each rule is read from its match program, which the compiler's ToCore writes, one instruction at a time:

	Length[p, n], MinLength[p, n]     Condition on the Length of the Arguments of the part at p, a normal expression
	HeadIs[p, name]                    Condition on SameQ of its Head and the atom name
	Same[p, e]                         Condition on SameQ of it and e, quoted
	Bind[name, local, p]               the part, by MatchPart, bound to the pattern variable
	Join[local, p]                     Condition on SameQ of the part and the local: a repeated name
	BindSequence, Sequence, SequenceNot   the arguments from one position to another, by Drop, bound or tested
	AnyOf, NoneOf                      Condition on MatchQ of the matches of the alternatives
	Guard[core]                        Condition on SameQ of the ExpressionValue of core, quoted, and True

A part is matched once, the first time an instruction needs it, and named by the pattern variable that binds it. A
pattern that needs a search, which the compiler leaves to the evaluator as a Match`Kernel, does not translate yet.
Every symbol and every atom but a natural number is an axiom of type Atoms, named by its full name or its InputForm,
declared where a rule uses it. The right side is quoted as it is: the rules give one step of evaluation, and the
Wolfram Language evaluates the result further.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[rulesDeclarations]


(* ::Section:: *)
(*Usage Messages*)


rulesDeclarations::usage = "rulesDeclarations[environment, HoldComplete[symbol]] gives the declarations of the rules of symbol: the atoms they use, then the definition of type Expressions -> Option[Expressions] named \"DownValues[symbol]\"."


(* ::Section:: *)
(*Function Definitions*)


rulesDeclarations[environment_, held : HoldComplete[symbol_Symbol]] := Which[
	! constantDeclaredQ[environment, HoldComplete[MatchFirst]],
		kernelFailure["RulesEnvironment", "The rules of `1` are terms of TypeTheoryEnvironment[\"WolframLanguage\"], which has Expressions and MatchFirst.", {HoldForm[symbol]}],
	! TrueQ[loadKernelCompiler[]],
		kernelFailure["KernelCompilerMissing", "Reading the rules of `1` needs the paclet Wolfram/KernelCompiler.", {HoldForm[symbol]}],
	True,
		Replace[Reap[translatedRules[held], atomDeclaration], {
			{value_HoldComplete, atoms_} :> With[{declarations = Append[missingDeclarations[environment, DeleteDuplicates[Catenate[Catenate[atoms]]]], rulesDefinition[held, value]]},
				If[ FailureQ[Quiet[TypeTheoryEnvironment[environment, declarations]]],
					kernelFailure["Unformalizable", "The rules of `1` translate to a term that does not check.", {HoldForm[symbol]}],
					declarations
				]
			],
			{{"Untranslatable", rule_}, _} :> kernelFailure["Untranslatable", "The rule `1` does not translate: its pattern needs a search, or has a part without a counterpart.", {rule}]
		}]
]

(* by the symbol's name, without its context, which is where it was defined and would change the name with it; the atoms
   keep their full names, as two symbols of one name in two contexts are different expressions *)
rulesName[HoldComplete[symbol_Symbol]] := "DownValues[" <> SymbolName[Unevaluated[symbol]] <> "]"

rulesDefinition[held_, HoldComplete[value_]] := With[{name = rulesName[held]}, TypeTheoryDefinition[name, Typed[value, Expressions -> Option[Expressions]]]]

(* the value of the rules, or {"Untranslatable", rule} for the first rule that does not translate *)
translatedRules[HoldComplete[symbol_Symbol]] := Catch[
	Replace[Function[statement, ruleMatch[fullName[symbol], statement]] /@ definitionStatements[symbol], {
		{} :> HoldComplete[Function[{Typed[expression, Expressions]}, Typed[OptionNone, Option[Expressions]]]],
		matches_List :> Replace[Fold[Function[{rest, match}, Replace[{match, rest}, {HoldComplete[m_], HoldComplete[r_]} :> HoldComplete[Wolfram`Patterns`MatchSum[m, r]]]], Reverse[matches]], {
			HoldComplete[sum_] :> HoldComplete[Function[{Typed[expression, Expressions]}, MatchFirst[sum]]]
		}]
	}],
	untranslatableRule
]

(* the match of one rule, its left side lowered by itself, so that its program is its own *)
ruleMatch[name_String, statement : HoldComplete[SetDelayed[HoldPattern[lhs_], rhs_]]] := Replace[
	Cases[Lookup[First[coreNormal[kernelCompilerSymbol["ToCore"][{statement}]]], name, {}], coreForm["Definition"][_, coreForm["Program"][instructions_List], ___] :> instructions],
	{
		{instructions_List} :> Replace[
			Catch[Block[{$partCount = 0, $partNames = partNames[instructions]}, programMatch[instructions, $rootEnvironment, Function[environment, valuesOf[quoted[ruleValue[HoldComplete[rhs], instructions], environment]]]]], untranslatable],
			Except[_HoldComplete] :> Throw[{"Untranslatable", HoldForm[lhs := rhs]}, untranslatableRule]
		],
		_ :> Throw[{"Untranslatable", HoldForm[lhs := rhs]}, untranslatableRule]
	}
]

(* a right side lhs := value /; test, whose test the program has as its last Guard, is value *)
ruleValue[HoldComplete[Verbatim[Condition][value_, _]], instructions_List] /; MatchQ[Last[instructions, None], coreForm["Guard"][_]] := HoldComplete[value]
ruleValue[HoldComplete[_Condition], _] := Throw[None, untranslatable]
ruleValue[value_HoldComplete, _] := value

valuesOf[HoldComplete[e_]] := HoldComplete[Wolfram`Patterns`MatchValues[e]]

(* the parts matched so far, by path, and the pattern variables and locals bound, each to {HoldComplete[variable], kind},
   kind "Expression" or "Sequence" *)
$rootEnvironment = <|"Parts" -> <|{} -> HoldComplete[expression]|>, "Names" -> <||>, "Locals" -> <||>|>

$partCount = 0

(* the pattern variable that names each part some Bind binds, so that a part a test reaches first has its name too *)
$partNames = <||>

partNames[instructions_List] := Association[Reverse[Cases[instructions, coreForm["Bind"][name_String, _, path_List] :> path -> preferredVariable[name]]]]

freshPart[] := ToExpression[Context[expression] <> "part" <> ToString[++$partCount], InputForm, HoldComplete]


(* ::Subsection:: *)
(*Match programs*)


(* the match of the instructions, ending in the match final gives for the environment they leave *)
programMatch[{}, environment_, final_] := final[environment]

programMatch[{coreForm["Length"][path_List, n_Integer], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, conditioned[programMatch[{rest}, inner, final], lengthTest[part, Function[e, HoldComplete[Decide[Length[Arguments[e]] == n]], HoldAllComplete]]]]
]
programMatch[{coreForm["MinLength"][path_List, n_Integer], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, conditioned[programMatch[{rest}, inner, final], lengthTest[part, Function[e, HoldComplete[Decide[n <= Length[Arguments[e]]]], HoldAllComplete]]]]
]
programMatch[{coreForm["HeadIs"][path_List, name_String], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, conditioned[programMatch[{rest}, inner, final], sameTest[headOf[part], atomTerm[name]]]]
]
programMatch[{coreForm["Same"][path_List, literal_HoldComplete], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, conditioned[programMatch[{rest}, inner, final], sameTest[part, quoted[literal, inner]]]]
]
programMatch[{coreForm["Bind"][name_, local_String, path_List], rest___}, environment_, final_] := withPart[path, environment, preferredVariable[name],
	Function[{part, inner}, programMatch[{rest}, bound[inner, name, local, {part, "Expression"}], final]]
]
programMatch[{coreForm["Join"][local_String, path_List], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, conditioned[programMatch[{rest}, inner, final], sameTest[part, localVariable[inner, local]]]]
]
programMatch[{coreForm["BindSequence"][name_, local_String, path_List, from_Integer, after_Integer], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, With[{variable = Replace[preferredVariable[name], None :> freshPart[]]},
		Replace[{sequenceTerm[part, from, after], variable, programMatch[{rest}, bound[inner, name, local, {variable, "Sequence"}], final]}, {
			{HoldComplete[s_], HoldComplete[v_], HoldComplete[m_]} :> HoldComplete[MatchBind[Wolfram`Patterns`MatchValues[Typed[s, {Expressions}]], Function[{Typed[v, {Expressions}]}, m]]]
		}]
	]]
]
programMatch[{coreForm["Sequence"][path_List, from_Integer, after_Integer, name_String], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, conditioned[programMatch[{rest}, inner, final], everyHead[sequenceTerm[part, from, after], atomTerm[name], True]]]
]
programMatch[{coreForm["SequenceNot"][path_List, from_Integer, after_Integer, name_String], rest___}, environment_, final_] := withPart[path, environment, None,
	Function[{part, inner}, conditioned[programMatch[{rest}, inner, final], everyHead[sequenceTerm[part, from, after], atomTerm[name], False]]]
]
programMatch[{coreForm["AnyOf"][alternatives : {__List}], rest___}, environment_, final_] := conditioned[
	programMatch[{rest}, environment, final],
	Fold[
		Function[{either, test}, Replace[{either, test}, {HoldComplete[a_], HoldComplete[b_]} :> HoldComplete[Or[a, b]]]],
		Function[alternative, matchTest[programMatch[alternative, environment, testFinal]]] /@ alternatives
	]
]
programMatch[{coreForm["NoneOf"][instructions_List], rest___}, environment_, final_] := conditioned[
	programMatch[{rest}, environment, final],
	Replace[matchTest[programMatch[instructions, environment, testFinal]], HoldComplete[t_] :> HoldComplete[Not[t]]]
]
programMatch[{coreForm["Guard"][core_], rest___}, environment_, final_] := conditioned[
	programMatch[{rest}, environment, final],
	sameTest[Replace[quotedCore[core, environment], HoldComplete[e_] :> HoldComplete[ExpressionValue[e]]], atomTerm["System`True"]]
]
programMatch[_, _, _] := Throw[None, untranslatable]

(* the match of a test, which binds nothing *)
testFinal[_] := HoldComplete[Wolfram`Patterns`MatchValues[expression]]

conditioned[HoldComplete[m_], HoldComplete[b_]] := HoldComplete[Condition[m, b]]
sameTest[HoldComplete[a_], HoldComplete[b_]] := HoldComplete[SameQ[a, b]]
matchTest[HoldComplete[m_]] := HoldComplete[MatchQ[m]]
headOf[HoldComplete[e_]] := HoldComplete[Head[e]]

(* a normal expression whose length passes the test *)
lengthTest[HoldComplete[e_], test_] := Replace[test[e], HoldComplete[t_] :> HoldComplete[And[Not[AtomQ[e]], t]]]

(* the arguments of a part from the from-th to the after-th from the end, exclusive *)
sequenceTerm[HoldComplete[e_], 1, 0] := HoldComplete[Arguments[e]]
sequenceTerm[HoldComplete[e_], from_Integer, 0] := With[{dropped = from - 1}, HoldComplete[Drop[Arguments[e], dropped]]]
sequenceTerm[HoldComplete[e_], from_Integer, after_Integer] := With[{dropped = from - 1}, HoldComplete[Reverse[Drop[Reverse[Drop[Arguments[e], dropped]], after]]]]

(* whether every expression of a sequence has the head, or none has *)
everyHead[HoldComplete[s_], HoldComplete[head_], True] := HoldComplete[InductiveRecursor[List][
	Function[{Typed[list, {Expressions}]}, Booleans], True, Function[{Typed[others, {Expressions}], Typed[first, Expressions], Typed[result, Booleans]}, And[SameQ[Head[first], head], result]], s
]]
everyHead[HoldComplete[s_], HoldComplete[head_], False] := HoldComplete[InductiveRecursor[List][
	Function[{Typed[list, {Expressions}]}, Booleans], True, Function[{Typed[others, {Expressions}], Typed[first, Expressions], Typed[result, Booleans]}, And[Not[SameQ[Head[first], head]], result]], s
]]

(* the part at a path, matched where no instruction has yet, its variable the pattern variable that binds it where one
   does: continuation[HoldComplete[variable], environment] inside the matches of the parts on the way; no rule here
   names a pattern part or inner, the parameters of the continuations, which a rule's right side would replace *)
withPart[path_List, environment_, preferred_, continuation_] := Replace[environment["Parts"][path], {
	matched_HoldComplete :> continuation[matched, environment],
	_Missing :> withPart[Most[path], environment, None, Function[{parent, parentEnvironment}, With[{variable = Replace[preferred, None :> Replace[Lookup[$partNames, Key[path], None], None :> freshPart[]]]},
		Replace[{parent, variable, continuation[variable, Join[parentEnvironment, <|"Parts" -> Append[parentEnvironment["Parts"], path -> variable]|>]]}, {
			{HoldComplete[p_], HoldComplete[v_], HoldComplete[m_]} :> partMatch[p, Evaluate[Last[path]], v, m]
		}]
	]]]
}]

SetAttributes[partMatch, HoldAll]
partMatch[p_, k_Integer, v_, m_] /; k >= 0 := HoldComplete[Wolfram`Patterns`MatchPart[p, k, Function[{Typed[v, Expressions]}, m]]]
partMatch[p_, k_Integer, v_, m_] := With[{index = -k - 1}, HoldComplete[MatchBind["matchElement"[Reverse[Arguments[p]], index], Function[{Typed[v, Expressions]}, m]]]]

preferredVariable[name_String] := ToExpression[name, InputForm, HoldComplete]
preferredVariable[None] := None

bound[environment_, name_, local_String, binding_] := Join[environment, <|
	"Locals" -> Append[environment["Locals"], local -> binding],
	"Names" -> If[StringQ[name], Append[environment["Names"], name -> binding], environment["Names"]]
|>]

localVariable[environment_, local_String] := Replace[environment["Locals"][local], {{variable_, "Expression"} :> variable, _ :> Throw[None, untranslatable]}]


(* ::Subsection:: *)
(*Quoting*)


(* an expression as a term of type Expressions: its pattern variables the parts they match, a natural number by
   naturalAtom, and every other atom an axiom *)
quoted[HoldComplete[e_Symbol], environment_] := Replace[environment["Names"][fullName[e]], {
	{variable_, "Expression"} :> variable,
	{HoldComplete[variable_], "Sequence"} :> Replace[atomTerm["System`Sequence"], HoldComplete[s_] :> HoldComplete[ExpressionNormal[s, variable]]],
	_Missing :> atomTerm[fullName[e]]
}]
quoted[HoldComplete[n_Integer], _] /; n >= 0 := HoldComplete[ExpressionAtom["naturalAtom"[n]]]
quoted[HoldComplete[e : (_String | _Integer | _Real | _Rational | _Complex)], _] := literalAtomTerm[HoldComplete[e]]
quoted[HoldComplete[h_[arguments___]], environment_] := normalTerm[quoted[HoldComplete[h], environment], Function[argument, quotedArgument[argument, environment]] /@ (HoldComplete /@ Unevaluated[{arguments}])]
quoted[_, _] := Throw[None, untranslatable]

(* ExpressionNormal[head, arguments], the arguments a list: the expressions among them in list literals, and each sequence
   variable joined in, as ExpressionNormal[head, Join[{x, y}, z]] for head[x, y, z] *)
normalTerm[HoldComplete[head_], arguments_List] := Replace[argumentList[arguments], HoldComplete[list_] :> HoldComplete[ExpressionNormal[head, list]]]

argumentList[{}] := HoldComplete[Typed[{}, {Expressions}]]
argumentList[arguments_List] := Fold[
	Function[{rest, part}, Replace[{part, rest}, {HoldComplete[p_], HoldComplete[r_]} :> HoldComplete[Join[p, r]]]],
	Reverse[argumentRuns[arguments]]
]

(* the runs of expressions, each a list literal, and the sequence variables, in order *)
argumentRuns[arguments_List] := Catenate[Replace[SplitBy[arguments, First], {
	run : {{"Expression", _}, ___} :> {Replace[Join @@ (Last /@ run), HoldComplete[elements___] :> HoldComplete[{elements}]]},
	run_ :> Last /@ run
}, {1}]]

(* an argument, {"Expression", term} or, for a sequence variable, {"Sequence", variable} *)
quotedArgument[HoldComplete[e_Symbol], environment_] /; MatchQ[environment["Names"][fullName[e]], {_, "Sequence"}] := {"Sequence", First[environment["Names"][fullName[e]]]}
quotedArgument[argument_, environment_] := {"Expression", quoted[argument, environment]}

(* a condition's Core, quoted: its calls normal expressions, its locals the parts they name *)
quotedCore[coreForm["Call"][name_String, arguments_List], environment_] := normalTerm[atomTerm[name], Function[argument, quotedCoreArgument[argument, environment]] /@ arguments]
quotedCore[coreForm["Local"][local_String], environment_] := localVariable[environment, local]
quotedCore[coreForm["Constant"][HoldComplete[c_]], environment_] := quoted[HoldComplete[c], environment]
quotedCore[coreForm["Constant"][c_], environment_] := quoted[HoldComplete[c], environment]
quotedCore[coreForm["Evaluated"][core_], environment_] := quotedCore[core, environment]
quotedCore[_, _] := Throw[None, untranslatable]

quotedCoreArgument[coreForm["Local"][local_String], environment_] /; MatchQ[environment["Locals"][local], {_, "Sequence"}] := {"Sequence", First[environment["Locals"][local]]}
quotedCoreArgument[core_, environment_] := {"Expression", quotedCore[core, environment]}

(* the atom of a symbol, by its full name, an axiom that the symbol is; and of any other atom, by its InputForm *)
atomTerm[name_String] := (
	Sow[{ToExpression[name, InputForm, Function[symbol, TypeTheoryAxiom[name, Atoms, "Implementation" -> symbol], HoldAllComplete]]}, atomDeclaration];
	HoldComplete[ExpressionAtom[name]]
)
literalAtomTerm[HoldComplete[e_]] := With[{name = ToString[Unevaluated[e], InputForm]},
	Sow[{TypeTheoryAxiom[name, Atoms]}, atomDeclaration];
	HoldComplete[ExpressionAtom[name]]
]
