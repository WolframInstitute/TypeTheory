(* ::Package:: *)

(* Tests for the patterns of Elaboration/WolframRules.wl: the rules of a symbol, translated to matches, give the
   expression the Wolfram Language rewrites to, for every kind of pattern. The kernel computes the structure of a match
   but not SameQ or ExpressionValue, which the Wolfram Language computes, so the translated rules are run here by an
   interpreter of their constants in the Wolfram Language, and compared with Replace by the rules themselves. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

wolfram = TypeTheoryEnvironment["WolframLanguage"]

(* an expression is ex[e], held; a variable of a sequence is a list, spliced where it is quoted; each constant of matches
   is renamed to a function of this file, so that the paclet's symbols get no definitions *)
SetAttributes[{ex, quote, splice}, HoldAllComplete]

interpreted[definition_] := Replace[definition, TypeTheoryDefinition[_, Typed[value_, _]] :> interpretedTerm[HoldComplete[value]]]

$renamed = {
	WolframInstitute`TypeTheory`MatchValue -> mValue, WolframInstitute`TypeTheory`MatchSum -> mSum, WolframInstitute`TypeTheory`MatchBind -> mBind,
	WolframInstitute`TypeTheory`MatchFirst -> mFirst, WolframInstitute`TypeTheory`MatchPart -> mPart, WolframInstitute`TypeTheory`Arguments -> mArguments,
	WolframInstitute`TypeTheory`ExpressionValue -> mValueOf, WolframInstitute`TypeTheory`Decide -> mDecide, Head -> mHead, AtomQ -> mAtomQ,
	Condition -> mCondition, MatchQ -> mMatchQ, SameQ -> mSameQ, InductiveRecursor[List] -> mListRecursion,
	"splits" -> mSplits, "longestSplits" -> mLongestSplits, "permutations" -> mPermutations, "matchElement" -> mElement, "pair" -> List, "normal" -> mNormal
}

interpretedTerm[held_HoldComplete] := ReleaseHold[ReplaceRepeated[held, {
	HoldPattern[Function[{Typed[x_Symbol, {WolframInstitute`TypeTheory`Expressions}]}, body_]] :> RuleCondition[functionOf[x, markedQuotes[HoldComplete[body], x]]],
	HoldPattern[Function[{Typed[x_Symbol, _]}, body_]] :> RuleCondition[functionOf[x, HoldComplete[body]]],
	HoldPattern[Function[binders : {__Typed}, body_]] :> RuleCondition[functionsOf[binders, HoldComplete[body]]],
	HoldPattern[Typed[e_, _]] :> e
}] /. HoldForm -> quote /. $renamed]

functionOf[x_Symbol, HoldComplete[body_]] := Function[{x}, body]
functionsOf[binders_, HoldComplete[body_]] := Replace[binders /. HoldPattern[Typed[x_, _]] :> x, variables_List :> Function[variables, body]]
markedQuotes[held_HoldComplete, x_Symbol] := held /. HoldPattern[HoldForm[q_]] :> RuleCondition[Replace[HoldComplete[q] /. HoldPattern[x] :> splice[x], HoldComplete[m_] :> HoldForm[m]]]

mValue[a_] := {a}
mSum[a_List, b_List] := Join[a, b]
mBind[m_List, f_] := Join @@ Map[f, m]
mFirst[m_List] := If[m === {}, "none", "some"[First[m]]]
mPart[ex[e_], 0, f_] := f[Extract[HoldComplete[e], {1, 0}, ex]]
mPart[ex[e_], k_Integer, f_] := If[AtomQ[Unevaluated[e]] || k > Length[Unevaluated[e]], {}, f[Extract[HoldComplete[e], {1, k}, ex]]]
mCondition[m_List, c_] := If[TrueQ[c], m, {}]
mMatchQ[m_List] := m =!= {}
mSameQ[a_, b_] := a === b
mElement[l_List, i_Integer] := If[i < Length[l], {l[[i + 1]]}, {}]
mSplits[l_List] := Table[{Take[l, i], Drop[l, i]}, {i, 0, Length[l]}]
mLongestSplits[l_List] := Reverse[mSplits[l]]
mPermutations[l_List] := Map[Function[order, l[[order]]], Permutations[Range[Length[l]]]]
mNormal[ex[h_], arguments_List] := Replace[Join[HoldComplete[h], HoldComplete[], Sequence @@ Replace[arguments, ex[a_] :> HoldComplete[a], {1}]], HoldComplete[head_, parts___] :> ex[head[parts]]]
mHead[ex[e_]] := Extract[HoldComplete[e], {1, 0}, ex]
mAtomQ[ex[e_]] := AtomQ[Unevaluated[e]]
mArguments[ex[e_]] := If[AtomQ[Unevaluated[e]], {}, Replace[HoldComplete[e], HoldComplete[_[parts___]] :> (ex /@ Unevaluated[{parts}])]]
mValueOf[ex[e_]] := With[{value = e}, ex[value]]
mDecide[b_] := TrueQ[b]
mListRecursion[_, base_, step_, {}] := base
mListRecursion[motive_, base_, step_, {first_, rest___}] := step[first, {rest}, mListRecursion[motive, base, step, {rest}]]
quote[e_] := ex @@ (HoldComplete[e] //. {splice[l_List] :> RuleCondition[Sequence @@ l], ex[a_] :> a} //. h_[a___, Verbatim[Sequence][s___], b___] :> h[a, s, b])

(* the result of the translated rules at an expression, and that of the rules themselves, Replace by the first that
   matches, its right side unevaluated *)
translatedResult[symbol_, input_HoldComplete] := Module[{declarations = TypeTheoryFormalize[symbol, wolfram, "Meaning" -> "Rules"]},
	If[! MatchQ[declarations, {___, _TypeTheoryDefinition}], declarations,
		Replace[interpreted[Last[declarations]][ex @@ input], {"some"[ex[e_]] :> HoldComplete[e], "none" -> "none"}]
	]
]
SetAttributes[expectedResult, HoldFirst]
expectedResult[symbol_, input_HoldComplete] := Replace[
	Replace[input, Replace[DownValues[symbol], {
		(HoldPattern[lhs_] :> Verbatim[Condition][value_, test_]) :> (HoldComplete[lhs] :> Condition[HoldComplete[value], test]),
		(HoldPattern[lhs_] :> rhs_) :> (HoldComplete[lhs] :> HoldComplete[rhs])
	}, {1}]],
	unmatched_ /; unmatched === input :> "none"
]
agreesQ[symbol_, inputs_List] := AllTrue[inputs, Function[input, translatedResult[symbol, input] === expectedResult[symbol, input]]]
disagreements[symbol_, inputs_List] := Select[inputs, Function[input, translatedResult[symbol, input] =!= expectedResult[symbol, input]]]

VerificationTest[
	Block[{f},
		f[x_, y_Integer] := {y, x};
		f[0] := "zero";
		f[x_, x_] := "same";
		f[g[x_]] := x;
		f[h_[a_]] := h;
		disagreements[f, {HoldComplete[f[1, 2]], HoldComplete[f[a, 2]], HoldComplete[f[0]], HoldComplete[f[a, a]], HoldComplete[f[g[5]]], HoldComplete[f[k[5]]], HoldComplete[f[1, b]], HoldComplete[f[]]}]
	],
	{},
	TestID -> "Blanks-heads-literals-repeated-names-and-nested-patterns-agree-with-the-Wolfram-Language"
]

VerificationTest[
	Block[{f},
		f[x__, y__] := {{x}, {y}};
		f[x___, 0, y___] := {{x}, {y}};
		f[Longest[x__], y__] := {{x}, {y}};
		disagreements[f, {HoldComplete[f[1, 2, 3]], HoldComplete[f[1]], HoldComplete[f[1, 0, 2, 0, 3]], HoldComplete[f[0]]}]
	],
	{},
	TestID -> "Sequences-split-shortest-first-as-the-Wolfram-Language-does"
]

VerificationTest[
	Block[{f, l, s},
		f[Longest[x__], y__] := {{x}, {y}};
		l[Shortest[x__], y___] := {{x}, {y}};
		s[x_Integer.., y___] := {{x}, {y}};
		{disagreements[f, {HoldComplete[f[1, 2, 3]]}], disagreements[l, {HoldComplete[l[1, 2, 3]]}], disagreements[s, {HoldComplete[s[1, 2, a]], HoldComplete[s[a]], HoldComplete[s[1, 2]]}]}
	],
	{{}, {}, {}},
	TestID -> "Longest-Shortest-and-Repeated-agree-with-the-Wolfram-Language"
]

VerificationTest[
	Block[{f},
		f[x : (_Integer | _String)] := {x};
		f[x : Except[0, _Integer], y_] := {x, y};
		f[x_ /; x > 2] := "big";
		f[x_?EvenQ, y_] := "even";
		f[x_, y_] := x /; y === 1;
		disagreements[f, {HoldComplete[f[1]], HoldComplete[f["a"]], HoldComplete[f[a]], HoldComplete[f[3]], HoldComplete[f[0, 5]], HoldComplete[f[2, 5]], HoldComplete[f[a, 1]], HoldComplete[f[a, 2]]}]
	],
	{},
	TestID -> "Alternatives-Except-Condition-PatternTest-and-conditions-on-the-right-agree"
]

VerificationTest[
	Block[{f, o},
		f[x_, y_ : 7] := {x, y};
		f[PatternSequence[a_, b_], c___] := {{a, b}, {c}};
		o[OrderlessPatternSequence[x_Integer, y_String]] := {x, y};
		{
			disagreements[f, {HoldComplete[f[1]], HoldComplete[f[1, 2]], HoldComplete[f[1, 2, 3]]}],
			disagreements[o, {HoldComplete[o[1, "a"]], HoldComplete[o["a", 1]], HoldComplete[o[1, 2]]}]
		}
	],
	{{}, {}},
	TestID -> "Optional-PatternSequence-and-OrderlessPatternSequence-agree"
]

VerificationTest[
	Block[{f, p, v},
		SetAttributes[p, Orderless];
		p[x_Integer, y_String] := {x, y};
		f[x_, OptionsPattern[]] := {x};
		v[Verbatim[_]] := "blank";
		v[HoldPattern[a_ + b_]] := {a, b};
		{
			disagreements[p, {HoldComplete[p[1, "a"]], HoldComplete[p["a", 1]], HoldComplete[p[1, 2]]}],
			disagreements[f, {HoldComplete[f[1]], HoldComplete[f[1, "a" -> 2]], HoldComplete[f[1, 2]]}],
			disagreements[v, {HoldComplete[v[_]], HoldComplete[v[x]], HoldComplete[v[1 + 2]]}]
		}
	],
	{{}, {}, {}},
	TestID -> "Orderless-heads-OptionsPattern-Verbatim-and-HoldPattern-agree"
]

(* Flat and Orderless heads, as Plus is, sequences under an Orderless head, repetitions within bounds, a condition on a
   sequence and alternatives of sequences *)
VerificationTest[
	Block[{f, g, r, c},
		f[x_ + 1] := x;
		f[a_ + b_ + c] := {a, b};
		g[p[x_Integer, y__]] := {x, {y}};
		r[x : Repeated[_Integer, {2, 3}], y___] := {{x}, {y}};
		c[x__ /; Length[{x}] == 2, y___] := {{x}, {y}};
		c[(x__Integer | x__String), "end"] := {x};
		SetAttributes[p, Orderless];
		{
			disagreements[f, {HoldComplete[f[a + 1]], HoldComplete[f[a + b + 1]], HoldComplete[f[a + b + c]], HoldComplete[f[a]]}],
			disagreements[g, {HoldComplete[g[p[1, b, c]]], HoldComplete[g[p[b, c]]]}],
			disagreements[r, {HoldComplete[r[1]], HoldComplete[r[1, 2]], HoldComplete[r[1, 2, 3, 4]]}],
			disagreements[c, {HoldComplete[c[1, 2, 3]], HoldComplete[c[1]], HoldComplete[c[1, 2, "end"]]}]
		}
	],
	{{}, {}, {}, {}},
	TestID -> "Flat-and-Orderless-heads-bounded-repetitions-and-conditioned-sequences-agree"
]
