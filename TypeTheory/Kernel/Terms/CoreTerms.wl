(* ::Package:: *)

(*
The kernel's own representation of terms, and universe levels.

Core terms are locally nameless. A bound variable is a de Bruijn index, so terms that differ only in
the names of their bound variables are identical expressions, and SameQ, Association keys and caches
compare them structurally. A free variable is an integer naming an entry of a local context, which
carries its name and type.

	boundVariable[index]                                index 0 is the innermost binder
	freeVariable[id]                                    id an Integer
	metavariable[id]                                    a hole, solved by unification or by a tactic
	universeSort[level]                                 Sort level; Prop is universeSort[0]
	constantReference[HoldComplete[name], {level, ...}] a declared constant at universe levels
	application[function, argument]
	lambdaAbstraction[HoldComplete[name], domain, body, binder]
	dependentFunctionType[HoldComplete[name], domain, codomain, binder]
	localDefinition[HoldComplete[name], type, value, body]
	naturalLiteral[n]                                   n a non-negative Integer
	projection[HoldComplete[structure], index, term]    field index, counting from 0, of a term of a structure type

Names are held, so a constant or variable whose symbol has a value never evaluates inside a term.
binder is one of "Explicit", "Implicit", "StrictImplicit", "InstanceImplicit".

Levels are a non-negative Integer, levelParameter[HoldComplete[u]], levelMetavariable[id],
levelSuccessor[level, k] (level + k for an Integer k >= 1), levelMaximum[level, ...] and
levelImpredicativeMaximum[a, b], which is 0 when b is 0 and the maximum of a and b otherwise.
normalizeLevel brings a level to a canonical form, so equal canonical forms mean equal levels.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[boundVariable]
PackageScoped[freeVariable]
PackageScoped[metavariable]
PackageScoped[universeSort]
PackageScoped[constantReference]
PackageScoped[application]
PackageScoped[lambdaAbstraction]
PackageScoped[dependentFunctionType]
PackageScoped[localDefinition]
PackageScoped[naturalLiteral]
PackageScoped[projection]

PackageScoped[levelParameter]
PackageScoped[levelMetavariable]
PackageScoped[levelSuccessor]
PackageScoped[levelMaximum]
PackageScoped[levelImpredicativeMaximum]

PackageScoped[liftBoundVariables]
PackageScoped[instantiateBoundVariable]
PackageScoped[abstractFreeVariable]
PackageScoped[boundVariableOccursQ]
PackageScoped[instantiateUniverseParameters]
PackageScoped[applicationSpine]
PackageScoped[makeApplication]
PackageScoped[betaNormalize]
PackageScoped[normalizeLevel]
PackageScoped[levelEquivalentQ]
PackageScoped[levelLessEqualQ]
PackageScoped[levelNeverZeroQ]


(* ::Section:: *)
(*Usage Messages*)


boundVariable::usage = "boundVariable[index] is a variable bound by the index-th enclosing binder, counting from 0 at the innermost."
freeVariable::usage = "freeVariable[id] is a variable of a local context, whose name and type the context holds under id."
metavariable::usage = "metavariable[id] is a hole in a term, to be solved by unification or by a tactic."
universeSort::usage = "universeSort[level] is the sort at level; universeSort[0] is Prop."
constantReference::usage = "constantReference[HoldComplete[name], {level, ...}] refers to the declared constant name at the given universe levels."
application::usage = "application[function, argument] applies function to argument."
lambdaAbstraction::usage = "lambdaAbstraction[HoldComplete[name], domain, body, binder] is a function of a variable of type domain; body refers to it as boundVariable[0]."
dependentFunctionType::usage = "dependentFunctionType[HoldComplete[name], domain, codomain, binder] is the type of functions from domain to codomain, \
which may refer to the argument as boundVariable[0]."
localDefinition::usage = "localDefinition[HoldComplete[name], type, value, body] binds value of type type in body, which refers to it as boundVariable[0]."
naturalLiteral::usage = "naturalLiteral[n] is the natural number n."
projection::usage = "projection[HoldComplete[structure], index, term] is the field index, counting from 0, of term, whose type is the structure structure: \
an inductive type with one constructor and no indices."

levelParameter::usage = "levelParameter[HoldComplete[u]] is the universe parameter u."
levelMetavariable::usage = "levelMetavariable[id] is an unknown universe level, solved by unification."
levelSuccessor::usage = "levelSuccessor[level, k] is level + k."
levelMaximum::usage = "levelMaximum[level1, level2, ...] is the largest of the levels."
levelImpredicativeMaximum::usage = "levelImpredicativeMaximum[a, b] is 0 when b is 0 and the maximum of a and b otherwise: the level of a function type from Sort a to Sort b."

liftBoundVariables::usage = "liftBoundVariables[term, amount, cutoff] adds amount to every bound variable index at least cutoff."
instantiateBoundVariable::usage = "instantiateBoundVariable[body, value] replaces the variable bound just outside body by value."
abstractFreeVariable::usage = "abstractFreeVariable[term, id] replaces freeVariable[id] by a bound variable, ready to be wrapped in a binder."
boundVariableOccursQ::usage = "boundVariableOccursQ[body, index] gives True if body refers to boundVariable[index] counted from its own top."
instantiateUniverseParameters::usage = "instantiateUniverseParameters[term, {u, ...}, {level, ...}] replaces each universe parameter u by its level."
applicationSpine::usage = "applicationSpine[term] gives {head, {argument, ...}}, unwinding nested applications."
makeApplication::usage = "makeApplication[head, {argument, ...}] applies head to the arguments in turn."
betaNormalize::usage = "betaNormalize[term] reduces every application of a function in term, unfolding nothing."
normalizeLevel::usage = "normalizeLevel[level] gives the canonical form of level."
levelEquivalentQ::usage = "levelEquivalentQ[a, b] gives True if the levels a and b have the same canonical form."
levelLessEqualQ::usage = "levelLessEqualQ[a, b] gives True if a <= b holds for every value of the universe parameters; it may answer False for a true \
inequality it cannot prove, never True for a false one."
levelNeverZeroQ::usage = "levelNeverZeroQ[level] gives True if level is at least 1 for every value of the universe parameters."


(* ::Section:: *)
(*Function Definitions*)


(* ::Subsection:: *)
(*Bound variables*)


liftBoundVariables[term_, 0, _] := term
liftBoundVariables[boundVariable[index_], amount_, cutoff_] := boundVariable[If[index >= cutoff, index + amount, index]]
liftBoundVariables[application[function_, argument_], amount_, cutoff_] :=
	application[liftBoundVariables[function, amount, cutoff], liftBoundVariables[argument, amount, cutoff]]
liftBoundVariables[lambdaAbstraction[name_, domain_, body_, binder_], amount_, cutoff_] :=
	lambdaAbstraction[name, liftBoundVariables[domain, amount, cutoff], liftBoundVariables[body, amount, cutoff + 1], binder]
liftBoundVariables[dependentFunctionType[name_, domain_, codomain_, binder_], amount_, cutoff_] :=
	dependentFunctionType[name, liftBoundVariables[domain, amount, cutoff], liftBoundVariables[codomain, amount, cutoff + 1], binder]
liftBoundVariables[localDefinition[name_, type_, value_, body_], amount_, cutoff_] :=
	localDefinition[name, liftBoundVariables[type, amount, cutoff], liftBoundVariables[value, amount, cutoff], liftBoundVariables[body, amount, cutoff + 1]]
liftBoundVariables[projection[structure_, index_, term_], amount_, cutoff_] := projection[structure, index, liftBoundVariables[term, amount, cutoff]]
liftBoundVariables[term_, _, _] := term


instantiateBoundVariable[body_, value_] := substituteBoundVariable[body, value, 0]

substituteBoundVariable[boundVariable[index_], value_, depth_] := Which[
	index == depth,
		liftBoundVariables[value, depth, 0],
	index > depth,
		boundVariable[index - 1],
	True,
		boundVariable[index]
]
substituteBoundVariable[application[function_, argument_], value_, depth_] :=
	application[substituteBoundVariable[function, value, depth], substituteBoundVariable[argument, value, depth]]
substituteBoundVariable[lambdaAbstraction[name_, domain_, body_, binder_], value_, depth_] :=
	lambdaAbstraction[name, substituteBoundVariable[domain, value, depth], substituteBoundVariable[body, value, depth + 1], binder]
substituteBoundVariable[dependentFunctionType[name_, domain_, codomain_, binder_], value_, depth_] :=
	dependentFunctionType[name, substituteBoundVariable[domain, value, depth], substituteBoundVariable[codomain, value, depth + 1], binder]
substituteBoundVariable[localDefinition[name_, type_, definedValue_, body_], value_, depth_] :=
	localDefinition[name, substituteBoundVariable[type, value, depth], substituteBoundVariable[definedValue, value, depth], substituteBoundVariable[body, value, depth + 1]]
substituteBoundVariable[projection[structure_, index_, term_], value_, depth_] := projection[structure, index, substituteBoundVariable[term, value, depth]]
substituteBoundVariable[term_, _, _] := term


abstractFreeVariable[term_, id_] := abstractAt[term, id, 0]

abstractAt[freeVariable[id_], id_, depth_] := boundVariable[depth]
abstractAt[application[function_, argument_], id_, depth_] := application[abstractAt[function, id, depth], abstractAt[argument, id, depth]]
abstractAt[lambdaAbstraction[name_, domain_, body_, binder_], id_, depth_] :=
	lambdaAbstraction[name, abstractAt[domain, id, depth], abstractAt[body, id, depth + 1], binder]
abstractAt[dependentFunctionType[name_, domain_, codomain_, binder_], id_, depth_] :=
	dependentFunctionType[name, abstractAt[domain, id, depth], abstractAt[codomain, id, depth + 1], binder]
abstractAt[localDefinition[name_, type_, value_, body_], id_, depth_] :=
	localDefinition[name, abstractAt[type, id, depth], abstractAt[value, id, depth], abstractAt[body, id, depth + 1]]
abstractAt[projection[structure_, index_, term_], id_, depth_] := projection[structure, index, abstractAt[term, id, depth]]
abstractAt[term_, _, _] := term


boundVariableOccursQ[boundVariable[index_], target_] := index == target
boundVariableOccursQ[application[function_, argument_], target_] := boundVariableOccursQ[function, target] || boundVariableOccursQ[argument, target]
boundVariableOccursQ[(lambdaAbstraction | dependentFunctionType)[_, domain_, body_, _], target_] :=
	boundVariableOccursQ[domain, target] || boundVariableOccursQ[body, target + 1]
boundVariableOccursQ[localDefinition[_, type_, value_, body_], target_] :=
	boundVariableOccursQ[type, target] || boundVariableOccursQ[value, target] || boundVariableOccursQ[body, target + 1]
boundVariableOccursQ[projection[_, _, term_], target_] := boundVariableOccursQ[term, target]
boundVariableOccursQ[_, _] := False


(* ::Subsection:: *)
(*Applications and universe parameters*)


applicationSpine[term_] := spineFrom[term, {}]
spineFrom[application[function_, argument_], arguments_List] := spineFrom[function, Prepend[arguments, argument]]
spineFrom[head_, arguments_List] := {head, arguments}

makeApplication[head_, arguments_List] := Fold[application, head, arguments]


(* beta reduction alone terminates on well-typed terms; it gives the readable form of a type *)
betaNormalize[application[function_, argument_]] := betaApply[betaNormalize[function], betaNormalize[argument]]
betaNormalize[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_]] := head[name, betaNormalize[domain], betaNormalize[body], binder]
betaNormalize[localDefinition[name_, type_, value_, body_]] := localDefinition[name, betaNormalize[type], betaNormalize[value], betaNormalize[body]]
betaNormalize[projection[structure_, index_, term_]] := projection[structure, index, betaNormalize[term]]
betaNormalize[term_] := term

betaApply[lambdaAbstraction[_, _, body_, _], argument_] := betaNormalize[instantiateBoundVariable[body, argument]]
betaApply[function_, argument_] := application[function, argument]


instantiateUniverseParameters[term_, {}, {}] := term
instantiateUniverseParameters[term_, parameters_List, levels_List] /; Length[parameters] == Length[levels] := With[
	{rules = Thread[(levelParameter /@ parameters) -> levels]},
	term /. {
		universeSort[level_] :> universeSort[normalizeLevel[level /. rules]],
		constantReference[name_, constantLevels_List] :> constantReference[name, normalizeLevel /@ (constantLevels /. rules)]
	}
]


(* ::Subsection:: *)
(*Universe levels*)


(* A canonical level is a maximum of components, each an Integer or {base, offset} with base a
   parameter, a metavariable, or an impredicative maximum that could not be simplified. *)

normalizeLevel[level_] := fromComponents[levelComponents[level]]

levelComponents[n_Integer] := {n}
levelComponents[base : (_levelParameter | _levelMetavariable)] := {{base, 0}}
levelComponents[levelSuccessor[level_, k_Integer]] := Replace[levelComponents[level], {n_Integer :> n + k, {base_, offset_} :> {base, offset + k}}, {1}]
levelComponents[levelMaximum[levels___]] := mergeComponents[Join @@ (levelComponents /@ {levels})]
levelComponents[levelImpredicativeMaximum[a_, b_]] := impredicativeComponents[levelComponents[a], levelComponents[b]]

(* imax a b is max a b when b is never 0, and b when b is 0 or a is 0 *)
impredicativeComponents[a_, b_] := Which[
	b === {0},
		{0},
	componentsNeverZeroQ[b],
		mergeComponents[Join[a, b]],
	a === {0} || a === b,
		b,
	True,
		{{levelImpredicativeMaximum[fromComponents[a], fromComponents[b]], 0}}
]

componentsNeverZeroQ[components_List] := AnyTrue[components, Function[component, MatchQ[component, (n_Integer /; n > 0) | {_, k_ /; k > 0}]]]

mergeComponents[components_List] := With[
	{
		constant = Max[0, Cases[components, _Integer]],
		bases = Normal @ GroupBy[Cases[components, {_, _}], First -> Last, Max]
	},
	With[{kept = SortBy[List @@@ bases, First]},
		If[ AnyTrue[kept, Function[component, Last[component] >= constant]] && kept =!= {},
			kept,
			Prepend[kept, constant]
		]
	]
]

fromComponents[{n_Integer}] := n
fromComponents[{{base_, 0}}] := base
fromComponents[{{base_, offset_}}] := levelSuccessor[base, offset]
fromComponents[components_List] := levelMaximum @@ Replace[components, {{base_, 0} :> base, {base_, offset_} :> levelSuccessor[base, offset]}, {1}]


levelEquivalentQ[a_, b_] := normalizeLevel[a] === normalizeLevel[b]

levelNeverZeroQ[level_] := componentsNeverZeroQ[levelComponents[level]]

levelLessEqualQ[a_, b_] := componentsLessEqualQ[levelComponents[a], levelComponents[b]]

(* every component of a is below some component of b, or below b's least value *)
componentsLessEqualQ[a_List, b_List] := AllTrue[a, Function[component, componentLessEqualQ[component, b]]]
componentLessEqualQ[n_Integer, b_List] := n <= Max[Replace[b, {m_Integer :> m, {_, offset_} :> offset}, {1}]]
componentLessEqualQ[{base_, offset_}, b_List] := MemberQ[b, {base, other_ /; other >= offset}]
