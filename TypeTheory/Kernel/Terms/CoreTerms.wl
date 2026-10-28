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
	cubicalSystem[{{face, term}, ...}]                  a system of partial elements of cubical type theory (Cubical.wl)
	intervalUniverse[]                                  the sort of the interval of cubical type theory, no universe

Names are held, so a constant or variable whose symbol has a value never evaluates inside a term.
binder is its kind, one of "Explicit", "Implicit", "StrictImplicit", "InstanceImplicit", or under rules
with quantities {kind, quantity} with quantity 0 or 1 (Quantities.wl); a binder that is its kind alone has
the quantity Infinity.

Levels are a non-negative Integer, levelParameter[HoldComplete[u]], levelMetavariable[id],
levelSuccessor[level, k] (level + k for an Integer k >= 1), levelMaximum[level, ...] and
levelImpredicativeMaximum[a, b], which is 0 when b is 0 and the maximum of a and b otherwise.
normalizeLevel brings a level to a canonical form, so equal canonical forms mean equal levels.

The composite heads, application, lambdaAbstraction, dependentFunctionType, localDefinition, projection and
cubicalSystem, hold their parts completely, so evaluating a term stops at its head however large the term is.
A term is built from parts computed first, with Construct or With: a call written inside a composite head
stays a call, and a Module or Block variable stays a symbol. A replacement rule puts its right side into the
term as written, so a rule that computes does so as it matches, With[{value = ...}, value /; True].
withTermConstructionCheck finds a construction that leaves a part uncomputed.
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
PackageScoped[cubicalSystem]
PackageScoped[intervalUniverse]

PackageScoped[levelParameter]
PackageScoped[levelMetavariable]
PackageScoped[levelSuccessor]
PackageScoped[levelMaximum]
PackageScoped[levelImpredicativeMaximum]

PackageScoped[binderKind]
PackageScoped[binderQuantity]
PackageScoped[quantifiedBinder]
PackageScoped[withoutQuantities]

PackageScoped[liftBoundVariables]
PackageScoped[looseBoundRange]
PackageScoped[$looseBoundRangeCache]
PackageScoped[instantiateBoundVariable]
PackageScoped[instantiateBoundVariables]
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

PackageScoped[withTermConstructionCheck]
PackageScoped[installTermConstructionCheck]
PackageScoped[removeTermConstructionCheck]
PackageScoped[$termConstructionSites]


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
cubicalSystem::usage = "cubicalSystem[{{face, term}, ...}] is a system of cubical type theory: a partial element, each term given where its face holds."
intervalUniverse::usage = "intervalUniverse[] is the sort of the Interval of cubical type theory, which is no universe: nothing may have a type of it but the interval."

levelParameter::usage = "levelParameter[HoldComplete[u]] is the universe parameter u."
levelMetavariable::usage = "levelMetavariable[id] is an unknown universe level, solved by unification."
levelSuccessor::usage = "levelSuccessor[level, k] is level + k."
levelMaximum::usage = "levelMaximum[level1, level2, ...] is the largest of the levels."
levelImpredicativeMaximum::usage = "levelImpredicativeMaximum[a, b] is 0 when b is 0 and the maximum of a and b otherwise: the level of a function type from Sort a to Sort b."

binderKind::usage = "binderKind[binder] gives the kind of binder: \"Explicit\", \"Implicit\", \"StrictImplicit\" or \"InstanceImplicit\"."
binderQuantity::usage = "binderQuantity[binder] gives the quantity of binder: 0, 1, or Infinity for a binder that is its kind alone."
quantifiedBinder::usage = "quantifiedBinder[kind, quantity] gives the binder of the given kind and quantity: the kind alone for the quantity Infinity, and {kind, quantity} otherwise."
withoutQuantities::usage = "withoutQuantities[term] gives term with the quantity of every binder in it removed."

liftBoundVariables::usage = "liftBoundVariables[term, amount, cutoff] adds amount to every bound variable index at least cutoff."
looseBoundRange::usage = "looseBoundRange[term] gives one more than the largest index of a bound variable of term that no binder of term binds, or 0."
$looseBoundRangeCache::usage = "$looseBoundRangeCache is the Association of loose bound ranges remembered while the kernel checks a declaration, or None."
instantiateBoundVariable::usage = "instantiateBoundVariable[body, value] replaces the variable bound just outside body by value."
instantiateBoundVariables::usage = "instantiateBoundVariables[body, {value1, ..., valuek}] replaces the k variables bound just outside body by the values at once, the innermost by valuek."
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

withTermConstructionCheck::usage = "withTermConstructionCheck[expr] evaluates expr while every construction of a composite term that leaves a part \
uncomputed is caught, computed and recorded, and gives {result, <|place -> count, ...|>}."
installTermConstructionCheck::usage = "installTermConstructionCheck[] catches, computes and records in $termConstructionSites every construction of a \
composite term that leaves a part uncomputed, until removeTermConstructionCheck[]."
removeTermConstructionCheck::usage = "removeTermConstructionCheck[] stops the check that installTermConstructionCheck[] started."
$termConstructionSites::usage = "$termConstructionSites is the Association of the places where a composite term was built with a part uncomputed, \
counted, while the construction check is on."


(* ::Section:: *)
(*Function Definitions*)


(* ::Subsection:: *)
(*Composite terms*)


(* After any assignment, W15's evaluator evaluates an expression's parts again where it meets it, so a term passed
   on was walked as the tree it writes out to: a term of a million leaves and forty distinct nodes took
   887 us to pass, 0.8 us with its heads holding their parts completely. HoldAll does not stop the walk, since it
   still looks into the parts for Sequence and Unevaluated. *)
SetAttributes[{application, lambdaAbstraction, dependentFunctionType, localDefinition, projection, cubicalSystem}, HoldAllComplete]

$compositeHeads = {application, lambdaAbstraction, dependentFunctionType, localDefinition, projection, cubicalSystem}


(* ::Subsection:: *)
(*Binders*)


binderKind[{kind_String, _}] := kind
binderKind[kind_] := kind

binderQuantity[{_String, quantity_}] := quantity
binderQuantity[_] := Infinity

quantifiedBinder[kind_String, Infinity] := kind
quantifiedBinder[kind_String, quantity_] := {kind, quantity}

withoutQuantities[term_] := ReplaceAll[
	term,
	(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, {kind_String, _}] :>
		With[{bare = Construct[head, name, withoutQuantities[domain], withoutQuantities[body], kind]}, bare /; True]
]


(* ::Subsection:: *)
(*Bound variables*)


(* A term built by a tactic shares its subterms many times over: the proof of a lemma about integers
   that grind writes has 3.6 million nodes written out and under 6,000 distinct ones. Lifting,
   substitution and abstraction therefore pass by a subterm with no variable they could change, which
   its loose bound range tells, and work out each distinct subterm once per call, so the subterms of
   the result are shared as those of the term are. The range of a subterm is remembered while the
   kernel checks a declaration, where it saves a factor of four on balanceL's cone; the range of a
   variable or a constant is read off it, without the cache, which it would only fill. Substitution by
   one native scan for the variables and one ReplacePart was tried and is many times slower: it visits
   each occurrence of a shared subterm, where this walk visits each distinct one once. *)

looseBoundRange[boundVariable[index_]] := index + 1
looseBoundRange[_constantReference | _universeSort | _naturalLiteral | _freeVariable | _metavariable] := 0
looseBoundRange[term_] := If[ AssociationQ[$looseBoundRangeCache],
	Lookup[$looseBoundRangeCache, Key[term], $looseBoundRangeCache[term] = looseBoundRangeOf[term]],
	looseBoundRangeOf[term]
]

looseBoundRangeOf[boundVariable[index_]] := index + 1
looseBoundRangeOf[application[function_, argument_]] := Max[looseBoundRange[function], looseBoundRange[argument]]
looseBoundRangeOf[(lambdaAbstraction | dependentFunctionType)[_, domain_, body_, _]] := Max[looseBoundRange[domain], looseBoundRange[body] - 1]
looseBoundRangeOf[localDefinition[_, type_, value_, body_]] := Max[looseBoundRange[type], looseBoundRange[value], looseBoundRange[body] - 1]
looseBoundRangeOf[projection[_, _, term_]] := looseBoundRange[term]
looseBoundRangeOf[cubicalSystem[branches_List]] := Max[0, looseBoundRange /@ Flatten[branches, 1]]
looseBoundRangeOf[_] := 0

$looseBoundRangeCache = None

(* outside a check of the kernel, a call remembers the ranges it works out for its own use *)
SetAttributes[withRangeCache, HoldFirst]
withRangeCache[body_] := If[AssociationQ[$looseBoundRangeCache], body, Block[{$looseBoundRangeCache = <||>}, body]]


liftBoundVariables[term_, 0, _] := term
liftBoundVariables[term_, amount_, cutoff_] := withRangeCache[
	If[looseBoundRange[term] <= cutoff, term, Block[{$liftMemo = <||>}, liftShared[term, amount, cutoff]]]
]

liftShared[term_, amount_, cutoff_] := If[ looseBoundRange[term] <= cutoff,
	term,
	Lookup[$liftMemo, Key[{term, cutoff}], $liftMemo[{term, cutoff}] = liftNode[term, amount, cutoff]]
]

liftNode[boundVariable[index_], amount_, cutoff_] := boundVariable[If[index >= cutoff, index + amount, index]]
liftNode[application[function_, argument_], amount_, cutoff_] := Construct[application, liftShared[function, amount, cutoff], liftShared[argument, amount, cutoff]]
liftNode[lambdaAbstraction[name_, domain_, body_, binder_], amount_, cutoff_] :=
	Construct[lambdaAbstraction, name, liftShared[domain, amount, cutoff], liftShared[body, amount, cutoff + 1], binder]
liftNode[dependentFunctionType[name_, domain_, codomain_, binder_], amount_, cutoff_] :=
	Construct[dependentFunctionType, name, liftShared[domain, amount, cutoff], liftShared[codomain, amount, cutoff + 1], binder]
liftNode[localDefinition[name_, type_, value_, body_], amount_, cutoff_] :=
	Construct[localDefinition, name, liftShared[type, amount, cutoff], liftShared[value, amount, cutoff], liftShared[body, amount, cutoff + 1]]
liftNode[projection[structure_, index_, term_], amount_, cutoff_] := Construct[projection, structure, index, liftShared[term, amount, cutoff]]
liftNode[cubicalSystem[branches_List], amount_, cutoff_] := Construct[cubicalSystem, Map[Function[part, liftShared[part, amount, cutoff]], branches, {2}]]
liftNode[term_, _, _] := term


instantiateBoundVariable[body_, value_] := instantiateBoundVariables[body, {value}]

(* the variables bound just outside body, innermost last, replaced at once by values, as beta reduction of a
   function of several arguments needs: body refers to the last value as boundVariable[0] *)
instantiateBoundVariables[body_, values_List] := withRangeCache[
	If[looseBoundRange[body] == 0, body, Block[{$substitutionMemo = <||>}, substituteShared[body, Reverse[values], 0]]]
]

(* values innermost first: boundVariable[depth + j] is the value at j + 1 *)
substituteShared[term_, values_, depth_] := If[ looseBoundRange[term] <= depth,
	term,
	Lookup[$substitutionMemo, Key[{term, depth}], $substitutionMemo[{term, depth}] = substituteNode[term, values, depth]]
]

substituteNode[boundVariable[index_], values_, depth_] := Which[
	index < depth,
		boundVariable[index],
	index < depth + Length[values],
		liftBoundVariables[values[[index - depth + 1]], depth, 0],
	True,
		boundVariable[index - Length[values]]
]
substituteNode[application[function_, argument_], values_, depth_] :=
	Construct[application, substituteShared[function, values, depth], substituteShared[argument, values, depth]]
substituteNode[lambdaAbstraction[name_, domain_, body_, binder_], values_, depth_] :=
	Construct[lambdaAbstraction, name, substituteShared[domain, values, depth], substituteShared[body, values, depth + 1], binder]
substituteNode[dependentFunctionType[name_, domain_, codomain_, binder_], values_, depth_] :=
	Construct[dependentFunctionType, name, substituteShared[domain, values, depth], substituteShared[codomain, values, depth + 1], binder]
substituteNode[localDefinition[name_, type_, definedValue_, body_], values_, depth_] :=
	Construct[localDefinition, name, substituteShared[type, values, depth], substituteShared[definedValue, values, depth], substituteShared[body, values, depth + 1]]
substituteNode[projection[structure_, index_, term_], values_, depth_] := Construct[projection, structure, index, substituteShared[term, values, depth]]
substituteNode[cubicalSystem[branches_List], values_, depth_] := Construct[cubicalSystem, Map[Function[part, substituteShared[part, values, depth]], branches, {2}]]
substituteNode[term_, _, _] := term


abstractFreeVariable[term_, id_] := Block[{$abstractionMemo = <||>}, abstractShared[term, id, 0]]

abstractShared[term : (_boundVariable | _universeSort | _constantReference | _naturalLiteral | _metavariable | _intervalUniverse), _, _] := term
abstractShared[term_, id_, depth_] := Lookup[$abstractionMemo, Key[{term, depth}], $abstractionMemo[{term, depth}] = abstractAt[term, id, depth]]

abstractAt[freeVariable[id_], id_, depth_] := boundVariable[depth]
abstractAt[application[function_, argument_], id_, depth_] := Construct[application, abstractShared[function, id, depth], abstractShared[argument, id, depth]]
abstractAt[lambdaAbstraction[name_, domain_, body_, binder_], id_, depth_] :=
	Construct[lambdaAbstraction, name, abstractShared[domain, id, depth], abstractShared[body, id, depth + 1], binder]
abstractAt[dependentFunctionType[name_, domain_, codomain_, binder_], id_, depth_] :=
	Construct[dependentFunctionType, name, abstractShared[domain, id, depth], abstractShared[codomain, id, depth + 1], binder]
abstractAt[localDefinition[name_, type_, value_, body_], id_, depth_] :=
	Construct[localDefinition, name, abstractShared[type, id, depth], abstractShared[value, id, depth], abstractShared[body, id, depth + 1]]
abstractAt[projection[structure_, index_, term_], id_, depth_] := Construct[projection, structure, index, abstractShared[term, id, depth]]
abstractAt[cubicalSystem[branches_List], id_, depth_] := Construct[cubicalSystem, Map[Function[part, abstractShared[part, id, depth]], branches, {2}]]
abstractAt[term_, _, _] := term


boundVariableOccursQ[boundVariable[index_], target_] := index == target
boundVariableOccursQ[application[function_, argument_], target_] := boundVariableOccursQ[function, target] || boundVariableOccursQ[argument, target]
boundVariableOccursQ[(lambdaAbstraction | dependentFunctionType)[_, domain_, body_, _], target_] :=
	boundVariableOccursQ[domain, target] || boundVariableOccursQ[body, target + 1]
boundVariableOccursQ[localDefinition[_, type_, value_, body_], target_] :=
	boundVariableOccursQ[type, target] || boundVariableOccursQ[value, target] || boundVariableOccursQ[body, target + 1]
boundVariableOccursQ[projection[_, _, term_], target_] := boundVariableOccursQ[term, target]
boundVariableOccursQ[cubicalSystem[branches_List], target_] := AnyTrue[Flatten[branches, 1], Function[part, boundVariableOccursQ[part, target]]]
boundVariableOccursQ[_, _] := False


(* ::Subsection:: *)
(*Applications and universe parameters*)


applicationSpine[term_] := spineFrom[term, {}]
spineFrom[application[function_, argument_], arguments_List] := spineFrom[function, Prepend[arguments, argument]]
spineFrom[head_, arguments_List] := {head, arguments}

makeApplication[head_, arguments_List] := Fold[application, head, arguments]


(* beta reduction alone terminates on well-typed terms; it gives the readable form of a type *)
betaNormalize[application[function_, argument_]] := betaApply[betaNormalize[function], betaNormalize[argument]]
betaNormalize[(head : lambdaAbstraction | dependentFunctionType)[name_, domain_, body_, binder_]] := Construct[head, name, betaNormalize[domain], betaNormalize[body], binder]
betaNormalize[localDefinition[name_, type_, value_, body_]] := Construct[localDefinition, name, betaNormalize[type], betaNormalize[value], betaNormalize[body]]
betaNormalize[projection[structure_, index_, term_]] := Construct[projection, structure, index, betaNormalize[term]]
betaNormalize[cubicalSystem[branches_List]] := Construct[cubicalSystem, Map[betaNormalize, branches, {2}]]
betaNormalize[term_] := term

betaApply[lambdaAbstraction[_, _, body_, _], argument_] := betaNormalize[instantiateBoundVariable[body, argument]]
betaApply[function_, argument_] := application[function, argument]


instantiateUniverseParameters[term_, {}, {}] := term
instantiateUniverseParameters[term_, parameters_List, levels_List] /; Length[parameters] == Length[levels] := With[
	{rules = Thread[(levelParameter /@ parameters) -> levels]},
	term /. {
		universeSort[level_] :> With[{instantiated = normalizeLevel[level /. rules]}, universeSort[instantiated] /; True],
		constantReference[name_, constantLevels_List] :> With[{instantiated = normalizeLevel /@ (constantLevels /. rules)}, constantReference[name, instantiated] /; True]
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

(* imax a b is max a b when b is never 0, and b when b is 0 or a <= max 1 b, as for a = 0, a = 1 or a = b:
   then b = 0 gives 0, and b >= 1 gives max a b = b. Lean's kernel reads imax 1 u as u the same way. *)
impredicativeComponents[a_, b_] := Which[
	b === {0},
		{0},
	componentsNeverZeroQ[b],
		mergeComponents[Join[a, b]],
	componentsLessEqualQ[a, mergeComponents[Append[b, 1]]],
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

(* every component of a is below some component of b, or below b's least value; imax x y is at most
   max x y, so it is below b when x and y are *)
componentsLessEqualQ[a_List, b_List] := AllTrue[a, Function[component, componentLessEqualQ[component, b]]]
componentLessEqualQ[n_Integer, b_List] := n <= Max[Replace[b, {m_Integer :> m, {_, offset_} :> offset}, {1}]]
componentLessEqualQ[{base_, offset_}, b_List] /; MemberQ[b, {base, other_ /; other >= offset}] := True
componentLessEqualQ[{levelImpredicativeMaximum[x_, y_], offset_}, b_List] :=
	componentsLessEqualQ[levelComponents[levelSuccessor[x, offset]], b] && componentsLessEqualQ[levelComponents[levelSuccessor[y, offset]], b]
componentLessEqualQ[{_, _}, _List] := False


(* ::Subsection:: *)
(*Construction check*)


(* The check is a rule on each composite head that fires when a part of the term is not a term yet: the parts
   are computed, the term is built from them, and the place is recorded, by the kind of the first part found
   uncomputed and the kernel functions being evaluated. A part that evaluation leaves as it is but that is no
   term, as a pending abstraction in a proof under construction, is recorded as data and taken as it is. *)

SetAttributes[withTermConstructionCheck, HoldFirst]
withTermConstructionCheck[expr_] := Block[{$termConstructionSites = <||>, $readyTerms = <||>},
	installTermConstructionCheck[];
	WithCleanup[{expr, $termConstructionSites}, removeTermConstructionCheck[]]
]

installTermConstructionCheck[] := (
	If[ ! AssociationQ[$termConstructionSites], $termConstructionSites = <||>];
	If[ ! AssociationQ[$readyTerms], $readyTerms = <||>];
	Scan[Function[head, head[parts___] /; ! readyTermQ[head[parts]] := checkedConstruction[head, parts]], $compositeHeads]
)

removeTermConstructionCheck[] := Scan[Function[head, DownValues[head] = {}], $compositeHeads]

$termConstructionSites = None

$readyTerms = None

SetAttributes[{readyTermQ, rememberReady, readyCompositeQ, readyLevelQ, readyLevelsQ, readyBinderQ, readyBranchesQ}, HoldAllComplete]

(* a term none of whose parts is left to compute, checked without evaluating it; a composite found ready is
   remembered, so a term built from checked parts is checked at its own parts alone *)
readyTermQ[term : _application | _lambdaAbstraction | _dependentFunctionType | _localDefinition | _projection | _cubicalSystem] :=
	Lookup[$readyTerms, Key[HoldComplete[term]], rememberReady[term]]
readyTermQ[boundVariable[_Integer] | freeVariable[_Integer] | metavariable[_Integer] | naturalLiteral[_Integer] | intervalUniverse[]] := True
readyTermQ[universeSort[level_]] := readyLevelQ[level]
readyTermQ[constantReference[HoldComplete[_], {levels___}]] := readyLevelsQ[levels]
readyTermQ[_] := False

rememberReady[term_] := (
	If[Length[$readyTerms] > 1000000, $readyTerms = <||>];
	$readyTerms[HoldComplete[term]] = readyCompositeQ[term]
)

readyCompositeQ[application[function_, argument_]] := readyTermQ[function] && readyTermQ[argument]
readyCompositeQ[(lambdaAbstraction | dependentFunctionType)[HoldComplete[_], domain_, body_, binder_]] := readyTermQ[domain] && readyTermQ[body] && readyBinderQ[binder]
readyCompositeQ[localDefinition[HoldComplete[_], type_, value_, body_]] := readyTermQ[type] && readyTermQ[value] && readyTermQ[body]
readyCompositeQ[projection[HoldComplete[_], _Integer, term_]] := readyTermQ[term]
readyCompositeQ[cubicalSystem[{branches___}]] := readyBranchesQ[branches]
readyCompositeQ[_] := False

readyLevelQ[_Integer | levelParameter[HoldComplete[_]] | levelMetavariable[_Integer]] := True
readyLevelQ[levelSuccessor[level_, _Integer]] := readyLevelQ[level]
readyLevelQ[(levelMaximum | levelImpredicativeMaximum)[levels___]] := readyLevelsQ[levels]
readyLevelQ[_] := False

readyLevelsQ[] := True
readyLevelsQ[level_, levels___] := readyLevelQ[level] && readyLevelsQ[levels]

readyBinderQ[_String | {_String, 0 | 1}] := True
readyBinderQ[_] := False

readyBranchesQ[] := True
readyBranchesQ[{face_, term_}, branches___] := readyTermQ[face] && readyTermQ[term] && readyBranchesQ[branches]
readyBranchesQ[___] := False

SetAttributes[{checkedConstruction, constructionPlace, uncomputedPart, describeUncomputed, kernelFunctionQ}, HoldAllComplete]

(* a pattern, as MatchQ and Cases evaluate one, is neither *)
checkedConstruction[head_, parts___] := Replace[HoldComplete @@ {parts}, HoldComplete[computed___] :> (
	Which[
		HoldComplete[computed] =!= HoldComplete[parts],
			recordConstruction[constructionPlace["Uncomputed", head, parts]],
		FreeQ[HoldComplete[parts], $patternHeads],
			$readyTerms[HoldComplete[head[computed]]] = True;
			recordConstruction[constructionPlace["Data", head, parts]],
		True,
			$readyTerms[HoldComplete[head[computed]]] = True
	];
	head[computed]
)]

$patternHeads = _Pattern | _Blank | _BlankSequence | _BlankNullSequence | _Alternatives | _Condition | _PatternTest | _Optional | _Verbatim | _Except | _HoldPattern

recordConstruction[place_] := $termConstructionSites[place] = Lookup[$termConstructionSites, Key[place], 0] + 1

constructionPlace[kind_, head_, parts___] := {
	kind,
	SymbolName[Unevaluated[head]],
	uncomputedPart[parts],
	With[{functions = Select[Stack[], kernelFunctionQ]}, Take[functions, -Min[3, Length[functions]]]]
}

kernelFunctionQ[function_Symbol] := StringStartsQ[Context[Unevaluated[function]], "WolframInstitute`TypeTheory`"] &&
	! MemberQ[Join[$compositeHeads, {checkedConstruction, constructionPlace, recordConstruction, uncomputedPart, describeUncomputed, kernelFunctionQ}], Unevaluated[function]]
kernelFunctionQ[_] := False

(* the first part left to compute, looked for inside composites, leaves and lists, named by its head *)
uncomputedPart[parts___] := FirstCase[List @@ (describeUncomputed /@ HoldComplete[parts]), _String, "none"]

describeUncomputed[part_] := Replace[HoldComplete[part], {
	HoldComplete[ready_] /; readyTermQ[ready] || readyBinderQ[ready] || readyLevelQ[ready] :> None,
	HoldComplete[HoldComplete[_] | _Integer | _String] :> None,
	HoldComplete[symbol_Symbol] :> "symbol " <> SymbolName[Unevaluated[symbol]],
	HoldComplete[(application | lambdaAbstraction | dependentFunctionType | localDefinition | projection | cubicalSystem | universeSort | constantReference | levelSuccessor | levelMaximum | levelImpredicativeMaximum | List)[inner___]] :>
		uncomputedPart[inner],
	HoldComplete[(head_Symbol)[___]] :> "call " <> SymbolName[Unevaluated[head]],
	HoldComplete[(table_Association)[key_]] :> "lookup in an Association of " <> ToString[Length[table]] <> " keys, the first " <>
		ToString[Short[Take[Keys[table], UpTo[2]], 1], InputForm] <> ", at a " <> ToString[Head[Unevaluated[key]]],
	HoldComplete[(head_)[___]] :> "call of a " <> ToString[Head[Unevaluated[head]]],
	_ :> "call"
}]
