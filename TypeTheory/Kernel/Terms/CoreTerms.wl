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
PackageScoped[withHashCons]
PackageScoped[withFreshHashCons]
PackageScoped[instantiateBoundVariable]
PackageScoped[instantiateBoundVariables]
PackageScoped[instantiateBoundVariablesProjecting]
PackageScoped[abstractFreeVariable]
PackageScoped[abstractFreeVariables]
PackageScoped[boundVariableOccursQ]
PackageScoped[instantiateUniverseParameters]
PackageScoped[$universeInstantiationCache]
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
withHashCons::usage = "withHashCons[body] evaluates body with an active hash-consing table for term rebuilding, reusing any enclosing table."
withFreshHashCons::usage = "withFreshHashCons[body] evaluates body with a fresh hash-consing table for term rebuilding."
instantiateBoundVariable::usage = "instantiateBoundVariable[body, value] replaces the variable bound just outside body by value."
instantiateBoundVariables::usage = "instantiateBoundVariables[body, {value1, ..., valuek}] replaces the k variables bound just outside body by the values at once, the innermost by valuek."
instantiateBoundVariablesProjecting::usage = "instantiateBoundVariablesProjecting[body, values, fields] replaces the variables as instantiateBoundVariables[body, values] does, and each projection of a replaced variable whose entry of fields, aligned with values, is {HoldComplete[structure], {field1, ...}} by its field: the entry None leaves the variable's projections to be replaced as any other occurrence.\n\
instantiateBoundVariablesProjecting[body, values, fields, fold] gives fold of each application of a constant to two literals that the substitution builds, in its place."
abstractFreeVariable::usage = "abstractFreeVariable[term, id] replaces freeVariable[id] by a bound variable, ready to be wrapped in a binder."
abstractFreeVariables::usage = "abstractFreeVariables[term, {id, ...}] replaces each freeVariable[id] by the bound variable of a binder for it, the last id the innermost, \
ready to be wrapped in those binders: what abstracting the ids one at a time, the last first, gives, in one walk of the term."
boundVariableOccursQ::usage = "boundVariableOccursQ[body, index] gives True if body refers to boundVariable[index] counted from its own top."
instantiateUniverseParameters::usage = "instantiateUniverseParameters[term, {u, ...}, {level, ...}] replaces each universe parameter u by its level."
$universeInstantiationCache::usage = "$universeInstantiationCache is the Association of universe instantiations remembered while the kernel checks a declaration, or None."
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


(* Bottom-up integer-ID hash-consing for term-rebuilding walks (lifting, substitution, abstraction).
   When two distinct input subterms (for instance at different binder depths) collapse to structurally
   identical outputs, memoization on {input, depth} alone allocates two distinct expression pointers;
   a later Association lookup (such as occursQ) then hits the same hash bucket with different pointers
   and falls back to unmemoized structural SameQ over the expanded tree, which is exponential on shared
   DAGs. Keying each rebuilt node by its tag and integer child IDs guarantees that structurally equal
   subterms share one canonical pointer, with O(1) integer-tuple keys and zero structural SameQ on
   composite terms. *)
$hashConsTable = None
$hashConsLeaves = None
$hashConsInterned = None
$hashConsNextIdentifier = 0

SetAttributes[withHashCons, HoldFirst]
withHashCons[body_] := If[ AssociationQ[$hashConsTable],
	body,
	Block[{$hashConsTable = <||>, $hashConsLeaves = <||>, $hashConsNextIdentifier = 0}, body]
]

SetAttributes[withFreshHashCons, HoldFirst]
withFreshHashCons[body_] := Block[{$hashConsTable = <||>, $hashConsLeaves = <||>, $hashConsNextIdentifier = 0}, body]

hashConsLeafPair[leaf_] := Lookup[$hashConsLeaves, Key[leaf], $hashConsLeaves[leaf] = {leaf, ++$hashConsNextIdentifier}]

hashConsRegister[key_, expression_] := $hashConsTable[key] = {expression, ++$hashConsNextIdentifier}

hashConsApplication[{functionExpression_, functionId_}, {argumentExpression_, argumentId_}] := Lookup[
	$hashConsTable,
	Key[{1, functionId, argumentId}],
	hashConsRegister[{1, functionId, argumentId}, Construct[application, functionExpression, argumentExpression]]
]

hashConsLambda[name_, {domainExpression_, domainId_}, {bodyExpression_, bodyId_}, binder_] := Lookup[
	$hashConsTable,
	Key[{2, name, domainId, bodyId, binder}],
	hashConsRegister[{2, name, domainId, bodyId, binder}, Construct[lambdaAbstraction, name, domainExpression, bodyExpression, binder]]
]

hashConsDependentFunction[name_, {domainExpression_, domainId_}, {codomainExpression_, codomainId_}, binder_] := Lookup[
	$hashConsTable,
	Key[{3, name, domainId, codomainId, binder}],
	hashConsRegister[{3, name, domainId, codomainId, binder}, Construct[dependentFunctionType, name, domainExpression, codomainExpression, binder]]
]

hashConsLocalDefinition[name_, {typeExpression_, typeId_}, {valueExpression_, valueId_}, {bodyExpression_, bodyId_}] := Lookup[
	$hashConsTable,
	Key[{4, name, typeId, valueId, bodyId}],
	hashConsRegister[{4, name, typeId, valueId, bodyId}, Construct[localDefinition, name, typeExpression, valueExpression, bodyExpression]]
]

hashConsProjection[structure_, index_, {innerExpression_, innerId_}] := Lookup[
	$hashConsTable,
	Key[{5, structure, index, innerId}],
	hashConsRegister[{5, structure, index, innerId}, Construct[projection, structure, index, innerExpression]]
]

hashConsCubical[branchPairs_List] := hashConsCubicalKey[Map[Last, branchPairs, {2}], Map[First, branchPairs, {2}]]
hashConsCubicalKey[branchIds_List, branchExpressions_List] := Lookup[
	$hashConsTable,
	Key[{6, branchIds}],
	hashConsRegister[{6, branchIds}, Construct[cubicalSystem, branchExpressions]]
]

(* Intern an unchanged subterm into the active hash-cons table so that any rebuilt subterm structurally
   equal to it (for example a shifted bound variable matching an unchanged inner one) shares its pointer.
   $hashConsInterned is scoped per top-level call and keyed ONLY by input subterms (never populated by
   hashConsRegister with newly built output terms), so an unchanged input subterm never collides with a
   structurally equal rebuilt term in $hashConsInterned. When every child of an unchanged composite kept
   its original pointer and no canonical entry exists yet, the original term itself is registered. *)
hashConsInternPair[term : (_boundVariable | _freeVariable | _metavariable | _universeSort | _constantReference | _naturalLiteral | _intervalUniverse)] :=
	hashConsLeafPair[term]
hashConsInternPair[term_] := Take[hashConsInternTracked[term], 2]

hashConsInternTracked[term : (_boundVariable | _freeVariable | _metavariable | _universeSort | _constantReference | _naturalLiteral | _intervalUniverse)] :=
	hashConsInternLeafAt[Lookup[$hashConsLeaves, Key[term], None], term]
hashConsInternTracked[term_] := Lookup[$hashConsInterned, Key[term], $hashConsInterned[term] = hashConsInternComposite[term]]

hashConsInternLeafAt[None, leaf_] := Append[$hashConsLeaves[leaf] = {leaf, ++$hashConsNextIdentifier}, True]
hashConsInternLeafAt[existing_List, _] := Append[existing, False]

hashConsInternComposite[term : application[function_, argument_]] :=
	hashConsInternApplication[term, hashConsInternTracked[function], hashConsInternTracked[argument]]
hashConsInternComposite[term : lambdaAbstraction[name_, domain_, body_, binder_]] :=
	hashConsInternLambda[term, name, hashConsInternTracked[domain], hashConsInternTracked[body], binder]
hashConsInternComposite[term : dependentFunctionType[name_, domain_, codomain_, binder_]] :=
	hashConsInternDependentFunction[term, name, hashConsInternTracked[domain], hashConsInternTracked[codomain], binder]
hashConsInternComposite[term : localDefinition[name_, type_, value_, body_]] :=
	hashConsInternLocalDefinition[term, name, hashConsInternTracked[type], hashConsInternTracked[value], hashConsInternTracked[body]]
hashConsInternComposite[term : projection[structure_, index_, inner_]] :=
	hashConsInternProjection[term, structure, index, hashConsInternTracked[inner]]
hashConsInternComposite[term : cubicalSystem[branches_List]] :=
	hashConsInternCubical[term, Map[hashConsInternTracked, branches, {2}]]
hashConsInternComposite[term_] := hashConsInternLeafAt[Lookup[$hashConsLeaves, Key[term], None], term]

hashConsInternApplication[term_, {functionExpression_, functionId_, functionPreserved_}, {argumentExpression_, argumentId_, argumentPreserved_}] :=
	hashConsInternApplicationAt[Lookup[$hashConsTable, Key[{1, functionId, argumentId}], None], {1, functionId, argumentId}, term, functionPreserved && argumentPreserved, functionExpression, argumentExpression]
hashConsInternApplicationAt[None, key_, term_, True, _, _] := Append[$hashConsTable[key] = {term, ++$hashConsNextIdentifier}, True]
hashConsInternApplicationAt[None, key_, _, False, functionExpression_, argumentExpression_] :=
	Append[$hashConsTable[key] = {Construct[application, functionExpression, argumentExpression], ++$hashConsNextIdentifier}, False]
hashConsInternApplicationAt[existing_List, _, _, _, _, _] := Append[existing, False]

hashConsInternLambda[term_, name_, {domainExpression_, domainId_, domainPreserved_}, {bodyExpression_, bodyId_, bodyPreserved_}, binder_] :=
	hashConsInternLambdaAt[Lookup[$hashConsTable, Key[{2, name, domainId, bodyId, binder}], None], {2, name, domainId, bodyId, binder}, term, domainPreserved && bodyPreserved, name, domainExpression, bodyExpression, binder]
hashConsInternLambdaAt[None, key_, term_, True, _, _, _, _] := Append[$hashConsTable[key] = {term, ++$hashConsNextIdentifier}, True]
hashConsInternLambdaAt[None, key_, _, False, name_, domainExpression_, bodyExpression_, binder_] :=
	Append[$hashConsTable[key] = {Construct[lambdaAbstraction, name, domainExpression, bodyExpression, binder], ++$hashConsNextIdentifier}, False]
hashConsInternLambdaAt[existing_List, _, _, _, _, _, _, _] := Append[existing, False]

hashConsInternDependentFunction[term_, name_, {domainExpression_, domainId_, domainPreserved_}, {codomainExpression_, codomainId_, codomainPreserved_}, binder_] :=
	hashConsInternDependentFunctionAt[Lookup[$hashConsTable, Key[{3, name, domainId, codomainId, binder}], None], {3, name, domainId, codomainId, binder}, term, domainPreserved && codomainPreserved, name, domainExpression, codomainExpression, binder]
hashConsInternDependentFunctionAt[None, key_, term_, True, _, _, _, _] := Append[$hashConsTable[key] = {term, ++$hashConsNextIdentifier}, True]
hashConsInternDependentFunctionAt[None, key_, _, False, name_, domainExpression_, codomainExpression_, binder_] :=
	Append[$hashConsTable[key] = {Construct[dependentFunctionType, name, domainExpression, codomainExpression, binder], ++$hashConsNextIdentifier}, False]
hashConsInternDependentFunctionAt[existing_List, _, _, _, _, _, _, _] := Append[existing, False]

hashConsInternLocalDefinition[term_, name_, {typeExpression_, typeId_, typePreserved_}, {valueExpression_, valueId_, valuePreserved_}, {bodyExpression_, bodyId_, bodyPreserved_}] :=
	hashConsInternLocalDefinitionAt[Lookup[$hashConsTable, Key[{4, name, typeId, valueId, bodyId}], None], {4, name, typeId, valueId, bodyId}, term, typePreserved && valuePreserved && bodyPreserved, name, typeExpression, valueExpression, bodyExpression]
hashConsInternLocalDefinitionAt[None, key_, term_, True, _, _, _, _] := Append[$hashConsTable[key] = {term, ++$hashConsNextIdentifier}, True]
hashConsInternLocalDefinitionAt[None, key_, _, False, name_, typeExpression_, valueExpression_, bodyExpression_] :=
	Append[$hashConsTable[key] = {Construct[localDefinition, name, typeExpression, valueExpression, bodyExpression], ++$hashConsNextIdentifier}, False]
hashConsInternLocalDefinitionAt[existing_List, _, _, _, _, _, _, _] := Append[existing, False]

hashConsInternProjection[term_, structure_, index_, {innerExpression_, innerId_, innerPreserved_}] :=
	hashConsInternProjectionAt[Lookup[$hashConsTable, Key[{5, structure, index, innerId}], None], {5, structure, index, innerId}, term, innerPreserved, structure, index, innerExpression]
hashConsInternProjectionAt[None, key_, term_, True, _, _, _] := Append[$hashConsTable[key] = {term, ++$hashConsNextIdentifier}, True]
hashConsInternProjectionAt[None, key_, _, False, structure_, index_, innerExpression_] :=
	Append[$hashConsTable[key] = {Construct[projection, structure, index, innerExpression], ++$hashConsNextIdentifier}, False]
hashConsInternProjectionAt[existing_List, _, _, _, _, _, _] := Append[existing, False]

hashConsEntryIdentifier[entry_] := Extract[entry, 2]

hashConsInternCubical[term_, branchTriples_List] := hashConsInternCubicalKey[
	term,
	{6, Map[hashConsEntryIdentifier, branchTriples, {2}]},
	AllTrue[Flatten[branchTriples, 1], Last],
	Map[First, branchTriples, {2}]
]
hashConsInternCubicalKey[term_, key_, preserved_, branchExpressions_] :=
	hashConsInternCubicalAt[Lookup[$hashConsTable, Key[key], None], key, term, preserved, branchExpressions]
hashConsInternCubicalAt[None, key_, term_, True, _] := Append[$hashConsTable[key] = {term, ++$hashConsNextIdentifier}, True]
hashConsInternCubicalAt[None, key_, _, False, branchExpressions_] :=
	Append[$hashConsTable[key] = {Construct[cubicalSystem, branchExpressions], ++$hashConsNextIdentifier}, False]
hashConsInternCubicalAt[existing_List, _, _, _, _] := Append[existing, False]


liftBoundVariables[term_, 0, _] := term
liftBoundVariables[term_, amount_, cutoff_] := withRangeCache[
	If[ looseBoundRange[term] <= cutoff,
		term,
		withHashCons[First[liftBoundVariablesPair[term, amount, cutoff]]]
	]
]

liftBoundVariablesPair[term_, 0, _] := Block[{$hashConsInterned = <||>}, hashConsInternPair[term]]
liftBoundVariablesPair[term_, amount_, cutoff_] := Block[{$hashConsInterned = <||>},
	If[ looseBoundRange[term] <= cutoff,
		hashConsInternPair[term],
		Block[{$liftMemo = <||>}, liftShared[term, amount, cutoff]]
	]
]

liftShared[term_, amount_, cutoff_] := If[ looseBoundRange[term] <= cutoff,
	hashConsInternPair[term],
	Lookup[$liftMemo, Key[{term, cutoff}], $liftMemo[{term, cutoff}] = liftNode[term, amount, cutoff]]
]

liftNode[boundVariable[index_], amount_, cutoff_] := hashConsLeafPair[boundVariable[If[index >= cutoff, index + amount, index]]]
liftNode[application[function_, argument_], amount_, cutoff_] :=
	hashConsApplication[liftShared[function, amount, cutoff], liftShared[argument, amount, cutoff]]
liftNode[lambdaAbstraction[name_, domain_, body_, binder_], amount_, cutoff_] :=
	hashConsLambda[name, liftShared[domain, amount, cutoff], liftShared[body, amount, cutoff + 1], binder]
liftNode[dependentFunctionType[name_, domain_, codomain_, binder_], amount_, cutoff_] :=
	hashConsDependentFunction[name, liftShared[domain, amount, cutoff], liftShared[codomain, amount, cutoff + 1], binder]
liftNode[localDefinition[name_, type_, value_, body_], amount_, cutoff_] :=
	hashConsLocalDefinition[name, liftShared[type, amount, cutoff], liftShared[value, amount, cutoff], liftShared[body, amount, cutoff + 1]]
liftNode[projection[structure_, index_, term_], amount_, cutoff_] :=
	hashConsProjection[structure, index, liftShared[term, amount, cutoff]]
liftNode[cubicalSystem[branches_List], amount_, cutoff_] :=
	hashConsCubical[Map[liftBranchPart[amount, cutoff], branches, {2}]]
liftNode[term_, _, _] := hashConsInternPair[term]

liftBranchPart[amount_, cutoff_][part_] := liftShared[part, amount, cutoff]


instantiateBoundVariable[body_, value_] := instantiateBoundVariables[body, {value}]

(* the variables bound just outside body, innermost last, replaced at once by values, as beta reduction of a
   function of several arguments needs: body refers to the last value as boundVariable[0] *)
instantiateBoundVariables[body_, {}] := body
instantiateBoundVariables[body_, values_List] := withRangeCache[
	If[ looseBoundRange[body] == 0,
		body,
		withHashCons[Block[{$substitutionMemo = <||>, $hashConsInterned = <||>, $substitutedFields = {}}, First[substituteShared[body, Reverse[values], 0]]]]
	]
]

(* Beta reduction with each projection of a value that is a structure's constructor applied in full taken at once:
   projection i of the constructor applied to its parameters and fields reduces to field i, by the kernel's own rule
   for projections, so the reduct is definitionally equal to the one of instantiateBoundVariables and of the same type.
   Taken later, the projection would carry the whole value, its other fields with it, into every place the variable is
   projected, and a term that shares such values level after level grows in its tree size, which hashing and walking a
   term cost, though not in memory. Any term shared many times still costs its tree size so; a traversal that visits
   each shared subterm once is the general remedy. *)
$substitutedFields = {}

instantiateBoundVariablesProjecting[body_, values_List, fields_List] := instantiateBoundVariablesProjecting[body, values, fields, None]
instantiateBoundVariablesProjecting[body_, values_List, fields_List, fold_] := withRangeCache[
	If[ looseBoundRange[body] == 0,
		body,
		withHashCons[Block[{$substitutionMemo = <||>, $hashConsInterned = <||>, $substitutedFields = Reverse[fields], $literalFold = fold}, First[substituteShared[body, Reverse[values], 0]]]]
	]
]

(* An application of a constant to two literals that this substitution builds is what fold gives of it, where the caller
   gives a fold: beta reduction gives the kernel's computation of a registered operation on literals, so a sum of
   products of literals in a field is a literal as soon as the field exists, and no later reduction carries it unreduced,
   shared, to be read again at each use. $literalFold is the fold of the substitution in progress, set here from the
   argument and nowhere else, as $substitutedFields is; with None, as every other substitution has it, substitution is
   purely syntactic. *)
$literalFold = None
foldedApplicationPair[pair : {node : application[application[_constantReference, _naturalLiteral], _naturalLiteral], _}] /; $literalFold =!= None :=
	Block[{$hashConsInterned = <||>}, hashConsInternPair[$literalFold[node]]]
foldedApplicationPair[pair_] := pair

(* values innermost first: boundVariable[depth + j] is the value at j + 1 *)
substituteShared[term_, values_, depth_] := If[ looseBoundRange[term] <= depth,
	hashConsInternPair[term],
	Lookup[$substitutionMemo, Key[{term, depth}], $substitutionMemo[{term, depth}] = substituteNode[term, values, depth]]
]

substituteNode[boundVariable[index_], values_, depth_] := Which[
	index < depth,
		hashConsLeafPair[boundVariable[index]],
	index < depth + Length[values],
		liftBoundVariablesPair[values[[index - depth + 1]], depth, 0],
	True,
		hashConsLeafPair[boundVariable[index - Length[values]]]
]
substituteNode[application[function_, argument_], values_, depth_] :=
	foldedApplicationPair[hashConsApplication[substituteShared[function, values, depth], substituteShared[argument, values, depth]]]
substituteNode[lambdaAbstraction[name_, domain_, body_, binder_], values_, depth_] :=
	hashConsLambda[name, substituteShared[domain, values, depth], substituteShared[body, values, depth + 1], binder]
substituteNode[dependentFunctionType[name_, domain_, codomain_, binder_], values_, depth_] :=
	hashConsDependentFunction[name, substituteShared[domain, values, depth], substituteShared[codomain, values, depth + 1], binder]
substituteNode[localDefinition[name_, type_, definedValue_, body_], values_, depth_] :=
	hashConsLocalDefinition[name, substituteShared[type, values, depth], substituteShared[definedValue, values, depth], substituteShared[body, values, depth + 1]]
substituteNode[projection[structure_, index_, term_], values_, depth_] :=
	substituteProjectionResult[structure, index, term, values, depth, substitutedFieldPair[structure, index, term, depth]]
substituteNode[cubicalSystem[branches_List], values_, depth_] :=
	hashConsCubical[Map[substituteBranchPart[values, depth], branches, {2}]]
substituteNode[term_, _, _] := hashConsInternPair[term]

substituteProjectionResult[structure_, index_, term_, values_, depth_, None] :=
	hashConsProjection[structure, index, substituteShared[term, values, depth]]
substituteProjectionResult[_, _, _, _, _, fieldPair_] := fieldPair

substituteBranchPart[values_, depth_][part_] := substituteShared[part, values, depth]

(* the field of a projection of a replaced variable whose value is a constructor applied in full, lifted as the value
   would be; None for any other projection *)
substitutedFieldPair[structure_, index_Integer, boundVariable[k_Integer], depth_] /; depth <= k < depth + Length[$substitutedFields] :=
	Replace[Extract[$substitutedFields, k - depth + 1], {
		{structure, fields_List} /; 0 <= index < Length[fields] :> liftBoundVariablesPair[Extract[fields, index + 1], depth, 0],
		_ -> None
	}]
substitutedFieldPair[___] := None


abstractFreeVariable[term_, id_] := withHashCons[Block[{$abstractionMemo = <||>, $hashConsInterned = <||>}, First[abstractShared[term, id, 0]]]]

abstractFreeVariables[term_, {}] := term
abstractFreeVariables[term_, ids_List] := withHashCons[
	Block[{$abstractionMemo = <||>, $hashConsInterned = <||>, $abstractionIndices = AssociationThread[ids, Reverse[Range[Length[ids]] - 1]]},
		First[abstractManyShared[term, 0]]
	]
]

abstractManyShared[term : (_boundVariable | _universeSort | _constantReference | _naturalLiteral | _metavariable | _intervalUniverse), _] := hashConsLeafPair[term]
abstractManyShared[term_, depth_] := Lookup[$abstractionMemo, Key[{term, depth}], $abstractionMemo[{term, depth}] = abstractManyAt[term, depth]]

abstractManyAt[freeVariable[id_], depth_] :=
	hashConsLeafPair[Replace[Lookup[$abstractionIndices, Key[id], None], {None -> freeVariable[id], index_Integer :> boundVariable[index + depth]}]]
abstractManyAt[application[function_, argument_], depth_] :=
	hashConsApplication[abstractManyShared[function, depth], abstractManyShared[argument, depth]]
abstractManyAt[lambdaAbstraction[name_, domain_, body_, binder_], depth_] :=
	hashConsLambda[name, abstractManyShared[domain, depth], abstractManyShared[body, depth + 1], binder]
abstractManyAt[dependentFunctionType[name_, domain_, codomain_, binder_], depth_] :=
	hashConsDependentFunction[name, abstractManyShared[domain, depth], abstractManyShared[codomain, depth + 1], binder]
abstractManyAt[localDefinition[name_, type_, value_, body_], depth_] :=
	hashConsLocalDefinition[name, abstractManyShared[type, depth], abstractManyShared[value, depth], abstractManyShared[body, depth + 1]]
abstractManyAt[projection[structure_, index_, term_], depth_] :=
	hashConsProjection[structure, index, abstractManyShared[term, depth]]
abstractManyAt[cubicalSystem[branches_List], depth_] :=
	hashConsCubical[Map[abstractManyBranchPart[depth], branches, {2}]]
abstractManyAt[term_, _] := hashConsInternPair[term]

abstractManyBranchPart[depth_][part_] := abstractManyShared[part, depth]

abstractShared[term : (_boundVariable | _universeSort | _constantReference | _naturalLiteral | _metavariable | _intervalUniverse), _, _] := hashConsLeafPair[term]
abstractShared[term_, id_, depth_] := Lookup[$abstractionMemo, Key[{term, depth}], $abstractionMemo[{term, depth}] = abstractAt[term, id, depth]]

abstractAt[freeVariable[id_], id_, depth_] := hashConsLeafPair[boundVariable[depth]]
abstractAt[application[function_, argument_], id_, depth_] :=
	hashConsApplication[abstractShared[function, id, depth], abstractShared[argument, id, depth]]
abstractAt[lambdaAbstraction[name_, domain_, body_, binder_], id_, depth_] :=
	hashConsLambda[name, abstractShared[domain, id, depth], abstractShared[body, id, depth + 1], binder]
abstractAt[dependentFunctionType[name_, domain_, codomain_, binder_], id_, depth_] :=
	hashConsDependentFunction[name, abstractShared[domain, id, depth], abstractShared[codomain, id, depth + 1], binder]
abstractAt[localDefinition[name_, type_, value_, body_], id_, depth_] :=
	hashConsLocalDefinition[name, abstractShared[type, id, depth], abstractShared[value, id, depth], abstractShared[body, id, depth + 1]]
abstractAt[projection[structure_, index_, term_], id_, depth_] :=
	hashConsProjection[structure, index, abstractShared[term, id, depth]]
abstractAt[cubicalSystem[branches_List], id_, depth_] :=
	hashConsCubical[Map[abstractBranchPart[id, depth], branches, {2}]]
abstractAt[term_, _, _] := hashConsInternPair[term]

abstractBranchPart[id_, depth_][part_] := abstractShared[part, id, depth]


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


(* A check instantiates the same constant's type, value or recursor rule at the same levels again and again, one
   reduction step after another, and each is a term the environment's record holds, so a check remembers them. *)
instantiateUniverseParameters[term_, {}, {}] := term
instantiateUniverseParameters[term_, parameters_List, levels_List] /; Length[parameters] == Length[levels] := If[ AssociationQ[$universeInstantiationCache],
	Lookup[$universeInstantiationCache, Key[{term, parameters, levels}], $universeInstantiationCache[{term, parameters, levels}] = universesReplaced[term, parameters, levels]],
	universesReplaced[term, parameters, levels]
]

$universeInstantiationCache = None

universesReplaced[term_, parameters_, levels_] := levelRulesApplied[term, Thread[(levelParameter /@ parameters) -> levels]]

levelRulesApplied[term_, rules_] := term /. {
	universeSort[level_] :> With[{instantiated = normalizeLevel[level /. rules]}, universeSort[instantiated] /; True],
	constantReference[name_, constantLevels_List] :> With[{instantiated = normalizeLevel /@ (constantLevels /. rules)}, constantReference[name, instantiated] /; True]
}


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
   then b = 0 gives 0, and b >= 1 gives max a b = b. So imax 1 u is u. *)
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

(* a symbol, not an expression with the head Symbol, as Symbol[] on the stack of a display *)
kernelFunctionQ[function_Symbol] /; AtomQ[Unevaluated[function]] := StringStartsQ[Context[Unevaluated[function]], "WolframInstitute`TypeTheory`"] &&
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
