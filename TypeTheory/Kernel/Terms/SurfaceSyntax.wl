(* ::Package:: *)

(*
Surface terms: the type theory written with built-in symbols, and its conversion to and from core terms.

A surface term is an ordinary Wolfram Language expression, kept unevaluated:

	Function[{Typed[x, A], ...}, b]                   a function
	ForAll[{Typed[x, A], ...}, B]                     a dependent function type, or a universal statement
	Implies[A, B], TypeSpecifier[{A, ...} -> B]       a function type whose result does not depend on the argument;
	A -> B, {A, ...} -> B                             the same, written as a rule
	TypedImplicit[x, A]                               an implicit binder, the same as Annotation[Typed[x, A], "Implicit"]
	Annotation[Typed[x, A], kind]                     a binder of kind "StrictImplicit" or "InstanceImplicit"
	Typed[x, A, q], TypedImplicit[x, A, q]            a binder of quantity q, 0, 1 or Infinity, under rules with quantities
	Exists[{Typed[x, A]}, p]                          Exists applied to Function[{Typed[x, A]}, p]
	Typed[e, A]                                       e, checked against A
	With[{x = v}, b]                                  b with x standing for v
	RightTee[{Typed[x, A], ...}, B]                   the same as ForAll: a goal, its hypotheses and its conclusion
	TypeUniverse[level]                               Sort level: TypeUniverse[0] is Prop, TypeUniverse[1] is Type
	f[a, b]                                           application, curried
	Subscript[c, level, ...]                          the constant c at explicit universe levels
	n                                                 a natural number literal

Every other symbol is a bound variable or a declared constant; the prelude's constants include the
built-in symbols True, False, Not, And, Or, Equal, Exists, NonNegativeIntegers and Plus, so a term reads
like ordinary mathematics. Plus and Times are Flat, so a sum of more than two terms is read as a left
fold.

TypeTheoryTerm[term, environment] holds a surface term (it has the HoldFirst attribute), so built-in
functions never evaluate it: ForAll[Typed[x, A], B] on its own evaluates to B, because a quantifier whose
variable does not occur is dropped. The environment, evaluated, says where its constants come from.

Two more forms make a term exact, as the Lean bridge and Normal[environment] need:

	Construct[f, a, b]                                f applied to a and b with no implicit arguments filled in
	t[[i]]                                            field i of t, of a structure type

Held terms are turned into syntax trees first, so the rest of the code never risks evaluating them:

	syntaxSymbol[HoldComplete[symbol]]
	syntaxInteger[n], syntaxString[text], syntaxOther[HoldComplete[expr]]
	syntaxApplication[headSyntax, {argumentSyntax, ...}]

Delaboration turns a core term back into a syntax tree, opening each binder with a fresh free variable
and naming it with its binder's name, or a numbered variant of that name, as a1, when a variable in
scope already shows it; a binder with no name is called x. For display it drops
implicit arguments; with $exactReadBack it writes every argument, using Construct where an implicit one
would otherwise be filled in again, and every universe level with Subscript, so the term elaborates back
to itself.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryTerm]
PackageExported[TypeUniverse]
PackageExported[ImpredicativeMaximum]
PackageExported[InductiveRecursor]
PackageExported[TypedImplicit]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[syntaxSymbol]
PackageScoped[syntaxInteger]
PackageScoped[syntaxString]
PackageScoped[syntaxOther]
PackageScoped[syntaxApplication]
PackageScoped[toSyntax]
PackageScoped[heldFromSyntax]
PackageScoped[syntaxHead]
PackageScoped[listElements]
PackageScoped[delaborate]
PackageScoped[displayCoreTerm]
PackageScoped[coreToTypeTheoryTerm]
PackageScoped[$exactReadBack]
PackageScoped[nameSyntax]
PackageScoped[displayedName]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryTerm::usage = "TypeTheoryTerm[term, environment] represents a term of the type theory in the TypeTheoryEnvironment environment, \
written with built-in symbols such as Function, Typed, ForAll, Implies, Equal and Plus, and kept unevaluated.\n\
TypeTheoryTerm[term] is a term in the default environment, $TypeTheoryEnvironment: the prelude, unless SetTypeTheoryEnvironment set another.\n\
TypeOf[TypeTheoryTerm[term, environment]] gives its type; TypeOf[TypeTheoryTerm[term], environment] gives its type in environment."
TypeUniverse::usage = "TypeUniverse[level] is the universe at level: TypeUniverse[0] is Prop, the universe of propositions, and TypeUniverse[1] is \
Type. level is a non-negative integer, a universe parameter, level + k, Max[level1, level2] or ImpredicativeMaximum[level1, level2]."
ImpredicativeMaximum::usage = "ImpredicativeMaximum[level1, level2] is the universe level 0 when level2 is 0 and Max[level1, level2] otherwise: the \
level of a function type from TypeUniverse[level1] to TypeUniverse[level2]."
InductiveRecursor::usage = "InductiveRecursor[type] is the recursor of the inductive type type, generated when the type is declared. Its arguments \
are the type's parameters (implicit), a motive, one minor premise per constructor, the indices (implicit) and the major premise."
TypedImplicit::usage = "TypedImplicit[x, type] is an implicit binder: a variable x of type type that is found from the other arguments rather than \
written. It is the same as Annotation[Typed[x, type], \"Implicit\"]."

syntaxSymbol::usage = "syntaxSymbol[HoldComplete[symbol]] is a symbol in a syntax tree."
syntaxInteger::usage = "syntaxInteger[n] is an integer in a syntax tree."
syntaxString::usage = "syntaxString[text] is a string in a syntax tree."
syntaxOther::usage = "syntaxOther[HoldComplete[expr]] is any other atom in a syntax tree."
syntaxApplication::usage = "syntaxApplication[head, {argument, ...}] is a compound expression in a syntax tree."
toSyntax::usage = "toSyntax[expr] gives the syntax tree of expr without evaluating it."
heldFromSyntax::usage = "heldFromSyntax[syntax] gives HoldComplete[expr] for the expression syntax describes."
syntaxHead::usage = "syntaxHead[symbol, {argument, ...}] gives the syntax tree of symbol applied to the argument syntax trees."
listElements::usage = "listElements[syntax] gives the elements of the syntax tree of a list, or {syntax} for any other syntax tree."
delaborate::usage = "delaborate[environment, context, term] gives a syntax tree for the core term in the local context."
displayCoreTerm::usage = "displayCoreTerm[environment, context, term] gives the core term as a TypeTheoryTerm, or the core term itself if it cannot be displayed."
coreToTypeTheoryTerm::usage = "coreToTypeTheoryTerm[environment, context, term] gives the core term as a TypeTheoryTerm in environment."
$exactReadBack::usage = "$exactReadBack is True while core terms are read back exactly, with every argument and universe level written out."
nameSyntax::usage = "nameSyntax[HoldComplete[name]] gives the syntax tree of a binder or constant name, a symbol or a string."
displayedName::usage = "displayedName[HoldComplete[name]] gives the name a symbol or string shows as, without its context."


(* ::Section:: *)
(*Function Definitions*)


SetAttributes[TypeTheoryTerm, HoldFirst]

$exactReadBack = False


(* ::Subsection:: *)
(*Syntax trees*)


SetAttributes[toSyntax, HoldAllComplete]
toSyntax[TypeTheoryTerm[term_, ___]] := toSyntax[term]
toSyntax[symbol_Symbol] := syntaxSymbol[HoldComplete[symbol]]
toSyntax[n_Integer] := syntaxInteger[n]
toSyntax[Rational[numerator_, denominator_]] := syntaxHead[Times, {syntaxInteger[numerator], syntaxHead[Power, {syntaxInteger[denominator], syntaxInteger[-1]}]}]
toSyntax[text_String] := syntaxString[text]
toSyntax[head_[arguments___]] := syntaxApplication[toSyntax[head], toSyntax /@ Unevaluated[{arguments}]]
toSyntax[other_] := syntaxOther[HoldComplete[other]]

heldFromSyntax[syntaxSymbol[held_HoldComplete]] := held
heldFromSyntax[syntaxInteger[n_]] := HoldComplete[n]
heldFromSyntax[syntaxString[text_]] := HoldComplete[text]
heldFromSyntax[syntaxOther[held_HoldComplete]] := held
heldFromSyntax[syntaxApplication[head_, arguments_List]] := joinHeld[heldFromSyntax[head], heldFromSyntax /@ arguments]

joinHeld[HoldComplete[head_], {}] := HoldComplete[head[]]
joinHeld[HoldComplete[head_], heldArguments_List] := Replace[
	Join[HoldComplete[head], Join @@ heldArguments],
	HoldComplete[function_, arguments___] :> HoldComplete[function[arguments]]
]

SetAttributes[syntaxHead, HoldFirst]
syntaxHead[symbol_Symbol, arguments_List] := syntaxApplication[syntaxSymbol[HoldComplete[symbol]], arguments]

listElements[syntaxApplication[syntaxSymbol[HoldComplete[List]], elements_List]] := elements
listElements[single_] := {single}


(* ::Subsection:: *)
(*Delaboration*)


coreToTypeTheoryTerm[environment_, context_, term_] := TypeTheoryTerm @@ Append[heldFromSyntax[delaborate[environment, context, term]], environment]

displayCoreTerm[environment_, context_, term_] := Replace[
	Quiet @ catchKernelFailure[coreToTypeTheoryTerm[environment, context, term]],
	{display_TypeTheoryTerm :> display, _ :> term}
]


delaborate[environment_, context_, term_] := Replace[term, {
	freeVariable[id_] :> nameSyntax[Lookup[Lookup[context, id, <||>], "Name", HoldComplete[x]]],
	boundVariable[index_] :> syntaxHead[Placeholder, {syntaxString["bound " <> ToString[index]]}],
	metavariable[id_] :> syntaxHead[Placeholder, {syntaxString["?" <> ToString[id]]}],
	universeSort[level_] :> syntaxHead[TypeUniverse, {levelSyntax[level]}],
	naturalLiteral[n_] :> syntaxInteger[n],
	projection[_, index_, structureTerm_] :> syntaxHead[Part, {delaborate[environment, context, structureTerm], syntaxInteger[index + 1]}],
	localDefinition[name_, type_, value_, body_] :> delaborate[environment, context, instantiateBoundVariable[body, value]],
	lambdaAbstraction[___] :> delaborateBinders[environment, context, term, lambdaAbstraction, Function],
	dependentFunctionType[_, domain_, codomain_, "Explicit"] /; ! boundVariableOccursQ[codomain, 0] :>
		delaborateArrow[environment, context, domain, codomain],
	dependentFunctionType[___] :> delaborateBinders[environment, context, term, dependentFunctionType, ForAll],
	_application | _constantReference :> delaborateApplication[environment, context, term],
	cubicalSystem[branches_List] :> syntaxHead[List, Function[branch, syntaxHead[Rule, {faceSyntax[environment, context, First[branch]], delaborate[environment, context, Last[branch]]}]] /@ branches],
	intervalUniverse[] :> syntaxString["IntervalUniverse"],
	_ :> syntaxOther[HoldComplete[term]]
}]

(* a face of a system as conditions on its variables, i == 0 and i == 1, joined by And and Or *)
faceSyntax[environment_, context_, face_] := Replace[Quiet @ catchKernelFailure[intervalForm[environment, context, face]], {
	{} :> syntaxSymbol[HoldComplete[False]],
	{{}} :> syntaxSymbol[HoldComplete[True]],
	form : {__List} :> joinedSyntax[Or, Function[conjunction, joinedSyntax[And, Function[literal,
		syntaxHead[Equal, {nameSyntax[Lookup[Lookup[context, First[literal], <||>], "Name", HoldComplete[x]]], syntaxInteger[Boole[Last[literal]]]}]
	] /@ conjunction]] /@ form],
	_ :> delaborate[environment, context, face]
}]

joinedSyntax[_, {single_}] := single
joinedSyntax[head_, parts_List] := syntaxHead[head, parts]

levelSyntax[n_Integer] := syntaxInteger[n]
levelSyntax[levelParameter[held_]] := nameSyntax[held]
levelSyntax[levelMetavariable[id_]] := syntaxHead[Placeholder, {syntaxString["?u" <> ToString[id]]}]
levelSyntax[levelSuccessor[level_, k_]] := syntaxHead[Plus, {levelSyntax[level], syntaxInteger[k]}]
levelSyntax[levelMaximum[levels___]] := syntaxHead[Max, levelSyntax /@ {levels}]
levelSyntax[levelImpredicativeMaximum[a_, b_]] := syntaxHead[ImpredicativeMaximum, {levelSyntax[a], levelSyntax[b]}]


(* a run of binders of the same kind becomes one Function or ForAll with a list of typed variables *)
delaborateBinders[environment_, context_, term_, head_, displayHead_] := collectBinders[environment, context, term, head, displayHead, {}]

collectBinders[environment_, context_, current : head_[binderName_, domain_, body_, binder_], head_, displayHead_, binders_List] /;
	! (head === dependentFunctionType && arrowBinderQ[current]) := With[
	{id = freshFreeVariable[], name = displayName[context, binderName]},
	collectBinders[
		environment,
		extendContext[context, id, name, domain, binder],
		instantiateBoundVariable[body, freeVariable[id]],
		head,
		displayHead,
		Append[binders, binderSyntax[name, delaborate[environment, context, domain], binder]]
	]
]
collectBinders[environment_, context_, current_, _, displayHead_, binders_List] :=
	syntaxApplication[syntaxSymbol[HoldComplete[displayHead]], {syntaxHead[List, binders], delaborate[environment, context, current]}]

arrowBinderQ[dependentFunctionType[_, _, codomain_, "Explicit"]] := ! boundVariableOccursQ[codomain, 0]
arrowBinderQ[_] := False

binderSyntax[name_, domainSyntax_, "Explicit"] := syntaxHead[Typed, {nameSyntax[name], domainSyntax}]
binderSyntax[name_, domainSyntax_, "Implicit"] := syntaxHead[TypedImplicit, {nameSyntax[name], domainSyntax}]
binderSyntax[name_, domainSyntax_, binder_String] := syntaxHead[Annotation, {syntaxHead[Typed, {nameSyntax[name], domainSyntax}], syntaxString[binder]}]
(* the quantity is the third argument of Typed or TypedImplicit *)
binderSyntax[name_, domainSyntax_, {kind_String, quantity_}] := Replace[binderSyntax[name, domainSyntax, kind], {
	syntaxApplication[head : syntaxSymbol[HoldComplete[Typed | TypedImplicit]], {nameAndType__}] :> syntaxApplication[head, {nameAndType, syntaxInteger[quantity]}],
	syntaxApplication[annotation_, {syntaxApplication[typed_, {nameAndType__}], kindSyntax_}] :> syntaxApplication[annotation, {syntaxApplication[typed, {nameAndType, syntaxInteger[quantity]}], kindSyntax}]
}]

nameSyntax[HoldComplete[name_String]] := syntaxString[name]
nameSyntax[name_HoldComplete] := syntaxSymbol[name]

(* the binder's own name, unless a variable in the context already shows the same name, as a variable
   of the prelude and a user's variable can: then the first numbered variant of it that no variable shows *)
displayName[context_, name_] := With[
	{
		taken = displayedName /@ Lookup[Values[context], "Name", {}],
		base = Replace[name, HoldComplete[Null] -> HoldComplete[x]]
	},
	SelectFirst[
		Prepend[Function[index, numberedName[base, index]] /@ Range[Length[taken] + 1], base],
		Function[candidate, ! MemberQ[taken, displayedName[candidate]]]
	]
]

displayedName[HoldComplete[name_String]] := name
displayedName[HoldComplete[symbol_Symbol]] := SymbolName[Unevaluated[symbol]]
displayedName[_] := None

(* a variant of a symbol lives in the symbol's own context *)
numberedName[HoldComplete[name_String], index_Integer] := HoldComplete @@ {name <> ToString[index]}
numberedName[HoldComplete[symbol_Symbol], index_Integer] :=
	ToExpression[Context[Unevaluated[symbol]] <> SymbolName[Unevaluated[symbol]] <> ToString[index], InputForm, HoldComplete]

(* A -> B: Implies between propositions, TypeSpecifier otherwise *)
delaborateArrow[environment_, context_, domain_, codomain_] := With[{result = liftedCodomain[codomain]},
	If[ propositionTermQ[environment, context, domain] && propositionTermQ[environment, context, result],
		syntaxHead[Implies, {delaborate[environment, context, domain], delaborate[environment, context, result]}],
		syntaxHead[TypeSpecifier, {syntaxHead[Rule, {syntaxHead[List, {delaborate[environment, context, domain]}], delaborate[environment, context, result]}]}]
	]
]

(* the codomain of a non-dependent function type, with its unused bound variable removed *)
liftedCodomain[codomain_] := instantiateBoundVariable[codomain, metavariable[0]]

propositionTermQ[environment_, context_, type_] := TrueQ[Quiet @ catchKernelFailure[
	MatchQ[weakHeadNormalForm[environment, context, inferType[environment, context, type]], universeSort[0]]
]]


(* an application, with its implicit arguments dropped, and Exists written with a binder; read back
   exactly, every argument and level is written out *)
delaborateApplication[environment_, context_, term_] /; TrueQ[$exactReadBack] := With[{spine = applicationSpine[term]},
	exactApplication[environment, context, First[spine], Last[spine]]
]
delaborateApplication[environment_, context_, term_] := With[{spine = applicationSpine[term]},
	Replace[{First[spine], explicitArguments[environment, context, First[spine], Last[spine]]}, {
		{constantReference[HoldComplete[Exists], _], {lambdaAbstraction[name_, domain_, body_, binder_]}} :> Replace[
			delaborateBinders[environment, context, lambdaAbstraction[name, domain, body, binder], lambdaAbstraction, Function],
			syntaxApplication[_, {binders_, bodySyntax_}] :> syntaxHead[Exists, {binders, bodySyntax}]
		],
		{head_, {}} :> headSyntax[environment, context, head],
		{head_, arguments_List} :> syntaxApplication[headSyntax[environment, context, head], Function[argument, delaborate[environment, context, argument]] /@ arguments]
	}]
]

headSyntax[environment_, context_, constantReference[HoldComplete[name_], _]] := toSyntax[name]
headSyntax[environment_, context_, head_] := delaborate[environment, context, head]

(* Construct keeps elaboration from filling in implicit arguments again, which it would do for any
   implicit binder among the arguments given, or before a constant on its own *)
exactApplication[environment_, context_, head_, arguments_List] := With[
	{
		headSyntax = exactHeadSyntax[environment, context, head],
		argumentSyntax = Function[argument, delaborate[environment, context, argument]] /@ arguments
	},
	Which[
		implicitBinderAmongQ[environment, context, head, Max[Length[arguments], 1]],
			syntaxHead[Construct, Prepend[argumentSyntax, headSyntax]],
		arguments === {},
			headSyntax,
		True,
			syntaxApplication[headSyntax, argumentSyntax]
	]
]

exactHeadSyntax[environment_, context_, constantReference[HoldComplete[name_], {}]] := toSyntax[name]
exactHeadSyntax[environment_, context_, constantReference[HoldComplete[name_], levels_List]] := syntaxHead[Subscript, Prepend[levelSyntax /@ levels, toSyntax[name]]]
exactHeadSyntax[environment_, context_, head_] := delaborate[environment, context, head]

implicitBinderAmongQ[environment_, context_, head_, n_Integer] := With[
	{binders = Quiet @ catchKernelFailure[binderKinds[environment, context, head, n]]},
	ListQ[binders] && ! MatchQ[binders, {"Explicit" ...}]
]

explicitArguments[environment_, context_, head_, arguments_List] := With[
	{binders = Quiet @ catchKernelFailure[binderKinds[environment, context, head, Length[arguments]]]},
	If[ ListQ[binders] && Length[binders] == Length[arguments],
		Pick[arguments, binders, "Explicit"],
		arguments
	]
]

(* the binder kinds of the first n arguments of head, read off its type: a function type as written gives
   its binder at once, and a type that is not one is unfolded, with the variables of the binders before it
   put in as placeholders. A constant's type is its declared one, whose universe levels decide no binder,
   and a function takes its own binders, so that only another head's type is inferred. *)
binderKinds[environment_, context_, constantReference[name_, _], n_Integer] := binderKindsFrom[environment, context, constantRecord[environment, name]["Type"], n, 0]
binderKinds[environment_, context_, function_lambdaAbstraction, n_Integer] /; Length[lambdaBinderKinds[function]] >= n := Take[lambdaBinderKinds[function], n]
binderKinds[environment_, context_, head_, n_Integer] := binderKindsFrom[environment, context, inferType[environment, context, head], n, 0]

lambdaBinderKinds[lambdaAbstraction[_, _, body_, binder_]] := Prepend[lambdaBinderKinds[body], binderKind[binder]]
lambdaBinderKinds[_] := {}
binderKindsFrom[_, _, _, 0, _] := {}
binderKindsFrom[environment_, context_, dependentFunctionType[_, _, codomain_, binder_], n_Integer, depth_Integer] :=
	Prepend[binderKindsFrom[environment, context, codomain, n - 1, depth + 1], binderKind[binder]]
binderKindsFrom[environment_, context_, type_, n_Integer, depth_Integer] := Replace[
	weakHeadNormalForm[environment, context, If[depth === 0, type, instantiateBoundVariables[type, ConstantArray[metavariable[0], depth]]]],
	{
		unfolded_dependentFunctionType :> binderKindsFrom[environment, context, unfolded, n, 0],
		_ :> {}
	}
]
