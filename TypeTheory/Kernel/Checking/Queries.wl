(* ::Package:: *)

(*
Questions about terms and environments.

TypeTheoryTerm[term, environment] carries the environment its constants come from; TypeTheoryTerm[term]
without one is read in the default environment, $TypeTheoryEnvironment, or, beside a term that has one, in that term's. A term's universe parameters are the symbols and strings
in its universe levels. Answers are TypeTheoryTerm expressions in the same environment, read back from
core terms.

An environment behaves like an Association of its constants: environment[name] gives the declaration
that introduced name, Keys gives the names in the order they were declared, and Length, KeyExistsQ and
Normal work as for an Association, Normal giving the declarations themselves, in order. Information
gives "Constants", "Kinds", "Axioms", "RewriteRules", "NaturalNumbers", "Rules" and "Provenance", which says whether
the environment was read from a file without checking it (SavedEnvironments.wl).

An environment's store can be changed by hand. TypeTheoryCheck[environment] is how to trust it anyway:
it replays every declaration in order on the empty environment of the same rules with the core
declaration functions, and compares each record with the one the replay produces. Axioms and rewrite
rules are taken on trust, as their name says.

TypeTheoryTranslate[environment, rules] replays the declarations the same way on the empty environment
of other rules, whose kernel checks each of them again: a translation is trusted no more than the
declarations it gives. Where the rules lose Prop, Prop becomes the lowest universe of types, Type, and the
other universes stay: a level l becomes max(l, 1), which commutes with instantiating universe parameters.
A recursor's motive goes into Sort u with Prop and into Sort (u + 1) without it, so the universe level a
recursor is applied at moves down by one where the rules lose Prop, and up by one where they gain it,
and a recursor that eliminates into Prop alone gets the level 0; a declaration whose motives go into
Prop itself, as a proof that 0 is no successor does, is tried again with the levels kept. An inductive
proposition lives in the universe of its largest field, as Exists does. What needs Prop's impredicativity
or proof irrelevance, or a recursor at a universe parameter that may be 0, then fails to check, and is
left out with every declaration that mentions it. A theorem of rules without Prop states a type, so where
the rules gain Prop it becomes a definition. Where the rules lose quantities, every binder loses its
quantity; where they gain them, the kernel gives the constructors and recursors theirs.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryType]
PackageExported[TypeTheoryExpression]
PackageExported[TypeTheoryCheck]
PackageExported[TypeTheoryAxiomClosure]
PackageExported[TypeTheoryTranslate]
PackageExported[DefinitionallyEqualQ]
PackageExported[WeakHeadNormalForm]
PackageExported[NormalForm]
PackageExported[TypeTheoryProofTree]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[termEnvironment]
PackageScoped[withNormalFormCheck]
PackageScoped[heldTerm]
PackageScoped[termSyntax]
PackageScoped[unnamedEnvironment]
PackageScoped[declarationOf]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryAxiomClosure::usage = "TypeTheoryAxiomClosure[term] gives the axioms the TypeTheoryTerm term rests on, through the types and values of the constants \
it mentions and of the constants those mention, as <|axiom -> kind, ...|>: \"Proposition\" for an axiom that is a proposition, \"Signature\" for one whose \
type is a type, a parameter as a variable is, \"RewriteRule\" for a rewrite rule of a constant reached, which the kernel computes with, and \"Registration\" \
for an operation on natural numbers registered without defining equations to check, which the kernel computes on literals as it trusts it to: \
every trusted assumption, so that an empty closure means the term rests on the kernel alone.\n\
TypeTheoryAxiomClosure[proof] gives the axioms the finished TypeTheoryProof proof rests on."
TypeTheoryExpression::usage = "TypeTheoryExpression[term] gives the expression of the Wolfram Language that the TypeTheoryTerm term is, as it is written: its constants the symbols that name them, a constructor of the type theory as the data the Wolfram Language writes, as True, Missing[\"NotAvailable\"] or a list of two for a pair, a class of the integers or the rationals as its number, and ascriptions and the types of binders left out; or a Failure where something in it is the type theory's only, as a proof or a recursor is. Nothing reduces it: TypeTheoryExpression[NormalForm[term]] reads the value the kernel computes, which the reading evaluates to where the definitions in term are the Wolfram Language's.\n\
TypeTheoryExpression[term, h] wraps the expression in h before it evaluates, as ToExpression does."
TypeTheoryType::usage = "TypeTheoryType[term] gives the type of term, or a Failure if it does not type-check: term is an expression of the type theory, \
kept unevaluated and in the default environment, or a TypeTheoryTerm in its own environment.\n\
TypeTheoryType[term, environment] gives the type of term in the TypeTheoryEnvironment environment, or in the library environment a name such as \"WolframLanguage\" stands for."
TypeTheoryCheck::usage = "TypeTheoryCheck[term] gives the type of the TypeTheoryTerm term by calling TypeTheoryType[term].\n\
TypeTheoryCheck[term, type] gives a Success if term has the given type, and a Failure otherwise.\n\
TypeTheoryCheck[environment] checks every declaration of the TypeTheoryEnvironment environment again from scratch and gives a Success, \
or a Failure for the first declaration that does not check. With Method -> \"Symbolic\" it replays every declaration with the kernel written in \
Wolfram Language; by default it checks with the compiled kernel where one is available."
TypeTheoryTranslate::usage = "TypeTheoryTranslate[environment, rules] translates the declarations of the TypeTheoryEnvironment environment to the \
TypeTheoryRules rules, whose kernel checks them again, and gives a Success whose \"Environment\" is the environment of rules with each declaration that \
checks there, and whose \"Failures\" gives the failure of each declaration left out, those that mention one included.\n\
Where rules have no Prop, Prop becomes the lowest universe of types, Type. Axioms are left out, since one that holds of propositions need not hold of \
types, as propositional extensionality does not; the option \"Axioms\" -> True keeps them."
DefinitionallyEqualQ::usage = "DefinitionallyEqualQ[term1, term2] gives True if the TypeTheoryTerm expressions term1 and term2 are equal by computation \
in their environment, and False otherwise."
WeakHeadNormalForm::usage = "WeakHeadNormalForm[term] reduces the TypeTheoryTerm term until its head can no longer reduce."
NormalForm::usage = "NormalForm[term] reduces the TypeTheoryTerm term and every part of it, under its binders too, until nothing can reduce: its normal form."
TypeTheoryProofTree::usage = "TypeTheoryProofTree[proof] gives the natural-deduction derivation of the TypeTheoryTerm proof, a proof of propositional logic. TypeTheoryProofTree[rule, claim, {premise, ...}] is such a derivation of the TypeTheoryTerm claim by rule from the premises, each a TypeTheoryProofTree, rule being \"Assumption\", \"ImpliesIntro\", \"ImpliesElim\", \"AndIntro\", \"AndElim\", \"OrIntro\", \"OrElim\" or \"FalseElim\"."

withNormalFormCheck::usage = "withNormalFormCheck[expr] gives {result, redexes}: the result of expr, and the normal forms NormalForm computed while it ran that hold a beta-redex, a function applied to an argument, which no normal form may."
termEnvironment::usage = "termEnvironment[term] gives the environment of the TypeTheoryTerm term, or the default environment if it has none."
unnamedEnvironment::usage = "unnamedEnvironment[HoldComplete[term]] gives the environment a term given without one is in, the default environment."
heldTerm::usage = "heldTerm[term] gives HoldComplete[expr] for the TypeTheoryTerm term holding expr."
termSyntax::usage = "termSyntax[term] gives the syntax tree of the TypeTheoryTerm term."
declarationOf::usage = "declarationOf[environment, HoldComplete[name], mode] gives the declaration that introduced the constant name, \
its terms read back for display (mode \"Display\") or exactly (mode \"Exact\")."


(* ::Section:: *)
(*Function Definitions*)


(* a term without an environment is in the default environment *)
termEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
termEnvironment[TypeTheoryTerm[_, name_String]] := environmentNamed[name]
termEnvironment[TypeTheoryTerm[term_]] := unnamedEnvironment[HoldComplete[term]]

unnamedEnvironment[_HoldComplete] := defaultEnvironment[]

heldTerm[TypeTheoryTerm[term_, ___]] := HoldComplete[term]

termSyntax[TypeTheoryTerm[term_, ___]] := toSyntax[term]

(* the environment two terms share: a term without one takes the other's, and two without one are in
   the default environment *)
sharedEnvironment[first_TypeTheoryTerm, second_TypeTheoryTerm] := Replace[{givenEnvironment[first], givenEnvironment[second]}, {
	{None, None} :> unnamedEnvironment[Join[heldTerm[first], heldTerm[second]]],
	{environment_, None} | {None, environment_} :> environment,
	{environment_, environment_} :> environment,
	_ :> kernelFailure["DifferentEnvironments", "The terms carry different environments.", {}]
}]

givenEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
givenEnvironment[TypeTheoryTerm[_, name_String]] := environmentNamed[name]
givenEnvironment[TypeTheoryTerm[_]] := None

(* a term on its own has no universe parameters, so a level nothing decided in it is the level of Type *)
elaborateQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] := Block[{$levelGeneralization = "Type", $queryTermNext = expected === None},
	elaborateClosedTerm[environment, heldTerm[term], expected, universeParameters]
]

(* a term checks under rules with quantities only if its functions use their variables as their quantities allow *)
checkedQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] := With[
	{elaborated = elaborateQueryTerm[environment, term, expected, universeParameters]},
	If[rulesSetting[environment, "Quantities"], withKernelCaches[checkLiveUses[environment, First[elaborated]]]];
	elaborated
]


TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "AxiomClosure"] := TypeTheoryAxiomClosure[term]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Constants"] := catchKernelFailure[ReleaseHold /@ typeAndValueConstants[termEnvironment[term], term]]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Holes"] := catchKernelFailure[termHoles[termEnvironment[term], term]]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Annotation"] := catchKernelFailure[termAnnotation[termEnvironment[term], term]]
TypeTheoryProofTree[term : TypeTheoryTerm[_, ___]] := catchKernelFailure[proofTree[termEnvironment[term], term]]
TypeTheoryProof /: Information[proof : TypeTheoryProof[_Association], "ProofTree"] := TypeTheoryProofTree[proof]
(* a finished proof, by its term *)
TypeTheoryProofTree[TypeTheoryProof[data_Association]] := catchKernelFailure @ If[ data["Goals"] =!= {},
	kernelFailure["ProofIncomplete", "The proof has `1` goals left: its term is not finished.", {Length[data["Goals"]]}],
	coreProofTree[data["Environment"], instantiateProofTerm[data, metavariable[data["Root"]]]]
]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "ProofTree"] := TypeTheoryProofTree[term]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Implementation"] := catchKernelFailure[termImplementation[termEnvironment[term], term]]
TypeTheoryTerm /: Information[TypeTheoryTerm[_, ___], "Properties"] := {"AxiomClosure", "Holes", "Constants", "Annotation", "ProofTree", "Implementation", "Expression"}

(* the Wolfram Language reading of a term: the expression it is, as it is written, its constants the symbols that name
   them and its data as the Wolfram Language writes them; it evaluates as the result of the function, or is wrapped in
   h before it does. Nothing reduces it: TypeTheoryExpression[NormalForm[term]] reads the value the kernel computes, and
   the two evaluate to the same expression where the term's definitions are the Wolfram Language's *)
TypeTheoryExpression[term_TypeTheoryTerm] := Replace[termReading[term], HoldComplete[expression_] :> expression]
TypeTheoryExpression[term_TypeTheoryTerm, wrapper_] := Replace[termReading[term], HoldComplete[expression_] :> wrapper[expression]]
TypeTheoryTerm /: Information[term : TypeTheoryTerm[_, ___], "Expression"] := TypeTheoryExpression[term]

(* the reading is of the term as it is written, which TypeTheoryType checks, and of a normal form as it is read back *)
termReading[term_TypeTheoryTerm] := catchKernelFailure[Replace[wolframReading[heldExpression[term], quotientReadings[termEnvironment[term]]], {
	None :> kernelFailure["NoExpression", "`1` has no reading as an expression of the Wolfram Language.", {term}]
}]]

SetAttributes[heldExpression, HoldAllComplete]
heldExpression[TypeTheoryTerm[expression_, ___]] := HoldComplete[expression]

(* the readable term, its data read as the Wolfram Language writes them, or None where something in it is the type
   theory's only. Unevaluated around the whole term is the expression itself; inside, it stays, as the Wolfram Language
   passes the argument on unevaluated. A class of a quotient is marked first, while its relation is as the normal form of
   the relation's constant writes it, and read once the pair in it is read. A string ascribed Strings stays a string,
   whatever constant its text names, kept as its character codes, where no rule reads it, until the end. Nothing a rule puts in a held expression evaluates. *)
wolframReading[held_HoldComplete, quotients_List] := With[
	{
		read = ReplaceAll[
			ReplaceRepeated[ReplaceRepeated[Replace[held, $wholeTermReadings], quotients], $wolframReadings],
			HoldPattern[stringValue[codes_List]] :> RuleCondition[FromCharacterCode[codes]]
		]
	},
	If[readQ[read], read, None]
]
$wholeTermReadings = {
	HoldComplete[Unevaluated[expression_]] :> HoldComplete[expression],
	HoldComplete[Unevaluated[elements___]] :> HoldComplete[Sequence[elements]]
}
$wolframReadings = {
	HoldPattern[Typed[text_String, Strings]] :> RuleCondition[stringValue[ToCharacterCode[text]]],
	(* the value of a type written by a string: the string itself, or what it parses to *)
	HoldPattern[Typed[FromString[text_String], Strings]] :> RuleCondition[stringValue[ToCharacterCode[text]]],
	HoldPattern[Typed[FromString[text_String], _]] :> RuleCondition[parsedString[ToExpression[text, InputForm, HoldComplete]]],
	HoldPattern[FromString[text_String]] :> RuleCondition[stringValue[ToCharacterCode[text]]],
	HoldPattern[(Typed | TypeHint)[expression_, _]] :> expression,
	(* a function takes its explicit arguments: its implicit binders are left out, and the types of the others *)
	HoldPattern[Function[{before___, _TypedImplicit, after___}, body_]] :> Function[{before, after}, body],
	HoldPattern[Function[{}, body_]] :> body,
	HoldPattern[Decide[proposition_]] :> proposition,
	HoldPattern[Arguments[expression_]] :> Sequence @@ expression,
	HoldPattern[Naturals] :> NonNegativeIntegers,
	HoldPattern["successor"[x_]] :> x + 1,
	"zero" -> 0,
	"true" -> True,
	"false" -> False,
	HoldPattern[("left" | "right" | "some")[x_]] :> x,
	"none" :> Missing["NotAvailable"],
	HoldPattern["pair"[a_, b_]] :> {a, b},
	(* an element of a subtype is its value, the proof that it is in the subtype no part of the expression, as a
	   machine integer is the integer *)
	HoldPattern["subtype"[value_, _]] :> value,
	HoldPattern[quotientClass[reading_, a_Integer, b_Integer]] :> RuleCondition[reading[a, b]],
	HoldPattern[parsedString[HoldComplete[expression_]]] :> expression,
	(* an atom or an association quoted, as a normal form reads one back among data, is itself *)
	HoldPattern[Unevaluated[atom_]] /; AtomQ[Unevaluated[atom]] && ! MatchQ[Unevaluated[atom], _Symbol] :> atom,
	HoldPattern[Unevaluated[association_Association]] :> association
}
(* the classes of the integers and the rationals by the normal forms of their relations: (a, b) is a - b, and (n, d) of
   an integer and a natural number is n / (d + 1) *)
quotientReadings[environment_] := quotientReadings[environment] = Join[
	quotientReading[environment, "integerRelation", Function[{a, b}, a - b]],
	quotientReading[environment, "rationalRelation", Function[{n, d}, n / (d + 1)]]
]
quotientReading[environment_, name_String, reading_] := If[ ! constantDeclaredQ[environment, HoldComplete[name]], {},
	Replace[With[{normal = NormalForm[TypeTheoryTerm @@ {name, environment}]}, heldExpression[normal]], {
		HoldComplete[relation_] :> {HoldPattern[QuotientIntroduction[relation, "pair"[a_, b_]]] :> quotientClass[reading, a, b]},
		_ -> {}
	}]
]

(* read: no constant named by a string, symbol of the type theory, as InductiveRecursor or Typed, or unread class is left *)
readQ[HoldComplete[expression_]] := FreeQ[
	Unevaluated[expression],
	_String[___] | _quotientClass | _parsedString | _stringValue | (symbol_Symbol /; Quiet[Context[Unevaluated[symbol]]] === "WolframInstitute`TypeTheory`"),
	{0, Infinity},
	Heads -> True
]



(* TypeTheoryType holds its argument, an expression of the type theory as a statement of TypeTheoryProof is, or a
   TypeTheoryTerm: written out, with PacletSymbol as its head as code copied from a documentation page has it, or kept
   in a symbol; a term computed by an expression is given with Evaluate *)
SetAttributes[TypeTheoryType, HoldAllComplete]
TypeTheoryType[term_] := typeOfTerm[givenTerm[term, None]]
TypeTheoryType[term_, environment_] := With[{evaluated = environmentNamed[environment]}, typeOfTerm[givenTerm[term, evaluated]] /; environmentQ[evaluated]]
TypeTheoryType[_, environment_] := With[{evaluated = environmentNamed[environment]}, evaluated /; FailureQ[evaluated]]

SetAttributes[givenTerm, HoldAllComplete]
givenTerm[term : TypeTheoryTerm[__], None] := term
givenTerm[TypeTheoryTerm[term_], environment_] := TypeTheoryTerm[term, environment]
givenTerm[given : TypeTheoryTerm[_, own_], environment_] /; environment =!= None :=
	If[ givenEnvironment[given] === environment, given, Failure["DifferentEnvironments", <|"MessageTemplate" -> "The term carries another environment than the one given.", "MessageParameters" -> {}|>]]
givenTerm[(head : HoldPattern[PacletSymbol[_, _String]])[arguments___], environment_] /; head === TypeTheoryTerm := givenTerm[TypeTheoryTerm[arguments], environment]
givenTerm[symbol_Symbol, None] /; MatchQ[OwnValues[symbol], {_ :> _TypeTheoryTerm}] := symbol
givenTerm[term_, None] := TypeTheoryTerm[term]
givenTerm[term_, environment_] := TypeTheoryTerm[term, environment]

(* a constant on its own has its declared type, with its implicit arguments and universe parameters *)
typeOfTerm[failure_Failure] := failure
(* an ascription, Typed[t, T], has the type T it is given, checked, as Lean's #check (t : T) shows T: the kernel's own
   type of t, as 4 == 4 for "equalityReflexivity"[4], is equal to it but no longer as written *)
typeOfTerm[term_TypeTheoryTerm] /; MatchQ[heldTerm[term], HoldComplete[Typed[_, _]]] := catchKernelFailure @ With[
	{environment = termEnvironment[term], universeParameters = universeParameterNames[{termSyntax[term]}]},
	Replace[heldTerm[term], HoldComplete[Typed[value_, type_]] :> With[
		{expected = Block[{$levelGeneralization = "Type"}, elaborateClosedType[environment, HoldComplete[type], universeParameters]]},
		checkedQueryTerm[environment, TypeTheoryTerm[value, environment], expected, universeParameters];
		coreToTypeTheoryTerm[environment, <||>, expected]
	]]
]
typeOfTerm[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	coreToTypeTheoryTerm[environment, <||>, betaNormalize @ Replace[aliasResolvedName[environment, heldFromSyntax[termSyntax[term]]], {
		name_ /; And[constantDeclaredQ[environment, name], ! overloadedNameQ[environment, name], constantRecord[environment, name]["Kind"] =!= "RewriteRule"] :>
			constantRecord[environment, name]["Type"],
		_ :> Last @ checkedQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]
	}]]
]


TypeTheoryCheck[term_TypeTheoryTerm] := TypeTheoryType[term]

TypeTheoryCheck[term_TypeTheoryTerm, type_TypeTheoryTerm] := catchKernelFailure @ With[
	{environment = sharedEnvironment[term, type], universeParameters = universeParameterNames[{termSyntax[term], termSyntax[type]}]},
	{expected = Block[{$levelGeneralization = "Type"}, elaborateClosedType[environment, heldTerm[type], universeParameters]]},
	checkedQueryTerm[environment, term, expected, universeParameters];
	Success["TypeChecked", <|"MessageTemplate" -> "`1` has type `2`.", "MessageParameters" -> {term, type}, "Term" -> term, "Type" -> type|>]
]


(* the kernel checks each term as elaboration finishes, so the two compared are checked; a comparison that goes deeper than
   the kernel can recurse is undecided, a failure that names the two terms, not False *)
DefinitionallyEqualQ[first_TypeTheoryTerm, second_TypeTheoryTerm] := Replace[catchKernelFailure @ With[
	{environment = sharedEnvironment[first, second], universeParameters = universeParameterNames[{termSyntax[first], termSyntax[second]}]},
	{
		terms = {
			First @ elaborateQueryTerm[environment, first, None, universeParameters],
			First @ elaborateQueryTerm[environment, second, None, universeParameters]
		}
	},
	withCheckedTerms[definitionallyEqualQ[environment, <||>, First[terms], Last[terms]]]
], {
	exhausted : Failure["RecursionLimit", _] :> Failure["RecursionLimit", <|
		"MessageTemplate" -> "Deciding whether `1` and `2` are definitionally equal goes deeper than the kernel can recurse, `3` calls: the two are not known to differ.",
		"MessageParameters" -> {first, second, First[exhausted["MessageParameters"]]}
	|>],
	result_ :> TrueQ[result]
}]


WeakHeadNormalForm[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	With[{elaborated = elaborateQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]},
		valueTerm[environment, weakHeadNormalForm[environment, <||>, First[elaborated]], Last[elaborated]]
	]
]

(* the normal form: the head reduced, then each part, a binder's body with its variable free *)
NormalForm[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	With[{elaborated = elaborateQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]},
		valueTerm[environment, noted[withKernelCaches[normalForm[environment, <||>, First[elaborated]]]], Last[elaborated]]
	]
]

(* the normal forms with a beta-redex, which none may hold, collected while withNormalFormCheck runs *)
$normalFormRedexes = None
SetAttributes[withNormalFormCheck, HoldFirst]
withNormalFormCheck[expr_] := Block[{$normalFormRedexes = {}}, With[{result = expr}, {result, $normalFormRedexes}]]
noted[normal_] := (
	If[ListQ[$normalFormRedexes] && ! FreeQ[normal, application[_lambdaAbstraction, _]], AppendTo[$normalFormRedexes, normal]];
	normal
)

(* A value read back as it is written, and ascribed its type where the reading alone does not elaborate: a lone string,
   which on its own names a constant, the empty list, or a value of a sum, "right"["text"], whose types the reading
   does not give; the type flows from the ascription into the parts, so one at the top is enough. A reading that
   elaborates is left as it is, with the type it elaborates to, as "none" is an option of any type. *)
valueTerm[environment_, term_, type_] := With[{read = coreToTypeTheoryTerm[environment, <||>, term]},
	If[ readBackQ[environment, read],
		read,
		Replace[{read, coreToTypeTheoryTerm[environment, <||>, type]}, {
			{TypeTheoryTerm[value_, ___], TypeTheoryTerm[typeValue_, ___]} :> TypeTheoryTerm[Typed[value, typeValue], environment],
			_ :> read
		}]
	]
]

readBackQ[environment_, read_TypeTheoryTerm] := ListQ[Quiet[catchKernelFailure[elaborateQueryTerm[environment, read, None, universeParameterNames[{termSyntax[read]}]]]]]

normalForm[environment_, context_, term_] := normalParts[environment, context, weakHeadNormalForm[environment, context, term]]

(* an application in weak head normal form is a head that does not reduce applied to its arguments: the head, a
   constant, a variable or a stuck recursor, stays, and only the arguments are normalized. Normalizing the function of
   each application on its own unfolds a partial application, as Plus[0] of a sum 0 + n stuck on n, into a function
   applied to n, a redex *)
normalParts[environment_, context_, term : application[_, _]] := With[{spine = applicationSpine[term]},
	makeApplication[normalHead[environment, context, First[spine]], Map[Function[argument, normalForm[environment, context, argument]], Last[spine]]]
]
normalHead[_, _, head : (_constantReference | _freeVariable | _boundVariable | _metavariable)] := head
normalHead[environment_, context_, head_] := normalForm[environment, context, head]
normalParts[environment_, context_, lambdaAbstraction[name_, domain_, body_, binder_]] := With[{id = freshFreeVariable[]},
	Construct[lambdaAbstraction, name, normalForm[environment, context, domain], abstractFreeVariable[
		normalForm[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[body, freeVariable[id]]], id
	], binder]
]
normalParts[environment_, context_, dependentFunctionType[name_, domain_, codomain_, binder_]] := With[{id = freshFreeVariable[]},
	Construct[dependentFunctionType, name, normalForm[environment, context, domain], abstractFreeVariable[
		normalForm[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[codomain, freeVariable[id]]], id
	], binder]
]
normalParts[environment_, context_, projection[structure_, index_, structureTerm_]] := Construct[projection, structure, index, normalForm[environment, context, structureTerm]]
normalParts[_, _, term_] := term


(* ::Subsection:: *)
(*Environments as associations*)


(environment : TypeTheoryEnvironment[_Symbol])[name_] /; environmentQ[environment] := declarationOf[environment, HoldComplete[name], "Display"]

TypeTheoryEnvironment /: Keys[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := ReleaseHold /@ environmentNames[environment]
TypeTheoryEnvironment /: Length[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := Length[environmentNames[environment]]
TypeTheoryEnvironment /: KeyExistsQ[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, name_] := constantDeclaredQ[environment, HoldComplete[name]]

(* the declarations, in order; constructors and recursors come with their inductive type *)
TypeTheoryEnvironment /: Normal[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := catchKernelFailure @ With[
	{primary = primaryNames[environment]},
	Replace[naturalNumberSettings[environment], {
		settings_Association :> withRegistrations[Function[name, declarationOf[environment, name, "Exact"]] /@ primary, primary, settings],
		None :> Function[name, declarationOf[environment, name, "Exact"]] /@ primary
	}]
]

(* constructors and recursors come with their type, the types of a block with its first, and the holes of a theorem
   with the theorem, whose proof reads back with them *)
primaryNames[environment_] := Select[
	environmentNames[environment],
	Function[name, With[{record = constantRecord[environment, name]}, ! generatedQ[record, name] && record["Kind"] =!= "Hole"]]
]

generatedQ[record_, name_] := Or[
	MatchQ[record["Kind"], "Constructor" | "Recursor"],
	record["Kind"] === "InductiveType" && First[record["Block"]] =!= name,
	record["Kind"] === "Quotient" && record["QuotientType"] =!= name,
	record["Kind"] === "Cubical" && record["CubicalRole"] =!= "Interval"
]

(* each registration of the natural numbers, or of operations on them, comes right after the last constant
   it names, and after the registration before it *)
withRegistrations[declarations_List, primary_List, settings_Association] := With[
	{positions = Rest @ FoldList[Max, 0, MapIndexed[
		Function[{roles, index}, Max[Flatten[Position[primary, Alternatives @@ registrationNames[settings, First[index]], {1}]]]],
		settings["Registrations"]
	]]},
	Catenate @ MapIndexed[
		Function[{declaration, index}, Prepend[
			Function[registration, registrationDeclaration[settings, registration]] /@ Flatten[Position[positions, First[index]]],
			declaration
		]],
		declarations
	]
]

(* the constants a registration names: the first also names the natural numbers themselves *)
registrationNames[settings_Association, 1] := Join[Lookup[settings, {"Type", "Zero", "Successor"}], Lookup[settings["Operations"], First[settings["Registrations"]]]]
registrationNames[settings_Association, index_Integer] := Lookup[settings["Operations"], settings["Registrations"][[index]]]

registrationOf[settings_Association, index_Integer] := <|
	KeyTake[settings, {"Type", "Zero", "Successor"}],
	"Operations" -> KeyTake[settings["Operations"], settings["Registrations"][[index]]]
|>

registrationDeclaration[settings_Association, index_Integer] := ReleaseHold @ heldFromSyntax @ syntaxHead[
	TypeTheoryNaturalNumbers,
	Join[
		toSyntax @@@ Lookup[settings, {"Type", "Zero", "Successor"}],
		Replace[KeyTake[settings["Operations"], settings["Registrations"][[index]]], {
			<||> -> {},
			operations_ :> {syntaxHead[Association, KeyValueMap[Function[{role, name}, syntaxHead[Rule, {syntaxString[role], toSyntax @@ name}]], operations]]}
		}]
	]
]

TypeTheoryEnvironment /: Information[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, property_String] := environmentInformation[environment, property]

environmentInformation[_, "Properties"] := {"Constants", "Kinds", "Theorems", "Axioms", "RewriteRules", "NaturalNumbers", "Rules", "Provenance"}
(* the theorems by name, each with its statement, in the order they were declared *)
environmentInformation[environment_, "Theorems"] := Association[
	Function[name, theoremKey[name] -> coreToTypeTheoryTerm[environment, <||>, constantRecord[environment, name]["Type"]]] /@
		Select[environmentNames[environment], Function[name, constantRecord[environment, name]["Kind"] === "Theorem"]]
]

(* a theorem's name as a key: its string, or its symbol held; a rule of its own, as an enclosing -> would scope the pattern *)
theoremKey[HoldComplete[text_String]] := text
theoremKey[held_HoldComplete] := HoldForm @@ held
environmentInformation[environment_, "Constants"] := Keys[environment]
environmentInformation[environment_, "Kinds"] := Counts[Function[name, constantRecord[environment, name]["Kind"]] /@ environmentNames[environment]]
environmentInformation[environment_, "Axioms"] :=
	ReleaseHold /@ Select[environmentNames[environment], Function[name, constantRecord[environment, name]["Kind"] === "Axiom"]]
environmentInformation[environment_, "RewriteRules"] :=
	ReleaseHold /@ Select[environmentNames[environment], Function[name, constantRecord[environment, name]["Kind"] === "RewriteRule"]]
environmentInformation[environment_, "NaturalNumbers"] := Replace[
	naturalNumberSettings[environment],
	settings_Association :> <|Map[ReleaseHold, KeyTake[settings, {"Type", "Zero", "Successor"}]], "Operations" -> Map[ReleaseHold, settings["Operations"]]|>
]
environmentInformation[environment_, "Rules"] := environmentRules[environment]
environmentInformation[environment_, "Provenance"] := environmentProvenance[environment]


(* ::Subsection:: *)
(*Declarations read back*)


(* the quotient constants come from one declaration, written short with the prelude's names *)
quotientDeclaration[record_] := Replace[{record["Equality"], record["QuotientNames"]}, {
	{HoldComplete[Equal], HoldComplete /@ Unevaluated[{QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction}]} :> TypeTheoryQuotients[],
	{HoldComplete[equality_], names_List} :> (TypeTheoryQuotients[equality, names] /. HoldComplete[name_] :> name)
}]

declarationOf[environment_, name_HoldComplete, mode_String] := If[ ! constantDeclaredQ[environment, name],
	Missing["KeyAbsent", ReleaseHold[name]],
	Replace[constantRecord[environment, name], {
		record : KeyValuePattern["Kind" -> "Constructor" | "Recursor"] :> declarationOf[environment, record["InductiveType"], mode],
		record : KeyValuePattern["Kind" -> "Hole"] :> declarationOf[environment, record["Theorem"], mode],
		record : KeyValuePattern["Kind" -> "Quotient"] :> quotientDeclaration[record],
		record : KeyValuePattern["Kind" -> "Cubical"] :> Replace[record["Sum"], HoldComplete[sum_] :> TypeTheoryCubical[sum]],
		record_ :> ReleaseHold @ heldFromSyntax @ If[mode === "Display", withoutAutomaticUniverses[#, record] &, Identity][declarationSyntax[environment, name, record, mode]]
	}]
]

(* a rewrite rule reads back as ForAll[binders, lhs -> rhs], with the binders its two sides share *)
declarationSyntax[environment_, name_, record : KeyValuePattern["Kind" -> "RewriteRule"], mode_] := syntaxHead[TypeTheoryRewriteRule, Join[
	{
		toSyntax @@ name,
		ruleSyntax[readBack[environment, record["LeftHandSide"], mode], readBack[environment, record["RightHandSide"], mode], record["NumberOfVariables"]]
	},
	universeOptionSyntax[record]
]]

declarationSyntax[environment_, name_, record_, mode_] := With[
	{
		nameSyntax = toSyntax @@ name,
		typeSyntax = readBack[environment, record["Type"], mode],
		universeOption = universeOptionSyntax[record]
	},
	Replace[record["Kind"], {
		"InductiveType" /; Length[record["Block"]] > 1 :> syntaxHead[TypeTheoryInductiveType, Join[
			{
				syntaxHead[List, Function[member,
					syntaxHead[Rule, {toSyntax @@ member, readBack[environment, constantRecord[environment, member]["Type"], mode]}]
				] /@ record["Block"]],
				syntaxHead[List, Function[constructor,
					syntaxHead[Rule, {toSyntax @@ constructor, readBack[environment, constantRecord[environment, constructor]["Type"], mode]}]
				] /@ Catenate[Function[member, constantRecord[environment, member]["Constructors"]] /@ record["Block"]]],
				syntaxHead[Rule, {syntaxString["Parameters"], syntaxInteger[record["NumberOfParameters"]]}]
			},
			universeOption
		]],
		"Axiom" :> syntaxHead[TypeTheoryAxiom, Join[{nameSyntax, typeSyntax}, universeOption, annotationOptionSyntax[record], overloadsOptionSyntax[record], implementationOptionSyntax[record]]],
		"Definition" | "Opaque" :> syntaxHead[TypeTheoryDefinition, Join[
			{nameSyntax, syntaxHead[Typed, {readBack[environment, record["Value"], mode], typeSyntax}]},
			universeOption,
			Function[role, syntaxHead[Rule, {syntaxString[role], syntaxSymbol[HoldComplete[True]]}]] /@ Keys[Select[recordRoles[record], TrueQ]],
			overloadsOptionSyntax[record]
		]],
		"Theorem" :> syntaxHead[TypeTheoryTheorem, Join[{nameSyntax, typeSyntax, readBack[environment, record["Value"], mode]}, universeOption, annotationOptionSyntax[record]]],
		"InductiveType" :> syntaxHead[TypeTheoryInductiveType, Join[
			{
				nameSyntax,
				typeSyntax,
				syntaxHead[List, Function[constructor,
					syntaxHead[Rule, {toSyntax @@ constructor, readBack[environment, constantRecord[environment, constructor]["Type"], mode]}]
				] /@ record["Constructors"]],
				syntaxHead[Rule, {syntaxString["Parameters"], syntaxInteger[record["NumberOfParameters"]]}]
			},
			universeOption
		]]
	}]
]

(* the roles of a definition's record, as declareDefinition takes them *)
recordRoles[record_] := Join[Append[KeyTake[record, {"Instance", "Coercion"}], "Opaque" -> record["Kind"] === "Opaque"], KeyTake[record, {"Overloads"}]]

overloadsOptionSyntax[record_] := Replace[Lookup[record, "Overloads", None], {None -> {}, operation_HoldComplete :> {syntaxHead[Rule, {syntaxString["Overloads"], toSyntax @@ operation}]}}]

implementationOptionSyntax[record_] := Replace[Lookup[record, "Implementation", None], {None -> {}, implementation_HoldComplete :> {syntaxHead[Rule, {syntaxString["Implementation"], toSyntax @@ implementation}]}}]

annotationOptionSyntax[record_] := Replace[Lookup[record, "Annotation", None], {None -> {}, annotation_ :> {syntaxOther[HoldComplete["Annotation" -> annotation]]}}]

(* the option "UniverseParameters" of a declaration read back for display is left out where Automatic gives the same
   list, the symbols and strings in the universe levels of its arguments in the order they appear; an exact read back,
   which translations read, keeps it *)
withoutAutomaticUniverses[syntax : syntaxApplication[head_, arguments_List], record_] := If[
	universeParameterNames[Rest[Select[arguments, Function[argument, ! optionSyntaxQ[argument]]]]] === record["UniverseParameters"],
	syntaxApplication[head, DeleteCases[arguments, syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {syntaxString["UniverseParameters"], _}]]],
	syntax
]
withoutAutomaticUniverses[syntax_, _] := syntax

optionSyntaxQ[syntaxApplication[syntaxSymbol[HoldComplete[Rule]], {syntaxString[_], _}]] := True
optionSyntaxQ[syntaxOther[HoldComplete[_String -> _]]] := True
optionSyntaxQ[_] := False

universeOptionSyntax[record_] := Replace[record["UniverseParameters"], {
	{} -> {},
	parameters_List :> {syntaxHead[Rule, {syntaxString["UniverseParameters"], syntaxHead[List, toSyntax @@@ parameters]}]}
}]

ruleSyntax[left_, right_, 0] := syntaxHead[Rule, {left, right}]
ruleSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Function]], {binders_, leftBody_}], syntaxApplication[syntaxSymbol[HoldComplete[Function]], {_, rightBody_}], _] :=
	syntaxHead[ForAll, {binders, syntaxHead[Rule, {leftBody, rightBody}]}]

readBack[environment_, term_, "Display"] := slotFunctions[delaborate[environment, <||>, term]]
readBack[environment_, term_, "Exact"] := Block[{$exactReadBack = True}, delaborate[environment, <||>, term]]


(* ::Subsection:: *)
(*The axioms a term rests on*)


(* Lean's #print axioms: the constants a term mentions, then those in the type and value of each, until an axiom,
   which is collected and its type followed, so that a signature's own parameters show; a constructor or recursor
   leads to its inductive type, and an inductive type to its constructors. A rewrite rule of a constant reached is
   trusted as an axiom is, and so is the registration of an operation on natural numbers without defining equations,
   which the kernel computes on literals unchecked: an empty closure means the term rests on the kernel alone. An axiom is a proposition when its type is a proposition, and a signature otherwise:
   a type, or a function into types, which a theorem holds for in every model, as for a variable. *)
TypeTheoryAxiomClosure[term_TypeTheoryTerm] := catchKernelFailure @ Block[{closureEnvironment = termEnvironment[term]},
	First[closureOf[closureEnvironment, queryCoreTerm[closureEnvironment, term]]]
]

(* a finished proof's own core term: the term it reads back as leaves out implicit arguments, which elaborating it
   again without its statement cannot always find *)
TypeTheoryAxiomClosure[TypeTheoryProof[data_Association]] := catchKernelFailure @ If[ data["Goals"] =!= {},
	kernelFailure["ProofIncomplete", "The proof has `1` goals left: its term is not finished.", {Length[data["Goals"]]}],
	First[closureOf[data["Environment"], instantiateProofTerm[data, metavariable[data["Root"]]]]]
]

(* the core term of a query; a declared constant on its own is that constant, an overloaded name such as True included *)
queryCoreTerm[environment_, term_] := Replace[aliasResolvedName[environment, heldFromSyntax[termSyntax[term]]], {
	name_ /; constantDeclaredQ[environment, name] :> constantReference[name, {}],
	_ :> First @ checkedQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]
}]

(* {axioms, holes} a term rests on: the axioms as <|name -> kind|>, the holes as <|HoldComplete[hole] -> record|>; the
   subterms seen are shared by the whole closure, so a term the declarations share is walked once *)
closureOf[environment_, term_] := Block[{$closureVisited = <||>, $closureAxioms = <||>, $closureHoles = <||>, $constantsSeen = <||>},
	withKernelCaches[visitTerm[environment, term]];
	{KeyMap[ReleaseHold, $closureAxioms], $closureHoles}
]

termHoles[environment_, term_] := holeGroups[environment, Last[closureOf[environment, queryCoreTerm[environment, term]]]]

(* the annotation of a constant's record: a hole's, or None *)
(* the function that computes a constant, the symbol its declaration names, or None *)
termImplementation[environment_, term_] := Replace[queryCoreTerm[environment, term], {
	constantReference[name_, _] :> Replace[Lookup[constantRecord[environment, name], "Implementation", None], HoldComplete[implementation_] :> implementation],
	_ :> None
}]

termAnnotation[environment_, term_] := Replace[queryCoreTerm[environment, term], {
	constantReference[name_, _] :> Lookup[constantRecord[environment, name], "Annotation", None],
	_ :> None
}]

(* the holes by the theorem they are holes of, each with its statement and its annotation *)
holeGroups[environment_, holes_Association] := GroupBy[
	KeyValueMap[
		Function[{name, record}, <|
			"Theorem" -> ReleaseHold[record["Theorem"]],
			"Hole" -> ReleaseHold[name],
			"Statement" -> coreToTypeTheoryTerm[environment, <||>, record["Type"]],
			"Annotation" -> record["Annotation"]
		|>],
		holes
	],
	Function[hole, hole["Theorem"]],
	Map[Function[hole, KeyDrop[hole, "Theorem"]]]
]

visitConstant[environment_, name_] := If[ ! KeyExistsQ[$closureVisited, name],
	$closureVisited[name] = True;
	visitRecord[environment, name, constantRecord[environment, name]];
	If[uncheckedRegistrationQ[environment, name], $closureAxioms[name] = "Registration"];
	Scan[Function[rule, $closureAxioms[rule] = "RewriteRule"], rewriteRuleNames[environment, name]]
]

visitRecord[environment_, name_, record_] := Switch[record["Kind"],
	"Axiom",
		$closureAxioms[name] = If[propositionTypeQ[environment, record["Type"]], "Proposition", "Signature"];
		visitTerm[environment, record["Type"]],
	"Definition" | "Opaque" | "Theorem",
		visitTerm[environment, record["Type"]];
		visitTerm[environment, record["Value"]],
	"InductiveType",
		visitTerm[environment, record["Type"]];
		Scan[Function[constructor, visitConstant[environment, constructor]], record["Constructors"]],
	"Constructor" | "Recursor",
		visitTerm[environment, record["Type"]];
		visitConstant[environment, record["InductiveType"]],
	"RewriteRule",
		$closureAxioms[name] = "RewriteRule",
	"Hole",
		$closureHoles[name] = record;
		visitTerm[environment, record["Type"]],
	_,
		visitTerm[environment, record["Type"]]
]

visitTerm[environment_, term_] := Scan[Function[name, visitConstant[environment, name]], unseenConstants[term]]

propositionTypeQ[environment_, type_] := MatchQ[weakHeadNormalForm[environment, <||>, inferType[environment, <||>, type]], universeSort[0]]

(* the constants the type and the value of a term mention: of a constant, those of its declaration *)
typeAndValueConstants[environment_, term_] := Replace[queryCoreTerm[environment, term], {
	constantReference[name_, _] :> Block[{constantFields = constantRecord[environment, name]},
		DeleteDuplicates[Join @@ Map[termConstants, DeleteMissing[Lookup[constantFields, {"Type", "Value"}]]]]
	],
	core_ :> DeleteDuplicates[Join[termConstants[core], termConstants[withKernelCaches[inferType[environment, <||>, core]]]]]
}]

(* the constants a core term mentions, each shared subterm visited once *)
termConstants[term_] := Block[{$constantsSeen = <||>}, unseenConstants[term]]

(* the constants in the subterms of term not seen yet *)
unseenConstants[term_] := DeleteDuplicates @ Flatten @ Last @ Reap[collectConstants[term], $constantTag]

collectConstants[term_] := If[ ! KeyExistsQ[$constantsSeen, term], $constantsSeen[term] = True; constantsOf[term]]

constantsOf[constantReference[name_, _]] := Sow[name, $constantTag]
constantsOf[application[function_, argument_]] := (collectConstants[function]; collectConstants[argument])
constantsOf[(lambdaAbstraction | dependentFunctionType)[_, domain_, body_, _]] := (collectConstants[domain]; collectConstants[body])
constantsOf[localDefinition[_, type_, value_, body_]] := (collectConstants[type]; collectConstants[value]; collectConstants[body])
constantsOf[projection[structure_, _, term_]] := (Sow[structure, $constantTag]; collectConstants[term])
constantsOf[cubicalSystem[branches_List]] := Scan[collectConstants, Flatten[branches, 1]]
constantsOf[_] := Null


(* ::Subsection:: *)
(*Checking an environment*)


Options[TypeTheoryCheck] = {Method -> Automatic}

(* The compiled kernel (CompiledKernel.wl) checks the declarations but inductive types, their constructors and
   recursors, and quotient types, which are declared again after it, each after the records before it as they are.
   Where it refuses a declaration, those before it are declared again first, so that the failure is that of the first
   declaration in order that does not check. Where it does not handle the environment, or Method -> "Symbolic", every
   declaration is replayed with the kernel of TypeChecking.wl. *)
TypeTheoryCheck[name_String, options : OptionsPattern[]] := Replace[TypeTheoryEnvironment[name], environment_?environmentQ :> TypeTheoryCheck[environment, options]]
TypeTheoryCheck[environment_?environmentQ, options : OptionsPattern[]] /; ! MemberQ[{Automatic, "Compiled", "Symbolic"}, OptionValue[TypeTheoryCheck, {options}, Method]] :=
	Failure["UnknownMethod", <|
		"MessageTemplate" -> "`1` is no method of TypeTheoryCheck, which are Automatic, \"Compiled\" and \"Symbolic\".",
		"MessageParameters" -> {OptionValue[TypeTheoryCheck, {options}, Method]}
	|>]
TypeTheoryCheck[environment_?environmentQ, OptionsPattern[]] := withStoreCleanup @ catchKernelFailure @ Replace[
	If[MemberQ[{Automatic, "Compiled"}, OptionValue[Method]], compiledKernelCheck[environment], None],
	{
		failure_Failure :> (
			replayNames[environment, Take[environmentNames[environment], failure["Position"] - 1], replayGenerated[environment]];
			throwFailure[Failure[failure["Tag"], KeyDrop[Last[failure], "Position"]]]
		),
		None /; OptionValue[Method] === "Compiled" :> kernelFailure[
			"CompiledKernelUnavailable",
			"The compiled kernel has no library for this platform and version, or does not handle this environment.",
			{}
		],
		None :> replayEnvironment[environment, Function[{partial, name, record}, replayDeclaration[environment, partial, name -> record]]],
		_Success :> replayRuns[environment]
	}
]

(* after the compiled kernel, each run of records between inductive types and quotients is added at once, as it is,
   and the natural numbers registered as far as its constants allow, before the next inductive type is declared *)
replayRuns[environment_] := With[
	{
		replayed = Fold[
			Function[{partial, run}, If[ generatedKindQ[constantRecord[environment, First[run]]],
				Fold[Function[{inner, name}, replayGenerated[environment][inner, name, constantRecord[environment, name]]], partial, run],
				registerWhenDeclared[addConstantRecords[partial, AssociationMap[Function[name, constantRecord[environment, name]], run]], naturalNumberSettings[environment]]
			]],
			emptyEnvironmentOf[environmentRules[environment]],
			SplitBy[environmentNames[environment], Function[name, generatedKindQ[constantRecord[environment, name]]]]
		]
	},
	If[ naturalNumberSettings[replayed] =!= naturalNumberSettings[environment],
		kernelFailure["DeclarationMismatch", "The natural numbers of the environment do not match its declarations.", {}]
	];
	Success["EnvironmentChecked", <|
		"MessageTemplate" -> "All `1` constants of the environment check again from their declarations.",
		"MessageParameters" -> {Length[environmentNames[environment]]},
		"Constants" -> Length[environmentNames[environment]]
	|>]
]

generatedKindQ[record_] := MemberQ[{"InductiveType", "Constructor", "Recursor", "Quotient"}, record["Kind"]]

(* after the compiled kernel, the inductive types and quotients are declared again, and the other records added as they
   are; the compiled kernel has checked the types and rules the kernel generates, so declaring them again only compares
   them with the records, as a batch declares them ($deferKernelChecks) *)
replayGenerated[environment_][partial_, name_, record_] := If[
	MemberQ[{"InductiveType", "Constructor", "Recursor", "Quotient"}, record["Kind"]],
	Block[{$deferKernelChecks = True}, replayDeclaration[environment, partial, name -> record]],
	registerWhenDeclared[addConstantRecords[partial, <|name -> record|>], naturalNumberSettings[environment]]
]

replayNames[environment_, names_List, replay_] := Fold[
	Function[{partial, name}, replay[partial, name, constantRecord[environment, name]]],
	emptyEnvironmentOf[environmentRules[environment]],
	names
]

replayEnvironment[environment_, replay_] := With[{replayed = replayNames[environment, environmentNames[environment], replay]},
	If[ naturalNumberSettings[replayed] =!= naturalNumberSettings[environment],
		kernelFailure["DeclarationMismatch", "The natural numbers of the environment do not match its declarations.", {}]
	];
	Success["EnvironmentChecked", <|
		"MessageTemplate" -> "All `1` constants of the environment check again from their declarations.",
		"MessageParameters" -> {Length[environmentNames[environment]]},
		"Constants" -> Length[environmentNames[environment]]
	|>]
]

(* Constructors and recursors are generated with their inductive type, which comes before them; every
   record must come out of the replay exactly as it is in the environment. *)
replayDeclaration[original_, replayed_, name_ -> record_] := With[
	{extended = If[generatedQ[record, name], replayed, redeclare[original, replayed, name, record]]},
	If[ ! constantDeclaredQ[extended, name] || constantRecord[extended, name] =!= record,
		kernelFailure["DeclarationMismatch", "The record of `1` does not match the record that checking its declaration gives.", {HoldForm @@ name}]
	];
	registerWhenDeclared[extended, naturalNumberSettings[original]]
]

redeclare[original_, replayed_, name_, record_] := Replace[record["Kind"], {
	"Axiom" :> declareAxiom[replayed, name, record["UniverseParameters"], record["Type"], Lookup[record, "Annotation", None], Lookup[record, "Overloads", None], Lookup[record, "Implementation", None]],
	"Hole" :> declareHole[replayed, name, record["UniverseParameters"], record["Type"], record["Annotation"], record["Theorem"]],
	"Definition" | "Opaque" :> declareDefinition[replayed, name, record["UniverseParameters"], record["Type"], record["Value"], recordRoles[record]],
	"Theorem" :> declareTheorem[replayed, name, record["UniverseParameters"], record["Type"], record["Value"], Lookup[record, "Annotation", None]],
	"RewriteRule" :> declareRewriteRule[replayed, name, record["UniverseParameters"], record["NumberOfVariables"], record["LeftHandSide"], record["RightHandSide"]],
	"Quotient" :> declareQuotients[replayed, record["Equality"], record["QuotientNames"]],
	"Cubical" :> declareCubical[replayed, record["Sum"]],
	"InductiveType" :> declareInductiveTypes[
		replayed,
		record["UniverseParameters"],
		record["NumberOfParameters"],
		Function[member, member -> constantRecord[original, member]["Type"]] /@ record["Block"],
		Function[constructor, constructor -> constantRecord[original, constructor]["Type"]] /@ Catenate[Function[member, constantRecord[original, member]["Constructors"]] /@ record["Block"]]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name, kind}]
}]

(* ::Subsection:: *)
(*Translations between rules*)


Options[TypeTheoryTranslate] = {"Axioms" -> False}

TypeTheoryTranslate[name_String, rest__] := Replace[TypeTheoryEnvironment[name], environment_?environmentQ :> TypeTheoryTranslate[environment, rest]]
TypeTheoryTranslate[environment_?environmentQ, rules_?rulesQ, OptionsPattern[]] := withStoreCleanup @ catchKernelFailure @ With[
	{
		direction = Replace[{TrueQ[rulesSetting[environment, "Prop"]], TrueQ[rules["Prop"]]}, {{True, False} -> "LoseProp", {False, True} -> "GainProp", _ -> "SameProp"}],
		axiomsQ = TrueQ[OptionValue["Axioms"]],
		primary = primaryNames[environment]
	},
	{
		result = Fold[
			Function[{state, name}, translateDeclaration[environment, state, name, direction, axiomsQ]],
			<|"Environment" -> emptyEnvironmentOf[rules], "Failures" -> <||>|>,
			primary
		]
	},
	Success["Translated", <|
		"MessageTemplate" -> "`1` of the `2` declarations translate to the rules `3`.",
		"MessageParameters" -> {Length[primary] - Length[result["Failures"]], Length[primary], rules["Name"]},
		"Environment" -> result["Environment"],
		"Failures" -> KeyMap[ReleaseHold, result["Failures"]]
	|>]
]

(* the declaration of name redeclared in the environment of the other rules, or its failure recorded *)
translateDeclaration[original_, state_Association, name_, direction_String, axiomsQ_] := With[{record = constantRecord[original, name]},
	If[ record["Kind"] === "Axiom" && ! axiomsQ,
		Append[state, "Failures" -> Append[state["Failures"], name -> Failure["AxiomLeftOut", <|
			"MessageTemplate" -> "`1` is an axiom, which a translation keeps only with \"Axioms\" -> True.",
			"MessageParameters" -> {HoldForm @@ name}
		|>]]],
		Replace[catchKernelFailure[translatedDeclaration[original, state["Environment"], name, record, direction]], {
			failure_Failure :> Append[state, "Failures" -> Append[state["Failures"], name -> failure]],
			extended_ :> Append[state, "Environment" -> Replace[catchKernelFailure[registerWhenDeclared[extended, naturalNumberSettings[original]]], _Failure -> extended]]
		}]
	]
]

(* the recursors' levels lowered, or else kept, where the rules lose Prop *)
translatedDeclaration[original_, target_, name_, record_, direction_String] := With[
	{attempt = Function[mode, catchKernelFailure[translatedRecord[original, target, name, record, direction, Function[term, translatedTerm[original, target, direction, mode, term]]]]]},
	Replace[attempt["Lowered"], failure_Failure /; direction === "LoseProp" :> Replace[attempt["Kept"], _Failure -> failure]]
]

translatedRecord[original_, target_, name_, record_, direction_, translate_] := Replace[record["Kind"], {
	"Axiom" :> declareAxiom[target, name, record["UniverseParameters"], translate[record["Type"]], Lookup[record, "Annotation", None], Lookup[record, "Overloads", None], Lookup[record, "Implementation", None]],
	"Hole" :> declareHole[target, name, record["UniverseParameters"], translate[record["Type"]], record["Annotation"], record["Theorem"]],
	"Definition" | "Opaque" :> declareDefinition[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]], recordRoles[record]],
	"Theorem" /; direction === "GainProp" :> declareDefinition[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]]],
	"Theorem" :> declareTheorem[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]], Lookup[record, "Annotation", None]],
	"RewriteRule" :> declareRewriteRule[target, name, record["UniverseParameters"], record["NumberOfVariables"], translate[record["LeftHandSide"]], translate[record["RightHandSide"]]],
	"Quotient" :> declareQuotients[target, record["Equality"], record["QuotientNames"]],
	"Cubical" :> declareCubical[target, record["Sum"]],
	"InductiveType" :> With[
		{
			constructorTypes = Function[constructor, constructor -> translate[constantRecord[original, constructor]["Type"]]] /@
				Catenate[Function[member, constantRecord[original, member]["Constructors"]] /@ record["Block"]]
		},
		declareInductiveTypes[
			target,
			record["UniverseParameters"],
			record["NumberOfParameters"],
			Function[member, member -> raisedProposition[original, target, direction, record, constructorTypes, member, translate[constantRecord[original, member]["Type"]]]] /@ record["Block"],
			constructorTypes
		]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name}]
}]

(* an inductive proposition, where the rules lose Prop, lives in the universe of its largest field that is
   not of a type of its block, and in Type at least *)
raisedProposition[original_, target_, "LoseProp", record_, constructorTypes_List, member_, type_] /; conclusionSort[constantRecord[original, member]["Type"]] === universeSort[0] :=
	withConclusion[type, universeSort[normalizeLevel[levelMaximum @@ Prepend[
		Catenate[Function[constructor, fieldLevels[target, <||>, record["NumberOfParameters"], record["Block"], Last[constructor], {}]] /@ constructorTypes],
		1
	]]]]
raisedProposition[_, _, _, _, _, _, type_] := type

conclusionSort[dependentFunctionType[_, _, codomain_, _]] := conclusionSort[codomain]
conclusionSort[sort_] := sort

withConclusion[dependentFunctionType[name_, domain_, codomain_, binder_], sort_] := Construct[dependentFunctionType, name, domain, withConclusion[codomain, sort], binder]
withConclusion[_, sort_] := sort

(* the universes of a constructor's fields, its parameters skipped *)
fieldLevels[target_, context_, skipped_Integer, block_List, dependentFunctionType[name_, domain_, codomain_, binder_], levels_List] := With[{id = freshFreeVariable[]},
	fieldLevels[
		target,
		extendContext[context, id, name, domain, binder],
		Max[skipped - 1, 0],
		block,
		instantiateBoundVariable[codomain, freeVariable[id]],
		If[ skipped > 0 || ! FreeQ[domain, constantReference[Alternatives @@ block, _]], levels, Append[levels, sortLevel[target, context, domain]]]
	]
]
fieldLevels[_, _, _, _, _, levels_List] := levels

(* Where the rules lose Prop, Prop becomes Type, the lowest universe of types, and every other sort stays: a
   level l becomes max(l, 1), so a constant keeps its universe levels, its own sorts lifted the same way. A
   recursor's level moves with the meaning of its motive's universe. *)
translatedTerm[original_, target_, direction_, mode_, term_] := ReplaceAll[If[TrueQ[rulesSetting[target, "Quantities"]], term, withoutQuantities[term]], {
	universeSort[level_] /; direction === "LoseProp" :> With[{lifted = normalizeLevel[levelMaximum[level, 1]]}, universeSort[lifted] /; True],
	constantReference[name : HoldComplete[_InductiveRecursor], levels_List] :> With[{moved = recursorLevels[original, target, direction, mode, name, levels]}, constantReference[name, moved] /; True]
}]

(* the levels of a recursor in the other rules: its first is the universe its motive goes into, if it has one *)
recursorLevels[original_, target_, direction_, mode_, name_, levels_List] := With[
	{
		sourceUniverse = TrueQ[constantRecord[original, name]["EliminationUniverse"]],
		targetUniverse = constantDeclaredQ[target, name] && TrueQ[constantRecord[target, name]["EliminationUniverse"]]
	},
	Which[
		direction === "LoseProp" && sourceUniverse && targetUniverse && mode === "Lowered", Prepend[Rest[levels], loweredUniverse[First[levels]]],
		direction === "LoseProp" && ! sourceUniverse && targetUniverse, Prepend[levels, 0],
		direction === "GainProp" && sourceUniverse && targetUniverse, Prepend[Rest[levels], normalizeLevel[levelSuccessor[First[levels], 1]]],
		True, levels
	]
]

(* the level u with Sort (u + 1) the translation of Sort l, max(l, 1): l less one, or 0 for Prop; a universe
   parameter that may be 0 has none, and stays, so what uses it fails to check *)
loweredUniverse[level_Integer] := Max[level, 1] - 1
loweredUniverse[levelSuccessor[base_, k_Integer]] /; k >= 1 := normalizeLevel[levelSuccessor[base, k - 1]]
(* Sort (max (a + 1) (b + 1)) is Sort (max a b + 1), as for the motive of a recursion over pairs of two types *)
loweredUniverse[level : levelMaximum[parts__]] /; lowerableUniverseQ[level] := normalizeLevel[levelMaximum @@ (loweredUniverse /@ {parts})]
loweredUniverse[level_] := level

(* a level that is never 0, so it has one less: a positive number, a successor, or the maximum of such *)
lowerableUniverseQ[level_Integer] := level >= 1
lowerableUniverseQ[levelSuccessor[_, k_Integer]] := k >= 1
lowerableUniverseQ[levelMaximum[parts__]] := AllTrue[{parts}, lowerableUniverseQ]
lowerableUniverseQ[_] := False

(* each registration of the natural numbers is replayed as soon as the constants it names are declared *)
registerWhenDeclared[replayed_, settings_Association] := With[
	{next = Replace[naturalNumberSettings[replayed], {registered_Association :> Length[registered["Registrations"]] + 1, None -> 1}]},
	If[ next <= Length[settings["Registrations"]] && AllTrue[registrationNames[settings, next], Function[name, constantDeclaredQ[replayed, name]]],
		registerWhenDeclared[registerNaturalNumbers[replayed, registrationOf[settings, next]], settings],
		replayed
	]
]
registerWhenDeclared[replayed_, None] := replayed


(* ::Subsection:: *)
(*Proof trees*)


(* The natural-deduction derivation of a proof of propositional logic. Its leading functions of propositions bind its atoms;
   then each part is a rule by its form, its claim the type the part has where it stands, which must be a formula over the
   atoms: a hypothesis is an assumption, a function of a proof an implication introduced, "andIntroduction",
   "andEliminationLeft" and "andEliminationRight", the two introductions of Or, Or's recursor and "falseElimination" their rules,
   and any other application an implication eliminated. A constant applied to formulas, as "excludedMiddle"[p], is an open
   assumption. A part whose claim is not a formula, as a proof of 2 == 2, or that has another form, makes the whole
   Missing["Untranslatable"]. *)
proofTree[environment_, term_] := Catch[
	withCheckedTerms[atomsOpened[environment, <||>, First[checkedQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]]]],
	untranslatable
]

(* the tree of a core term, as a finished proof's own term, which reading it back could leave without its implicit
   arguments *)
coreProofTree[environment_, core_] := Catch[withCheckedTerms[atomsOpened[environment, <||>, core]], untranslatable]

atomsOpened[environment_, context_, lambdaAbstraction[name_, universeSort[0], body_, binder_]] :=
	atomOpened[environment, context, name, binder, body, freshFreeVariable[]]
atomsOpened[environment_, context_, term_] := derivation[environment, context, term]

atomOpened[environment_, context_, name_, binder_, body_, id_] :=
	atomsOpened[environment, extendContext[context, id, name, universeSort[0], binder], instantiateBoundVariable[body, freeVariable[id]]]

notTranslated[] := Throw[Missing["Untranslatable"], untranslatable]

propositionTypeQ[environment_, context_, type_] := levelEquivalentQ[sortLevel[environment, context, type], 0]

(* a formula of propositional logic over the atoms: an atom, True, False, a conjunction, a disjunction, a negation, or an
   implication, a function type whose codomain does not mention its binder *)
formulaQ[context_, freeVariable[id_]] := MatchQ[Lookup[context, id, <||>], KeyValuePattern["Type" -> universeSort[0]]]
formulaQ[_, constantReference[HoldComplete[True | False], {}]] := True
formulaQ[context_, dependentFunctionType[_, domain_, codomain_, _]] := looseBoundRange[codomain] == 0 && formulaQ[context, domain] && formulaQ[context, codomain]
formulaQ[context_, term_application] := connectiveFormulaQ[context, applicationSpine[term]]
formulaQ[_, _] := False

connectiveFormulaQ[context_, {constantReference[HoldComplete[And | Or], {}], {left_, right_}}] := formulaQ[context, left] && formulaQ[context, right]
connectiveFormulaQ[context_, {constantReference[HoldComplete[Not], {}], {negated_}}] := formulaQ[context, negated]
connectiveFormulaQ[_, _] := False

(* the claim beta-normal, as a recursor's type is its motive applied to the major premise *)
derivation[environment_, context_, term_] := derivationOf[environment, context, term, betaNormalize[inferType[environment, context, term]]]

derivationOf[environment_, context_, term_, claim_] := If[formulaQ[context, claim], derivationNode[environment, context, term, claim], notTranslated[]]

treeNode[environment_, context_, rule_String, claim_, premises_List] := TypeTheoryProofTree[rule, coreToTypeTheoryTerm[environment, context, claim], premises]

derivationNode[environment_, context_, freeVariable[_], claim_] := treeNode[environment, context, "Assumption", claim, {}]
derivationNode[environment_, context_, constantReference[_, _], claim_] := treeNode[environment, context, "Assumption", claim, {}]
derivationNode[environment_, context_, lambdaAbstraction[name_, domain_, body_, binder_], claim_] := If[
	propositionTypeQ[environment, context, domain],
	treeNode[environment, context, "ImpliesIntro", claim, {assumed[environment, context, name, domain, binder, body, freshFreeVariable[]]}],
	notTranslated[]
]
derivationNode[environment_, context_, term_application, claim_] := applicationDerivation[environment, context, applicationSpine[term], term, claim]
derivationNode[___] := notTranslated[]

(* the derivation of body with its bound variable, a proof of domain, among the hypotheses *)
assumed[environment_, context_, name_, domain_, binder_, body_, id_] :=
	derivation[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[body, freeVariable[id]]]

applicationDerivation[environment_, context_, {constantReference[HoldComplete["andIntroduction"], _], {_, _, left_, right_}}, _, claim_] :=
	treeNode[environment, context, "AndIntro", claim, {derivation[environment, context, left], derivation[environment, context, right]}]
applicationDerivation[environment_, context_, {constantReference[HoldComplete["andEliminationLeft" | "andEliminationRight"], _], {_, _, conjunction_}}, _, claim_] :=
	treeNode[environment, context, "AndElim", claim, {derivation[environment, context, conjunction]}]
applicationDerivation[environment_, context_, {constantReference[HoldComplete["orIntroductionLeft" | "orIntroductionRight"], _], {_, _, disjunct_}}, _, claim_] :=
	treeNode[environment, context, "OrIntro", claim, {derivation[environment, context, disjunct]}]
applicationDerivation[
	environment_,
	context_,
	{constantReference[HoldComplete[InductiveRecursor[Or]], _], {left_, right_, _, leftCase_, rightCase_, disjunction_}},
	_,
	claim_
] := treeNode[environment, context, "OrElim", claim, {
	derivation[environment, context, disjunction],
	caseDerivation[environment, context, left, leftCase],
	caseDerivation[environment, context, right, rightCase]
}]
applicationDerivation[environment_, context_, {constantReference[HoldComplete["falseElimination"], _], {_, falsity_}}, _, claim_] :=
	treeNode[environment, context, "FalseElim", claim, {derivation[environment, context, falsity]}]
(* a constant applied to formulas is an open assumption, and any proofs it is applied to after them eliminate implications *)
applicationDerivation[environment_, context_, {head_constantReference, arguments_List}, _, claim_] := If[
	AllTrue[arguments, Function[argument, formulaQ[context, argument]]],
	treeNode[environment, context, "Assumption", claim, {}],
	treeNode[environment, context, "ImpliesElim", claim, {derivation[environment, context, makeApplication[head, Most[arguments]]], derivation[environment, context, Last[arguments]]}]
]
applicationDerivation[environment_, context_, _, application[function_, argument_], claim_] :=
	treeNode[environment, context, "ImpliesElim", claim, {derivation[environment, context, function], derivation[environment, context, argument]}]

(* a case of Or's recursor proves its claim from one disjunct: the body of a function of it, or the case applied to it *)
caseDerivation[environment_, context_, _, lambdaAbstraction[name_, domain_, body_, binder_]] := assumed[environment, context, name, domain, binder, body, freshFreeVariable[]]
caseDerivation[environment_, context_, disjunct_, case_] := caseApplied[environment, context, disjunct, case, freshFreeVariable[]]

caseApplied[environment_, context_, disjunct_, case_, id_] :=
	derivation[environment, extendContext[context, id, HoldComplete[h], disjunct, "Explicit"], makeApplication[case, {freeVariable[id]}]]
