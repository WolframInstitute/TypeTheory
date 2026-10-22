(* ::Package:: *)

(*
Quantities: how many times the code that runs may use a variable, under rules whose "Quantities" is True,
after BendTT's affine dependent type theory.

Every binder has a quantity. A variable of quantity 0 is erased: only the dead parts of a term may mention
it, the parts that are gone when it runs. A variable of quantity 1 is affine: the code that runs uses it
at most once. A variable of quantity Infinity, the quantity of a binder written without one, may be used
any number of times. A binder carries its quantity with its kind, as {kind, 0} or {kind, 1}, and a binder
that is its kind alone has the quantity Infinity (CoreTerms.wl).

The dead parts of a term are its types, a function's domain, both parts of a function type, a universe
and the type of a local definition, and the arguments a function takes at quantity 0. The rest is live,
and the value of a definition and the proof of a theorem are. The live check counts the live uses of
each variable: an argument that a function takes at quantity q counts q times its own uses, and the value
of a local definition counts as many times as the body uses its variable. A function whose body uses its
variable more than its binder's quantity allows is rejected. The counts are 0, 1 and Infinity, which
stands for more than once: 1 + 1 is Infinity.

The kernel gives the binders of an inductive type's constructors and recursor their quantities
(InductiveTypes.wl). The parameters of a constructor are erased, and so are the parameters, motives and
indices of a recursor. The recursor of a block without a recursive field takes its minor premises and its
major premise at quantity 1, and passes each field on at the quantity the constructor takes it: a match
on a pair uses the pair once. The uses of the minor premises add up, since every branch of a match is
part of the term until it computes. The recursor of a block with a recursive field takes them at
quantity Infinity, since a recursive call uses the fields of its argument again.

Two function types are equal only if their binders have the same quantity, so a function that uses its
argument once and one that copies it have different types. Nothing else about checking changes: the
rules only reject more terms, so they are consistent whenever the same rules without quantities are.

checkBinderQuantity, checkLiveUses and checkRewriteRuleUses are part of the trusted kernel.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[checkBinderQuantity]
PackageScoped[checkLiveUses]
PackageScoped[checkRewriteRuleUses]
PackageScoped[erasedBinder]
PackageScoped[multiplyQuantities]


(* ::Section:: *)
(*Usage Messages*)


checkBinderQuantity::usage = "checkBinderQuantity[environment, HoldComplete[name], binder] throws a kernel failure unless binder is a kind, or {kind, 0} or {kind, 1} under rules with quantities."
checkLiveUses::usage = "checkLiveUses[environment, term] throws a kernel failure if a function in a live part of term uses its variable more than its binder's quantity allows."
checkRewriteRuleUses::usage = "checkRewriteRuleUses[environment, HoldComplete[name], numberOfVariables, left, right] throws a kernel failure if the right side of the rewrite rule \
uses one of its variables more than the left side does, or if a function in either side uses its variable more than its binder's quantity allows."
erasedBinder::usage = "erasedBinder[environment, kind] gives the binder of the given kind at quantity 0 under rules with quantities, and the kind alone otherwise."
multiplyQuantities::usage = "multiplyQuantities[p, q] gives the product of the quantities p and q, each 0, 1 or Infinity."


(* ::Section:: *)
(*Function Definitions*)


(* ::Subsection:: *)
(*Binders*)


checkBinderQuantity[_, _, _String] := Null
checkBinderQuantity[environment_, _, {_String, 0 | 1}] /; rulesSetting[environment, "Quantities"] := Null
checkBinderQuantity[_, name_, {_String, quantity : 0 | 1}] :=
	kernelFailure["QuantitiesNotAllowed", "The binder of `1` has the quantity `2`, which the rules of the environment do not allow.", {HoldForm @@ name, quantity}]
checkBinderQuantity[_, _, binder_] := kernelFailure["IllFormedTerm", "`1` is not a binder.", {binder}]

erasedBinder[environment_, kind_String] := If[rulesSetting[environment, "Quantities"], quantifiedBinder[kind, 0], kind]


(* ::Subsection:: *)
(*Counting*)


addQuantities[0, quantity_] := quantity
addQuantities[quantity_, 0] := quantity
addQuantities[_, _] := Infinity

multiplyQuantities[0, _] := 0
multiplyQuantities[_, 0] := 0
multiplyQuantities[1, quantity_] := quantity
multiplyQuantities[quantity_, 1] := quantity
multiplyQuantities[_, _] := Infinity

quantityAtMostQ[used_, allowed_] := used === 0 || allowed === Infinity || used === allowed

(* the uses of variables, an Association from each variable's id to its count, 1 or Infinity *)
addUses[uses_, other_] := Merge[{uses, other}, Function[counts, Fold[addQuantities, 0, counts]]]

scaledUses[0, _] := <||>
scaledUses[1, uses_] := uses
scaledUses[quantity_, uses_] := Map[Function[count, multiplyQuantities[quantity, count]], uses]


(* ::Subsection:: *)
(*The live check*)


(* Only a function whose binder has quantity 0 or 1 can be refused, so a term without one is not walked,
   as no term of rules without quantities is. Within one check a term means the same wherever it occurs,
   its free variables being fresh for each binder opened, so the uses of each are worked out once. *)
checkLiveUses[environment_, term_] := If[ ! FreeQ[term, lambdaAbstraction[_, _, _, {_String, _}]],
	Block[{$liveUses = <||>}, liveUses[environment, <||>, term]]
]

liveUses[environment_, context_, term_] := Lookup[$liveUses, Key[term], $liveUses[term] = liveUsesOf[environment, context, term]]

liveUsesOf[environment_, context_, term_] := Replace[term, {
	freeVariable[id_] :> <|id -> 1|>,
	_application :> applicationUses[environment, context, applicationSpine[term]],
	lambdaAbstraction[name_, domain_, body_, binder_] :> functionUses[environment, context, name, domain, body, binder],
	localDefinition[name_, type_, value_, body_] :> localDefinitionUses[environment, context, name, type, value, body],
	projection[_, _, structureTerm_] :> liveUses[environment, context, structureTerm],
	(* a universe, a constant, a literal or a function type: closed, or dead *)
	_ :> <||>
}]

(* each argument counts as many times as the binder of the function's type that takes it says *)
applicationUses[environment_, context_, {head_, arguments_List}] := First @ Fold[
	Function[{state, argument}, Replace[weakHeadNormalForm[environment, context, Last[state]], {
		dependentFunctionType[_, _, codomain_, binder_] :> {
			addUses[First[state], argumentUses[environment, context, binderQuantity[binder], argument]],
			instantiateBoundVariable[codomain, argument]
		},
		other_ :> kernelFailure["FunctionExpected", "`1` is not a function type.", {displayCoreTerm[environment, context, other]}]
	}]],
	{liveUses[environment, context, head], inferType[environment, context, head]},
	arguments
]

argumentUses[_, _, 0, _] := <||>
argumentUses[environment_, context_, quantity_, argument_] := scaledUses[quantity, liveUses[environment, context, argument]]

functionUses[environment_, context_, name_, domain_, body_, binder_] := With[{id = freshFreeVariable[]},
	With[{uses = liveUses[environment, extendContext[context, id, name, domain, binder], instantiateBoundVariable[body, freeVariable[id]]]},
		If[ ! quantityAtMostQ[Lookup[uses, id, 0], binderQuantity[binder]],
			quantityFailure[name, binderQuantity[binder]]
		];
		KeyDrop[uses, id]
	]
]

(* the value counts once for each use of its variable, as putting it in the body would make it *)
localDefinitionUses[environment_, context_, name_, type_, value_, body_] := With[{id = freshFreeVariable[]},
	With[{uses = liveUses[environment, extendLocalDefinition[context, id, name, type, value], instantiateBoundVariable[body, freeVariable[id]]]},
		addUses[KeyDrop[uses, id], argumentUses[environment, context, Lookup[uses, id, 0], value]]
	]
]

quantityFailure[name_, 0] := kernelFailure["QuantityExceeded", "`1` is erased, of quantity 0, but the code that runs uses it.", {HoldForm @@ name}]
quantityFailure[name_, _] := kernelFailure["QuantityExceeded", "`1` has quantity 1, but the code that runs uses it more than once.", {HoldForm @@ name}]


(* ::Subsection:: *)
(*Rewrite rules*)


(* a rewrite rule may not copy what its left side uses once, nor use what it erases *)
checkRewriteRuleUses[environment_, name_HoldComplete, numberOfVariables_Integer, left_, right_] := Block[{$liveUses = <||>},
	With[{opened = Fold[openRuleVariable, <|"Context" -> <||>, "Ids" -> {}, "Left" -> left, "Right" -> right|>, Range[numberOfVariables]]},
		With[
			{
				leftUses = liveUses[environment, opened["Context"], opened["Left"]],
				rightUses = liveUses[environment, opened["Context"], opened["Right"]]
			},
			Scan[
				Function[id, If[ ! quantityAtMostQ[Lookup[rightUses, id, 0], Lookup[leftUses, id, 0]],
					kernelFailure["RewriteRuleQuantity", "The right side of the rewrite rule `1` uses its variable `2` more than its left side does.", {HoldForm @@ name, HoldForm @@ opened["Context"][id]["Name"]}]
				]],
				opened["Ids"]
			]
		]
	]
]

openRuleVariable[state_, _] := Replace[{state["Left"], state["Right"]}, {
	{lambdaAbstraction[name_, domain_, leftBody_, binder_], lambdaAbstraction[_, _, rightBody_, _]} :> With[{id = freshFreeVariable[]},
		<|
			"Context" -> extendContext[state["Context"], id, name, domain, binder],
			"Ids" -> Append[state["Ids"], id],
			"Left" -> instantiateBoundVariable[leftBody, freeVariable[id]],
			"Right" -> instantiateBoundVariable[rightBody, freeVariable[id]]
		|>
	],
	_ :> kernelFailure["RewriteRuleSpecification", "The sides of a rewrite rule must be functions of its variables.", {}]
}]
