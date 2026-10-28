(* ::Package:: *)

(* Tests for Checking/Quantities.wl: binders of quantity 0, 1 and Infinity under rules with quantities, the
   live check that counts how many times the code that runs uses a variable, the quantities the kernel
   gives constructors and recursors, function types that differ in quantity, and forged records. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

affineRules = TypeTheoryRules["CalculusOfInductiveConstructions", "Quantities" -> True]

translated = TypeTheoryTranslate[TypeTheoryEnvironment["Prelude"], affineRules, "Axioms" -> True]

prelude = translated["Environment"]

(* pairs whose fields are affine, A ⊗ B *)
affine = TypeTheoryEnvironment[prelude, {
	TypeTheoryInductiveType[CircleTimes, TypeSpecifier[{TypeUniverse[1], TypeUniverse[1]} -> TypeUniverse[1]], {
		Tensor -> ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[a, A, 1], Typed[b, B, 1]}, CircleTimes[A, B]]
	}]
}]

swap = TypeTheoryDefinition[swap, Function[{TypedImplicit[A, TypeUniverse[1], 0], TypedImplicit[B, TypeUniverse[1], 0], Typed[p, CircleTimes[A, B], 1]},
	InductiveRecursor[CircleTimes][Function[{Typed[q, CircleTimes[A, B]]}, CircleTimes[B, A]], Function[{Typed[a, A], Typed[b, B]}, Tensor[b, a]], p]
]]

(* the value stays unevaluated, as in a declaration: Function would complain of a binder with a quantity *)
SetAttributes[definitionFailure, HoldRest]
definitionFailure[environment_, value_] := Replace[TypeTheoryEnvironment[environment, {TypeTheoryDefinition[f, value]}], {failure_Failure :> First[failure], _ -> "Checked"}]

(* the quantities of a function type's binders, in order *)
quantities[TypeTheoryTerm[ForAll[binders_List, body_], ___]] := Join[
	Replace[binders, {(Typed | TypedImplicit)[_, _, quantity_] :> quantity, _ -> Infinity}, {1}],
	quantities[TypeTheoryTerm[body]]
]
quantities[TypeTheoryTerm[TypeSpecifier[{_} -> body_], ___]] := Prepend[quantities[TypeTheoryTerm[body]], Infinity]
quantities[_] := {}

(* a copy of the environment's store with one record changed by hand *)
forge[TypeTheoryEnvironment[store_Symbol], name_HoldComplete, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy["Records"] = MapAt[change, copy["Records"], Key[name]];
	TypeTheoryEnvironment[copy]
]


VerificationTest[
	{
		First @ TypeTheoryEnvironment[TypeTheoryEnvironment["Prelude"], {TypeTheoryDefinition[f, Function[{Typed[n, NonNegativeIntegers, 1]}, n]]}],
		First @ TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[f, Function[{Typed[n, NonNegativeIntegers, 2]}, n]]}],
		definitionFailure[prelude, Function[{Typed[n, NonNegativeIntegers, Infinity]}, n + n]]
	},
	{"QuantitiesNotAllowed", "ElaborationFailed", "Checked"},
	TestID -> "Quantities-need-rules-that-have-them"
]

VerificationTest[
	{
		translated["Failures"],
		quantities[TypeOf[TypeTheoryTerm[InductiveRecursor[CartesianProductType], prelude]]],
		quantities[TypeOf[TypeTheoryTerm[InductiveRecursor[NonNegativeIntegers], prelude]]],
		quantities[TypeOf[TypeTheoryTerm[Pair, prelude]]],
		Information[prelude, "Kinds"]["Quotient"]
	},
	{<||>, {0, 0, 0, 1, 1}, {0, Infinity, Infinity, Infinity}, {0, 0, Infinity, Infinity}, 4},
	TestID -> "The-prelude-translates-with-quantities"
]

VerificationTest[
	{
		MatchQ[TypeTheoryEnvironment[affine, {swap}], _TypeTheoryEnvironment],
		definitionFailure[affine, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A, 1]}, Tensor[x, x]]],
		definitionFailure[affine, Function[{TypedImplicit[A, TypeUniverse[1], 0], TypedImplicit[B, TypeUniverse[1], 0], Typed[x, A, 1], Typed[y, B, 1]}, x]]
	},
	{True, "QuantityExceeded", "Checked"},
	TestID -> "An-affine-variable-is-used-at-most-once"
]

(* the parameters of Equal's constructor are erased, so the proof mentions n only where it is dead *)
VerificationTest[
	{
		definitionFailure[prelude, Function[{Typed[n, NonNegativeIntegers, 0]}, n]],
		definitionFailure[prelude, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A]}, x]],
		MatchQ[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[reflexive, ForAll[{Typed[n, NonNegativeIntegers, 0]}, n == n], Function[{Typed[n, NonNegativeIntegers, 0]}, EqualityReflexivity[n]]]}], _TypeTheoryEnvironment]
	},
	{"QuantityExceeded", "Checked", True},
	TestID -> "An-erased-variable-appears-only-in-dead-parts"
]

VerificationTest[
	{
		definitionFailure[prelude, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[f, TypeSpecifier[{A} -> A], 1], Typed[x, A]}, f[x]]],
		definitionFailure[prelude, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[f, TypeSpecifier[{A} -> A], 1], Typed[x, A]}, f[f[x]]]],
		definitionFailure[prelude, Function[{Typed[n, NonNegativeIntegers, 1]}, n + 1]]
	},
	{"Checked", "QuantityExceeded", "QuantityExceeded"},
	TestID -> "An-argument-counts-as-often-as-its-binder-says"
]

VerificationTest[
	{
		definitionFailure[affine, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A, 1]}, With[{y = x}, Tensor[y, y]]]],
		definitionFailure[affine, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A, 1]}, With[{y = x}, y]]]
	},
	{"QuantityExceeded", "Checked"},
	TestID -> "A-local-definition-counts-as-often-as-it-is-used"
]

(* the branches of a match add up; a recursion takes its argument at quantity Infinity *)
VerificationTest[
	{
		definitionFailure[prelude, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[b, Booleans, 1], Typed[x, A, 1]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, A], x, x, b]]],
		definitionFailure[prelude, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[b, Booleans, 1], Typed[x, A, 1]},
			InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, ForAll[{Typed[y, A, 1]}, A]], Function[{Typed[y, A, 1]}, y], Function[{Typed[y, A, 1]}, y], b][x]
		]],
		definitionFailure[prelude, Function[{Typed[n, NonNegativeIntegers, 1]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers], 0, Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, r], n]]],
		definitionFailure[prelude, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers], 0, Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, r], n]]]
	},
	{"QuantityExceeded", "Checked", "QuantityExceeded", "Checked"},
	TestID -> "Matches-add-up-their-branches-and-recursion-copies"
]

VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers], prelude], TypeTheoryTerm[TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers], prelude]],
		DefinitionallyEqualQ[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers], prelude], TypeTheoryTerm[ForAll[{Typed[y, NonNegativeIntegers, 1]}, NonNegativeIntegers], prelude]],
		First @ TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, x], prelude], TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers], prelude]],
		First @ TypeTheoryCheck[TypeTheoryTerm[Function[{x}, x], prelude], TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers], prelude]],
		First @ TypeTheoryCheck[TypeTheoryTerm[Function[{x}, x + x], prelude], TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers], prelude]]
	},
	{False, True, "TypeChecked", "TypeChecked", "QuantityExceeded"},
	TestID -> "Function-types-differ-in-quantity"
]

VerificationTest[
	With[{environment = TypeTheoryEnvironment[affine, {swap}]},
		{
			First @ TypeTheoryCheck[environment],
			With[{duplicate = First[TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[f, Typed[Function[{Typed[x, NonNegativeIntegers]}, x + x], ForAll[{Typed[x, NonNegativeIntegers]}, NonNegativeIntegers]]]}]]["Records"][HoldComplete[f]]["Value"]},
				First @ TypeTheoryCheck[forge[
					TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[g, Typed[Function[{Typed[x, NonNegativeIntegers, 1]}, x], ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers]]]}],
					HoldComplete[g],
					Function[record, Append[record, "Value" -> Replace[duplicate, lambda_ :> ReplacePart[lambda, 4 -> {"Explicit", 1}]]]]
				]]
			],
			(* a recursion on an affine natural number *)
			First @ TypeTheoryCheck[forge[prelude, HoldComplete[InductiveRecursor[NonNegativeIntegers]], Function[record, Append[record, "Type" -> ReplacePart[record["Type"], {3, 3, 3, 4} -> {"Explicit", 1}]]]]]
		}
	],
	{"EnvironmentChecked", "QuantityExceeded", "DeclarationMismatch"},
	TestID -> "A-forged-record-is-caught"
]

VerificationTest[
	With[
		{
			rewriting = TypeTheoryEnvironment[TypeTheoryTranslate[TypeTheoryEnvironment["Prelude"], TypeTheoryRules[affineRules, "RewriteRules" -> True]]["Environment"], {
				TypeTheoryAxiom[consume, ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers]]
			}]
		},
		{
			MatchQ[TypeTheoryEnvironment[rewriting, {TypeTheoryRewriteRule[consumeComputes, ForAll[{Typed[x, NonNegativeIntegers]}, consume[x] -> x]]}], _TypeTheoryEnvironment],
			First @ TypeTheoryEnvironment[rewriting, {TypeTheoryRewriteRule[consumeCopies, ForAll[{Typed[x, NonNegativeIntegers]}, consume[x] -> x + x]]}]
		}
	],
	{True, "RewriteRuleQuantity"},
	TestID -> "A-rewrite-rule-may-not-copy-what-its-left-side-uses-once"
]

VerificationTest[
	With[{back = TypeTheoryTranslate[TypeTheoryEnvironment[affine, {swap}], TypeTheoryRules["CalculusOfInductiveConstructions"], "Axioms" -> True]},
		{back["Failures"], quantities[TypeOf[TypeTheoryTerm[swap, back["Environment"]]]]}
	],
	{<||>, {Infinity, Infinity, Infinity}},
	TestID -> "A-translation-to-rules-without-quantities-drops-them"
]
