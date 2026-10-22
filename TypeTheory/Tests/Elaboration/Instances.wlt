(* ::Package:: *)

(* Tests for the instances and coercions of Elaboration/Elaboration.wl: an instance-implicit argument is
   found among the definitions declared with "Instance" -> True, its own instance arguments in turn, and a
   term whose type is not the one expected is coerced by the definitions declared with "Coercion" -> True;
   the kernel checks the terms found as any other. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

(* the class of inhabited types, a default element of each, and instances for the naturals, the
   Booleans, lists and pairs; then the coercions of the Booleans to the naturals and of any element to its
   option *)
environment = TypeTheoryEnvironment[prelude, {
	TypeTheoryInductiveType[Inhabited, ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]]}, TypeUniverse[u + 1]], {
		InhabitedIntroduction -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]]}, Inhabited[\[Alpha]]]
	}],
	TypeTheoryDefinition[Default, Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Annotation[Typed[h, Inhabited[\[Alpha]]], "InstanceImplicit"]}, h[[1]]]],
	TypeTheoryDefinition[NaturalsInhabited, Typed[InhabitedIntroduction[0], Inhabited[NonNegativeIntegers]], "Instance" -> True],
	TypeTheoryDefinition[BooleansInhabited, Typed[InhabitedIntroduction["false"], Inhabited[Booleans]], "Instance" -> True],
	TypeTheoryDefinition[ListsInhabited, Typed[
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, InhabitedIntroduction[EmptyList]],
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, Inhabited[Lists[\[Alpha]]]]
	], "Instance" -> True],
	TypeTheoryDefinition[PairInhabited, Typed[
		Function[
			{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Annotation[Typed[h, Inhabited[\[Alpha]]], "InstanceImplicit"], Annotation[Typed[k, Inhabited[\[Beta]]], "InstanceImplicit"]},
			InhabitedIntroduction[Pair[h[[1]], k[[1]]]]
		],
		ForAll[
			{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Annotation[Typed[h, Inhabited[\[Alpha]]], "InstanceImplicit"], Annotation[Typed[k, Inhabited[\[Beta]]], "InstanceImplicit"]},
			Inhabited[CartesianProduct[\[Alpha], \[Beta]]]
		]
	], "Instance" -> True],
	TypeTheoryDefinition[NaturalOfBoolean, Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, NonNegativeIntegers], 0, 1, b]], "Coercion" -> True],
	TypeTheoryDefinition[OptionOf, Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]]}, OptionSome[x]], "Coercion" -> True]
}]

(* a copy of the environment's store with one record changed by hand *)
forge[TypeTheoryEnvironment[store_Symbol], name_HoldComplete, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy["Records"] = MapAt[change, copy["Records"], Key[name]];
	TypeTheoryEnvironment[copy]
]


VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Typed[Default, NonNegativeIntegers], environment]],
		WeakHeadNormalForm[TypeTheoryTerm[Typed[Default, Booleans], environment]]
	},
	{TypeTheoryTerm[0, environment], TypeTheoryTerm["false", environment]},
	TestID -> "An-instance-implicit-argument-is-found-among-the-instances"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Typed[Default, CartesianProduct[NonNegativeIntegers, Lists[Booleans]]], environment]],
	TypeTheoryTerm[Pair[NaturalsInhabited[[1]], ListsInhabited[[1]]], environment],
	TestID -> "An-instance-finds-its-own-instance-arguments"
]

VerificationTest[
	First @ TypeOf[TypeTheoryTerm[Typed[Default, Option[NonNegativeIntegers]], environment]],
	"NoInstance",
	TestID -> "No-instance-is-a-failure"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[environment], _Success],
		MemberQ[Normal[environment], TypeTheoryDefinition[NaturalsInhabited, _, "Instance" -> True]],
		MemberQ[Normal[environment], TypeTheoryDefinition[NaturalOfBoolean, _, "Coercion" -> True]]
	},
	{True, True, True},
	TestID -> "Instances-and-coercions-replay-with-their-options"
]

VerificationTest[
	First /@ {
		TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[NotAnInstance, Typed[NonNegativeIntegers, TypeUniverse[1]], "Instance" -> True]}],
		TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[NotACoercion, Typed[0, NonNegativeIntegers], "Coercion" -> True]}],
		TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[NotAnOption, 0, "Instance" -> 2]}]
	},
	{"InstanceTypeExpected", "CoercionTypeExpected", "InvalidOption"},
	TestID -> "The-options-Instance-and-Coercion-are-checked"
]

(* the instance for the naturals forged with the value of the one for the Booleans *)
VerificationTest[
	{
		First @ TypeTheoryEnvironment[prelude, {
			TypeTheoryDefinition[WrongCoercion, Typed[Function[{Typed[b, Booleans]}, b], TypeSpecifier[{Booleans} -> NonNegativeIntegers]], "Coercion" -> True]
		}],
		With[{booleanValue = First[environment]["Records"][HoldComplete[BooleansInhabited]]["Value"]},
			First @ TypeTheoryCheck[forge[environment, HoldComplete[NaturalsInhabited], Function[record, Append[record, "Value" -> booleanValue]]]]
		]
	},
	{"TypeMismatch", "TypeMismatch"},
	TestID -> "A-forged-instance-is-caught"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Typed["true", NonNegativeIntegers], environment]],
		WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberSuccessor["true"], environment]],
		First @ TypeOf[TypeTheoryTerm[Typed["true", NonNegativeIntegers], prelude]]
	},
	{TypeTheoryTerm[1, environment], TypeTheoryTerm[NaturalNumberSuccessor[NaturalOfBoolean["true"]], environment], "TypeMismatch"},
	TestID -> "A-term-of-another-type-is-coerced"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Typed[3, Option[NonNegativeIntegers]], environment]],
		WeakHeadNormalForm[TypeTheoryTerm[Typed["true", Option[NonNegativeIntegers]], environment]],
		First @ TypeOf[TypeTheoryTerm[Typed[EmptyList, NonNegativeIntegers], environment]]
	},
	{TypeTheoryTerm[OptionSome[3], environment], TypeTheoryTerm[OptionSome[NaturalOfBoolean["true"]], environment], "TypeMismatch"},
	TestID -> "Coercions-are-polymorphic-and-chain"
]
