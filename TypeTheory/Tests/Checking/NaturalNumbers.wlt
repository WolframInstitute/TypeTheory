(* ::Package:: *)

(* Tests for Checking/NaturalNumbers.wl: only an inductive type of the right shape can be registered as
   the natural numbers, and only operations of the right types; the kernel computes those on literals. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

(* the prelude up to, and without, its natural numbers *)
beforeNaturalNumbers = TypeTheoryEnvironment[TypeTheoryEnvironment[], TakeWhile[Normal[prelude], Function[declaration, Head[declaration] =!= TypeTheoryNaturalNumbers]]]


VerificationTest[
	Information[Append[beforeNaturalNumbers, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor"]], "NaturalNumbers"],
	<|"Type" -> NonNegativeIntegers, "Zero" -> "zero", "Successor" -> "successor", "Operations" -> <||>|>,
	TestID -> "The-natural-numbers-register-without-operations"
]

VerificationTest[
	First @ Append[beforeNaturalNumbers, TypeTheoryNaturalNumbers[NonNegativeIntegers, "successor", "zero"]],
	"InvalidNaturalNumbers",
	TestID -> "Zero-and-successor-cannot-be-swapped"
]

VerificationTest[
	First /@ {
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Quotient" -> NaturalNumberPredecessor|>]],
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Modulo" -> Times|>]],
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Addition" -> Times|>]],
		Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"GCD" -> Times|>]]
	},
	{"InvalidNaturalNumberOperation", "InvalidNaturalNumberOperation", "InvalidNaturalNumberOperation", "InvalidNaturalNumberOperation"},
	TestID -> "An-operation-needs-the-type-of-a-role-that-is-free"
]

VerificationTest[
	First /@ {
		WeakHeadNormalForm[TypeTheoryTerm[2^64 - 1]],
		WeakHeadNormalForm[TypeTheoryTerm[123456789 * 987654321]],
		WeakHeadNormalForm[TypeTheoryTerm[3 - 5]],
		WeakHeadNormalForm[TypeTheoryTerm[0^0]],
		WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n * 2][2^100]]]
	},
	{18446744073709551615, 121932631112635269, 0, 1, 2535301200456458802993406410752},
	TestID -> "The-prelude-computes-its-arithmetic-on-literals"
]

(* the prelude up to, and without, the registration of its comparisons of natural numbers *)
beforeComparisons = TypeTheoryEnvironment[
	TypeTheoryEnvironment[],
	TakeWhile[Normal[prelude], Function[declaration, ! MatchQ[declaration, TypeTheoryNaturalNumbers[_, _, _, operations_Association /; KeyExistsQ[operations, "Equal"]]]]]
]

VerificationTest[
	{
		First /@ {
			WeakHeadNormalForm[TypeTheoryTerm["equal"[2^70, 2^70]]],
			WeakHeadNormalForm[TypeTheoryTerm["lessEqual"[2^70 + 1, 2^70]]],
			WeakHeadNormalForm[TypeTheoryTerm[Decide[12^3 + 1 == 9^3 + 10^3]]]
		},
		Information[prelude, "NaturalNumbers"]["Operations"]["Equal"]
	},
	{{"true", "false", "true"}, "equal"},
	TestID -> "The-prelude-compares-literals-on-Booleans-in-one-step"
]

(* a comparison of its own, registered by the alias Naturals on the prelude without its comparisons *)
withEquality = TypeTheoryEnvironment[beforeComparisons, {
	TypeTheoryDefinition[
		NaturalNumberEqual,
		Function[{Typed[m, Naturals], Typed[n, Naturals]},
			InductiveRecursor[Naturals][Function[{Typed[t, Naturals]}, Booleans], "true", Function[{Typed[k, Naturals], Typed[r, Booleans]}, "false"], (m - n) + (n - m)]
		]
	],
	TypeTheoryNaturalNumbers[Naturals, "zero", "successor", <|"Equal" -> NaturalNumberEqual|>]
}]

VerificationTest[
	{
		First /@ {WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberEqual[2^70, 2^70], withEquality]], WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberEqual[2^70, 2^70 + 1], withEquality]]},
		Information[withEquality, "NaturalNumbers"]["Operations"]["Equal"],
		Count[Normal[withEquality], _TypeTheoryNaturalNumbers],
		MatchQ[TypeTheoryCheck[withEquality], _Success]
	},
	{{"true", "false"}, NaturalNumberEqual, 3, True},
	TestID -> "A-later-registration-adds-an-operation-with-Boolean-values"
]

(* the kernel trusts a registration to compute on literals: here a projection registered as multiplication computes as
   multiplication *)
VerificationTest[
	First @ WeakHeadNormalForm[TypeTheoryTerm[FirstNumber[2, 3], TypeTheoryEnvironment[beforeNaturalNumbers, {
		TypeTheoryDefinition[
			FirstNumber,
			Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
		],
		TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Multiplication" -> FirstNumber|>]
	}]]],
	6,
	TestID -> "A-registered-operation-is-trusted"
]

(* an addition must satisfy its defining equations by computation, which the offset rule reads terms by: a
   projection, or an addition by recursion on its first argument, which computes the literals right, is refused *)
VerificationTest[
	{
		Lookup[Last @ TypeTheoryEnvironment[beforeNaturalNumbers, {
			TypeTheoryDefinition[
				FirstNumber,
				Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
			],
			TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", FirstNumber]
		}], "MessageParameters"],
		Lookup[Last @ TypeTheoryEnvironment[beforeNaturalNumbers, {
			TypeTheoryDefinition[
				AdditionOnTheFirst,
				Typed[
					Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
						InductiveRecursor[NonNegativeIntegers][Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers], n, Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, "successor"[r]], m]
					],
					TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
				]
			],
			TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", AdditionOnTheFirst]
		}], "MessageParameters"]
	},
	{{HoldForm[FirstNumber], "t + successor[s] == successor[t + s]"}, {HoldForm[AdditionOnTheFirst], "t + zero == t"}},
	TestID -> "An-addition-is-refused-unless-its-defining-equations-hold"
]

VerificationTest[
	First @ TypeTheoryEnvironment[TypeTheoryEnvironment[], {
		TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
		TypeTheoryNaturalNumbers[Bit, BitZero, BitOne]
	}],
	"InvalidNaturalNumbers",
	TestID -> "A-type-without-a-successor-cannot-be-registered"
]

VerificationTest[
	First @ Append[prelude, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor"]],
	"NaturalNumbersRegistered",
	TestID -> "The-natural-numbers-are-registered-once"
]

VerificationTest[
	First @ TypeTheoryType[TypeTheoryTerm[3, beforeNaturalNumbers]],
	"ElaborationFailed",
	TestID -> "Literals-need-natural-numbers"
]


(* ::Section:: *)
(*Offsets*)


(* the offset rule of definitional equality, compared with unfolding alone ($naturalOffsetRule = False) on every pair of
   terms from five bases with offsets 0 to 4, each written as successors, as the base plus a literal, and as the base
   plus zero plus a literal; scripts/offset_agreement.wls compares offsets 0 to 12 *)
offsetDefinitionallyEqualQ = WolframInstitute`TypeTheory`PackageScope`definitionallyEqualQ
offsetReference[name_] := WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[name], {}]
offsetApplication[head_, arguments__] := Fold[WolframInstitute`TypeTheory`PackageScope`application, head, {arguments}]
offsetLiteral[n_] := WolframInstitute`TypeTheory`PackageScope`naturalLiteral[n]
offsetVariables = {WolframInstitute`TypeTheory`PackageScope`freshFreeVariable[], WolframInstitute`TypeTheory`PackageScope`freshFreeVariable[]}
offsetContext = Fold[
	Function[{context, id}, WolframInstitute`TypeTheory`PackageScope`extendContext[context, id, HoldComplete["v"], offsetReference[NonNegativeIntegers], "Explicit"]],
	<||>,
	offsetVariables
]
{offsetX, offsetY} = WolframInstitute`TypeTheory`PackageScope`freeVariable /@ offsetVariables
offsetPlus[a_, b_] := offsetApplication[offsetReference[Plus], a, b]
offsetSuccessor[a_] := offsetApplication[offsetReference["successor"], a]
offsetBases = {offsetReference["zero"], offsetX, offsetY, offsetSuccessor[offsetX], offsetPlus[offsetX, offsetY]}
offsetForms[base_, k_] := {Nest[offsetSuccessor, base, k], offsetPlus[base, offsetLiteral[k]], offsetPlus[base, offsetPlus[offsetLiteral[0], offsetLiteral[k]]]}
offsetTerms = Flatten[Outer[offsetForms, offsetBases, Range[0, 4]], 2]

VerificationTest[
	Module[{pairs = Tuples[offsetTerms, 2], withRule, withoutRule},
		withRule = Function[pair, offsetDefinitionallyEqualQ[prelude, offsetContext, First[pair], Last[pair]]] /@ pairs;
		withoutRule = Block[{WolframInstitute`TypeTheory`PackageScope`$naturalOffsetRule = False},
			Function[pair, offsetDefinitionallyEqualQ[prelude, offsetContext, First[pair], Last[pair]]] /@ pairs
		];
		{Length[pairs], withRule === withoutRule, Count[withRule, True] > Length[offsetTerms]}
	],
	{5625, True, True},
	TestID -> "The-offset-rule-agrees-with-unfolding-on-small-offsets"
]

(* large offsets: a common base with offsets k and k' is equal exactly where k == k', two different variables never *)
VerificationTest[
	BlockRandom[
		SeedRandom[2026];
		Module[{offsets = RandomInteger[{0, 2^64}, {100, 2}]},
			AllTrue[
				Join[offsets, Function[pair, {First[pair], First[pair]}] /@ Take[offsets, 20]],
				Function[pair, And[
					offsetDefinitionallyEqualQ[prelude, offsetContext, offsetPlus[offsetX, offsetLiteral[First[pair]]], offsetPlus[offsetPlus[offsetX, offsetLiteral[1]], offsetLiteral[Last[pair] - 1]]] === (First[pair] == Last[pair]),
					offsetDefinitionallyEqualQ[prelude, offsetContext, offsetPlus[offsetX, offsetLiteral[First[pair]]], offsetPlus[offsetY, offsetLiteral[First[pair]]]] === False
				]]
			]
		]
	],
	True,
	TestID -> "Large-offsets-are-equal-exactly-where-they-are-the-same"
]

(* t + (u + 3) and (t + u) + 3 are equal by the rule; (t + 3) + u and (t + u) + 3 only propositionally, which the rule
   leaves to unfolding; a literal 0 + 5 in the offset is read *)
VerificationTest[
	{
		offsetDefinitionallyEqualQ[prelude, offsetContext, offsetPlus[offsetX, offsetPlus[offsetY, offsetLiteral[3]]], offsetPlus[offsetPlus[offsetX, offsetY], offsetLiteral[3]]],
		offsetDefinitionallyEqualQ[prelude, offsetContext, offsetPlus[offsetPlus[offsetX, offsetLiteral[3]], offsetY], offsetPlus[offsetPlus[offsetX, offsetY], offsetLiteral[3]]],
		offsetDefinitionallyEqualQ[prelude, offsetContext, offsetPlus[offsetX, offsetPlus[offsetLiteral[0], offsetLiteral[5]]], offsetPlus[offsetX, offsetLiteral[5]]]
	},
	{True, False, True},
	TestID -> "The-offset-rule-reads-through-the-addition-and-no-further"
]

(* a forged proof of an equation whose offsets differ, or whose bases do, is still refused *)
VerificationTest[
	{
		First[TypeTheoryEnvironment[{TypeTheoryTheorem[ForgedOffset, ForAll[{x}, x + 5 == x + 6], Function[{Typed[x, NonNegativeIntegers]}, "equalityReflexivity"[x + 5]]]}]],
		First[TypeTheoryEnvironment[{TypeTheoryTheorem[ForgedBase, ForAll[{x, y}, x + 5 == y + 5], Function[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, "equalityReflexivity"[x + 5]]]}]],
		First[TypeTheoryEnvironment[{TypeTheoryTheorem[ForgedLarge, ForAll[{x}, x + 9223372036854775808 == x + 9223372036854775809], Function[{Typed[x, NonNegativeIntegers]}, "equalityReflexivity"[x + 9223372036854775808]]]}]]
	},
	{"TypeMismatch", "TypeMismatch", "TypeMismatch"},
	TestID -> "A-forged-proof-of-different-offsets-is-refused"
]

(* where a side has offset 0 over a base that is not zero, the base reduces: to three successors of x, found equal to
   x + 3, or stuck, an application of a variable, found unequal, each without a loop *)
VerificationTest[
	Module[{threeMore, f = WolframInstitute`TypeTheory`PackageScope`freshFreeVariable[], natural = offsetReference[NonNegativeIntegers], functionType},
		functionType = With[{domain = natural}, WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete["n"], domain, domain, "Explicit"]];
		threeMore = TypeTheoryEnvironment[prelude, {TypeTheoryDefinition[ThreeMore, Typed[n, NonNegativeIntegers] |-> "successor"["successor"["successor"[n]]]]}];
		TimeConstrained[
			{
				offsetDefinitionallyEqualQ[threeMore, offsetContext, offsetApplication[offsetReference[ThreeMore], offsetX], offsetPlus[offsetX, offsetLiteral[3]]],
				offsetDefinitionallyEqualQ[
					threeMore,
					WolframInstitute`TypeTheory`PackageScope`extendContext[offsetContext, f, HoldComplete["f"], functionType, "Explicit"],
					offsetApplication[WolframInstitute`TypeTheory`PackageScope`freeVariable[f], offsetX],
					offsetPlus[offsetX, offsetLiteral[3]]
				]
			},
			20,
			"TIMEOUT"
		]
	],
	{True, False},
	TestID -> "A-side-without-an-offset-reduces-and-the-rule-ends"
]

(* the literal value of a term is read by its offset, so asking whether m + c is a literal finds the base m at once: a
   lemma with c = 2^63 proves, where peeling c successors would not finish; held under a memory and a time limit *)
VerificationTest[
	With[{c = 9223372036854775808},
		MemoryConstrained[
			TimeConstrained[TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m + (c + 0) == (0 + (m + c)) + 0], {"Introduce"[m], "LinearArithmetic"}]["Goals"], 60, "TIMEOUT"],
			2*^9,
			"MEMORY"
		]
	],
	{},
	TestID -> "A-lemma-with-an-offset-of-2-to-the-63-proves"
]

(* the literal value is read in a loop, not by recursion: a definition by recursion whose step is two successors has its
   value, however many reductions it takes *)
VerificationTest[
	With[
		{
			twice = TypeTheoryEnvironment[{TypeTheoryDefinition[OffsetTwice, n |-> InductiveRecursor[Naturals][Naturals &, 0, {k, r} |-> "successor"["successor"[r]], n]]}],
			literalValue = Symbol["WolframInstitute`TypeTheory`Checking`NaturalNumbers`Private`literalValue"],
			elaborated = Symbol[First[Names["WolframInstitute`TypeTheory`*`elaborateQueryTerm"]]]
		},
		With[{core = First[elaborated[twice, TypeTheoryTerm[OffsetTwice[2900], twice], None, {}]]},
			MemoryConstrained[
				TimeConstrained[Quiet[literalValue[twice, <||>, WolframInstitute`TypeTheory`PackageScope`naturalNumberSettings[twice], core]], 60, "TIMEOUT"],
				2*^9,
				"MEMORY"
			]
		]
	],
	5800,
	TestID -> "A-literal-value-many-reductions-deep-is-read-in-a-loop"
]

(* a sum with a variable in it is no literal, which is read without reducing the other side: so a multiplication by a
   large literal, which unfolds into additions of a variable sum, is not reduced to see it *)
VerificationTest[
	With[{c = 9223372036854775808},
		MemoryConstrained[
			TimeConstrained[
				TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[c == m + 1 + k, c + (0 + 0 + 0) == ((m + 1) + k) + 0]], {"Introduce"[m, k, e], "LinearArithmetic"}]["Goals"],
				60,
				"TIMEOUT"
			],
			2*^9,
			"MEMORY"
		]
	],
	{},
	TestID -> "A-lemma-with-a-hypothesis-and-an-offset-of-2-to-the-63-proves"
]

(* the offset rule is a loop, at one depth however many rounds it takes: a recursion by two successors 2900 deep against
   a numeral is 1450 rounds, where a definitional equality for each would overflow the stack *)
VerificationTest[
	With[{twice = TypeTheoryEnvironment[{TypeTheoryDefinition[OffsetTwice, n |-> InductiveRecursor[Naturals][Naturals &, 0, {k, r} |-> "successor"["successor"[r]], n]]}]},
		MemoryConstrained[
			TimeConstrained[
				{
					DefinitionallyEqualQ[TypeTheoryTerm[OffsetTwice[2900] + 1, twice], TypeTheoryTerm[5801, twice]],
					DefinitionallyEqualQ[TypeTheoryTerm[OffsetTwice[2900] + 1, twice], TypeTheoryTerm[5802, twice]]
				},
				60,
				"TIMEOUT"
			],
			2*^9,
			"MEMORY"
		]
	],
	{True, False},
	TestID -> "The-offset-rule-compares-a-deep-recursion-in-a-loop"
]

(* the registered addition reduces by its equations, its recursion folded, so the offset of an integer's component stays
   readable: a natural number below 2^63 is in the range of the machine integers, which the first component of the
   pair of m + 2^63 met as 2^63 successors peeled one by one *)
VerificationTest[
	With[{c = 9223372036854775808, lower = -9223372036854775808},
		MemoryConstrained[
			TimeConstrained[
				Module[{environment = TypeTheoryEnvironment["Integers", {TypeTheoryDefinition["offsetRange", Typed[Typed[x, Integers] |-> Typed[lower, Integers] <= x && x < Typed[c, Integers], Integers -> TypeUniverse[0]]]}]},
					environment = TypeTheoryEnvironment[environment, {TypeTheoryTheorem["offsetLowerRelation", TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m + (c + 0) == (0 + (m + c)) + 0], environment, {"Introduce"[m], "LinearArithmetic"}]]}];
					environment = TypeTheoryEnvironment[environment, {TypeTheoryTheorem["offsetUpperRelation", TypeTheoryProof[
						ForAll[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[c == m + 1 + k, c + (0 + 0 + 0) == ((m + 1) + k) + 0]],
						environment,
						{"Introduce"[m, k, e], "LinearArithmetic"}
					]]}];
					Head[TypeTheoryEnvironment[environment, {TypeTheoryTheorem["offsetNaturalRange", TypeTheoryProof[
						ForAll[{Typed[m, NonNegativeIntegers]}, Implies[m < c, "offsetRange"["integerOfNatural"[m]]]],
						environment,
						{
							"Introduce"[m, h], "Constructor",
							"Exact"["existsIntroduction"[m + c, "quotientSoundness"["offsetLowerRelation"[m]]]],
							"Exact"[InductiveRecursor[Exists][
								Typed[w, Exists[{Typed[k, NonNegativeIntegers]}, c == m + 1 + k]] |-> "integerOfNatural"[m] < Typed[c, Integers],
								{Typed[k, NonNegativeIntegers], Typed[e, c == m + 1 + k]} |-> "existsIntroduction"[k, "quotientSoundness"["offsetUpperRelation"[m, k, e]]],
								"lessEqualWitness"[m + 1, c, h]
							]]
						}
					]]}]]
				],
				120,
				"TIMEOUT"
			],
			2*^9,
			"MEMORY"
		]
	],
	TypeTheoryEnvironment,
	TestID -> "A-natural-number-below-2-to-the-63-is-in-the-range-of-the-machine-integers"
]
