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

(* a comparison of its own, registered by the alias Naturals on the prelude without its comparisons: by recursion on
   both arguments, as its defining equations hold by computation; (m - n) + (n - m) == 0 is equal to it only by proof,
   and is refused *)
withEquality = TypeTheoryEnvironment[beforeComparisons, {
	TypeTheoryDefinition[
		NaturalNumberEqual,
		Typed[
			Function[{Typed[m, Naturals]}, InductiveRecursor[Naturals][
				Function[{Typed[a, Naturals]}, Naturals -> Booleans],
				Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][Function[{Typed[c, Naturals]}, Booleans], "true", Function[{Typed[c, Naturals], Typed[r, Booleans]}, "false"], n]],
				Function[{Typed[a, Naturals], Typed[ih, Naturals -> Booleans]}, Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][Function[{Typed[c, Naturals]}, Booleans], "false", Function[{Typed[c, Naturals], Typed[r, Booleans]}, ih[c]], n]]],
				m
			]],
			Naturals -> Naturals -> Booleans
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

(* the kernel trusts the registration of an operation without defining equations to compute on literals: here a
   projection registered as the greatest common divisor computes as the greatest common divisor *)
VerificationTest[
	First @ WeakHeadNormalForm[TypeTheoryTerm[FirstNumber[2, 3], TypeTheoryEnvironment[beforeNaturalNumbers, {
		TypeTheoryDefinition[
			FirstNumber,
			Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
		],
		TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"GCD" -> FirstNumber|>]
	}]]],
	1,
	TestID -> "A-registered-operation-is-trusted"
]

(* an operation with defining equations is checked against them, as addition is: a projection is no multiplication, a
   constant true is no equality, and a multiplication needs an addition registered, which its equations use *)
VerificationTest[
	With[
		{
			first = TypeTheoryDefinition[FirstNumber, Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]],
			beforeComparisons = TypeTheoryEnvironment[TypeTheoryEnvironment[], TakeWhile[Normal[prelude], Function[declaration, ! MatchQ[declaration, TypeTheoryNaturalNumbers[_, _, _, operations_Association /; KeyExistsQ[operations, "Equal"]]]]]]
		},
		{
			Lookup[Last @ TypeTheoryEnvironment[beforeNaturalNumbers, {TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", Plus], first, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Multiplication" -> FirstNumber|>]}], "MessageParameters"],
			Lookup[Last @ TypeTheoryEnvironment[beforeComparisons, {
				TypeTheoryDefinition[AlwaysTrue, Typed[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]} |-> "true", NonNegativeIntegers -> NonNegativeIntegers -> Booleans]],
				TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Equal" -> AlwaysTrue|>]
			}], "MessageParameters"],
			Lookup[Last @ TypeTheoryEnvironment[beforeNaturalNumbers, {first, TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Multiplication" -> FirstNumber|>]}], "MessageParameters"]
		}
	],
	{
		{HoldForm[FirstNumber], "Multiplication", "t * zero == zero"},
		{HoldForm[AlwaysTrue], "Equal", "equal[zero, successor[s]] == false"},
		{HoldForm[FirstNumber], "Multiplication", "Addition"}
	},
	TestID -> "An-operation-with-defining-equations-is-refused-unless-they-hold"
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
	{{HoldForm[FirstNumber], "Addition", "t + successor[s] == successor[t + s]"}, {HoldForm[AdditionOnTheFirst], "Addition", "t + zero == t"}},
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

(* an equality equal to the reference only by proof, isZero[(m - n) + (n - m)], does not satisfy its defining equations
   by computation, and is refused *)
VerificationTest[
	Last[Lookup[Last @ TypeTheoryEnvironment[beforeComparisons, {
		TypeTheoryDefinition[
			DifferenceEqual,
			Function[{Typed[m, Naturals], Typed[n, Naturals]},
				InductiveRecursor[Naturals][Function[{Typed[t, Naturals]}, Booleans], "true", Function[{Typed[k, Naturals], Typed[r, Booleans]}, "false"], (m - n) + (n - m)]
			]
		],
		TypeTheoryNaturalNumbers[Naturals, "zero", "successor", <|"Equal" -> DifferenceEqual|>]
	}], "MessageParameters"]],
	"equal[successor[t], zero] == false",
	TestID -> "An-equality-equal-to-the-reference-only-by-proof-is-refused"
]

(* a quotient and a remainder by recursion on the dividend, the remainder counted up to the divisor and back to zero and
   decided by the registered equality, satisfy their equations by computation: they are checked, and a theorem that
   computes with them on literals rests on nothing trusted; 7 = 3 * 2 + 1, and with the divisor 0 the quotient is 0
   and the remainder the dividend *)
VerificationTest[
	With[
		{
			divided = TypeTheoryEnvironment[prelude, {
				TypeTheoryDefinition["remainderOf", Function[{Typed[dividend, NonNegativeIntegers], Typed[divisor, NonNegativeIntegers]},
					InductiveRecursor[NonNegativeIntegers][
						Function[{Typed[n, NonNegativeIntegers]}, NonNegativeIntegers],
						0,
						Function[{Typed[n, NonNegativeIntegers], Typed[remainder, NonNegativeIntegers]},
							InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, NonNegativeIntegers], remainder + 1, 0, "equal"[remainder + 1, divisor]]
						],
						dividend
					]
				]],
				TypeTheoryDefinition["quotientOf", Function[{Typed[dividend, NonNegativeIntegers], Typed[divisor, NonNegativeIntegers]},
					InductiveRecursor[NonNegativeIntegers][
						Function[{Typed[n, NonNegativeIntegers]}, NonNegativeIntegers],
						0,
						Function[{Typed[n, NonNegativeIntegers], Typed[quotient, NonNegativeIntegers]},
							InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, NonNegativeIntegers], quotient, quotient + 1, "equal"["remainderOf"[n, divisor] + 1, divisor]]
						],
						dividend
					]
				]],
				TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Quotient" -> "quotientOf", "Remainder" -> "remainderOf"|>]
			}]
		},
		{
			TypeTheoryAxiomClosure[TypeTheoryProof[TypeTheoryTerm["quotientOf"[7, 2] == 3 && "remainderOf"[7, 2] == 1, divided], {"Decide"}]],
			First /@ {WeakHeadNormalForm[TypeTheoryTerm["quotientOf"[7, 0], divided]], WeakHeadNormalForm[TypeTheoryTerm["remainderOf"[7, 0], divided]]}
		}
	],
	{<||>, {0, 7}},
	TestID -> "A-quotient-and-a-remainder-that-meet-their-equations-are-checked"
]

(* a quotient that does not meet its equations, as a projection, is accepted and trusted, as any function defined by
   well-founded recursion, which does not compute on a variable, has to be: it computes the quotient on literals, 0 for
   2 / 3, and unfolds to 2, so 0 == 2, a proof of False, and the axiom closure names the registration it rests on;
   an operation of a role the kernel reads terms through is refused instead, as a multiplication *)
VerificationTest[
	With[
		{
			lied = TypeTheoryEnvironment[beforeNaturalNumbers, {
				TypeTheoryDefinition[
					FirstNumber,
					Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
				],
				TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Quotient" -> FirstNumber|>]
			}]
		},
		{
			First @ WeakHeadNormalForm[TypeTheoryTerm[FirstNumber[2, 3], lied]],
			TypeTheoryAxiomClosure[TypeTheoryTerm[Typed["equalityReflexivity"[FirstNumber[2, 3]], FirstNumber[2, 3] == 0], lied]],
			FailureQ[TypeTheoryEnvironment[lied, {TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Multiplication" -> FirstNumber|>]}]]
		}
	],
	{0, <|FirstNumber -> "Registration"|>, True},
	TestID -> "A-quotient-that-fails-its-equations-is-trusted-and-named"
]

(* the products, powers and differences read as stuck are those no literal can be, by the operations' defining equations:
   n 0 and n^0 still compute to 0 and 1, and n - 0 to n, where n 5, n^5 and n - 5 are no literal *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n 0], TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> 0]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n^0], TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> 1]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n - 0], TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n 5], TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n 4 + n]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n^5], TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> 5]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> 3 5], TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> 15]]
	},
	{True, True, True, True, False, True},
	TestID -> "Products-powers-and-differences-compute-to-literals-where-their-equations-give-them"
]


(* A beta reduction computes each registered operation on literals that its substitution builds: the pair of 2 + 2 and 2
   is the pair of 4 and 2 as soon as it exists. What it computes is what the kernel computes of the operation at a head,
   so a proof by it is a proof of 2 + 2 == 4 and of nothing else: the forged 2 + 2 == 5 is refused, written out or
   through the reduction. An operation that is not registered is left as it is built. *)
VerificationTest[
	With[
		{
			literals = Function[{environment, held},
				Cases[
					WolframInstitute`TypeTheory`PackageScope`weakHeadNormalForm[environment, <||>, First[WolframInstitute`TypeTheory`PackageScope`elaborateClosedTerm[environment, held, None, {}]]],
					WolframInstitute`TypeTheory`PackageScope`naturalLiteral[n_] :> n,
					{0, Infinity}
				]
			],
			unregistered = TypeTheoryEnvironment[prelude, {TypeTheoryAxiom["otherPlus", Naturals -> Naturals -> Naturals]}]
		},
		{
			literals[prelude, HoldComplete[(Typed[x, Naturals] |-> "pair"[x + 2, x])[2]]],
			literals[prelude, HoldComplete[(Typed[x, Naturals] |-> "pair"[x 3 + x, x])[2]]],
			literals[unregistered, HoldComplete[(Typed[x, Naturals] |-> "pair"["otherPlus"[x, 2], x])[2]]],
			Head[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem["sumIsFour", 2 + 2 == 4, (Typed[x, Naturals] |-> "equalityReflexivity"[x + 2])[2]]}]],
			FailureQ[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem["forgedSum", 2 + 2 == 5, (Typed[x, Naturals] |-> "equalityReflexivity"[x + 2])[2]]}]],
			FailureQ[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem["forgedSumWritten", 2 + 2 == 5, "equalityReflexivity"[4]]}]],
			FailureQ[TypeTheoryEnvironment[unregistered, {TypeTheoryTheorem["forgedOther", "otherPlus"[2, 2] == 4, (Typed[x, Naturals] |-> "equalityReflexivity"["otherPlus"[x, 2]])[2]]}]]
		}
	],
	{{4, 2}, {8, 2}, {2, 2, 2}, TypeTheoryEnvironment, True, True, True},
	TestID -> "A-beta-reduction-computes-the-registered-operations-on-literals-it-builds-and-no-forged-sum"
]


(* ::Section:: *)
(*Registrations checked by the compiled kernel*)


(* natural numbers and Booleans of their own, with an operation for each role that has equations, by recursion *)
countDeclarations = {
	TypeTheoryInductiveType["Count", TypeUniverse[1], {"none" -> "Count", "more" -> ("Count" -> "Count")}],
	TypeTheoryInductiveType["Flag", TypeUniverse[1], {"no" -> "Flag", "yes" -> "Flag"}],
	TypeTheoryDefinition["sum", Typed[
		Function[{Typed[t, "Count"], Typed[s, "Count"]}, InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Count"], t, Function[{Typed[k, "Count"], Typed[r, "Count"]}, "more"[r]], s]],
		"Count" -> "Count" -> "Count"]],
	TypeTheoryDefinition["product", Typed[
		Function[{Typed[t, "Count"], Typed[s, "Count"]}, InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Count"], "none", Function[{Typed[k, "Count"], Typed[r, "Count"]}, "sum"[r, t]], s]],
		"Count" -> "Count" -> "Count"]],
	TypeTheoryDefinition["raised", Typed[
		Function[{Typed[t, "Count"], Typed[s, "Count"]}, InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Count"], "more"["none"], Function[{Typed[k, "Count"], Typed[r, "Count"]}, "product"[r, t]], s]],
		"Count" -> "Count" -> "Count"]],
	TypeTheoryDefinition["before", Typed[
		Function[{Typed[n, "Count"]}, InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Count"], "none", Function[{Typed[k, "Count"], Typed[r, "Count"]}, k], n]],
		"Count" -> "Count"]],
	TypeTheoryDefinition["less", Typed[
		Function[{Typed[t, "Count"], Typed[s, "Count"]}, InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Count"], t, Function[{Typed[k, "Count"], Typed[r, "Count"]}, "before"[r]], s]],
		"Count" -> "Count" -> "Count"]],
	TypeTheoryDefinition["same", Typed[
		Function[{Typed[a, "Count"]}, InductiveRecursor["Count"][
			Function[{Typed[x, "Count"]}, "Count" -> "Flag"],
			Function[{Typed[b, "Count"]}, InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Flag"], "yes", Function[{Typed[k, "Count"], Typed[r, "Flag"]}, "no"], b]],
			Function[{Typed[k, "Count"], Typed[f, "Count" -> "Flag"]}, Function[{Typed[b, "Count"]},
				InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Flag"], "no", Function[{Typed[j, "Count"], Typed[r, "Flag"]}, f[j]], b]]],
			a
		]],
		"Count" -> "Count" -> "Flag"]],
	TypeTheoryDefinition["atMost", Typed[
		Function[{Typed[a, "Count"]}, InductiveRecursor["Count"][
			Function[{Typed[x, "Count"]}, "Count" -> "Flag"],
			Function[{Typed[b, "Count"]}, "yes"],
			Function[{Typed[k, "Count"], Typed[f, "Count" -> "Flag"]}, Function[{Typed[b, "Count"]},
				InductiveRecursor["Count"][Function[{Typed[x, "Count"]}, "Flag"], "no", Function[{Typed[j, "Count"], Typed[r, "Flag"]}, f[j]], b]]],
			a
		]],
		"Count" -> "Count" -> "Flag"]]
};
(* {role, the registrations it needs first, an operation that has the role's equations, one of the same type that is another function} *)
roleFixtures = {
	{"Addition", <||>, "sum", "product"},
	{"Multiplication", <|"Addition" -> "sum"|>, "product", "raised"},
	{"Power", <|"Addition" -> "sum", "Multiplication" -> "product"|>, "raised", "less"},
	{"Subtraction", <||>, "less", "sum"},
	{"Equal", <||>, "same", "atMost"},
	{"LessEqual", <||>, "atMost", "same"}
};

counted = TypeTheoryEnvironment[TypeTheoryEnvironment[], countDeclarations]

countRegistered[base_, operations_] := TypeTheoryEnvironment[base, {TypeTheoryNaturalNumbers @@ {"Count", "none", "more", operations}}]

(* the natural numbers of counted with the operations a role needs first *)
countBase[needed_] := countRegistered[counted, needed]

registrationsOf[environment_] := Replace[WolframInstitute`TypeTheory`PackageScope`naturalNumberSettings[environment], {settings_Association :> Length[settings["Registrations"]], _ -> 0}]

(* the registration made with its equations left to the compiled kernel, as a list of declarations checked at once
   makes it, and unchecked until the compiled kernel checks it *)
countDeferred[base_, operations_] := Block[{WolframInstitute`TypeTheory`PackageScope`$deferRegistrationEquations = True}, countRegistered[base, operations]]

(* the verdict of the comparison by the kernel of TypeChecking.wl, and of the compiled kernel alone on the same
   registration: "accepted", or the registration, the role and the equation that fails *)
comparisonVerdict[base_, operations_] := Replace[countRegistered[base, operations], {failure_Failure :> failure["MessageParameters"], _ -> "accepted"}]
compiledVerdict[base_, operations_] := Replace[countDeferred[base, operations], {
	failure_Failure :> failure["MessageParameters"],
	deferred_ :> Replace[WolframInstitute`TypeTheory`PackageScope`compiledKernelCheck[deferred, Length[base], registrationsOf[base]], {
		failure_Failure /; TrueQ[failure["RegistrationEquation"]] :> failure["MessageParameters"],
		_Success -> "accepted",
		other_ :> other
	}]
}]

(* The compiled kernel checks the equations of a registration that have a variable in every application of an operation,
   and the registration then does not compare them. This rests on the compiled kernel computing a registered operation
   only where every argument is a literal, and reading no sum by its offset: if it did either on an open term, it
   would take an equation for true by the registration the equation is to justify. So for each role that refuses, a
   different function of the role's type is offered to the compiled kernel alone, the comparison left out, and it
   must refuse it, with the equation that fails: a product for the sum, a power for the product, a difference for the
   power, a sum for the difference, an order for the equality and an equality for the order. The function that has
   the role's equations it accepts. *)
VerificationTest[
	If[ WolframInstitute`TypeTheory`PackageScope`compiledKernelAvailableQ[],
		Map[Apply[Function[{role, needed, right, wrong}, {role, compiledVerdict[countBase[needed], <|role -> right|>], compiledVerdict[countBase[needed], <|role -> wrong|>]}]], roleFixtures],
		"no compiled kernel"
	],
	{
		{"Addition", "accepted", {HoldForm["product"], "Addition", "t + zero == t"}},
		{"Multiplication", "accepted", {HoldForm["raised"], "Multiplication", "t * zero == zero"}},
		{"Power", "accepted", {HoldForm["less"], "Power", "t ^ zero == successor[zero]"}},
		{"Subtraction", "accepted", {HoldForm["sum"], "Subtraction", "t - successor[s] == predecessor[t - s]"}},
		{"Equal", "accepted", {HoldForm["atMost"], "Equal", "equal[zero, successor[s]] == false"}},
		{"LessEqual", "accepted", {HoldForm["same"], "LessEqual", "lessEqual[zero, s] == true"}}
	} | "no compiled kernel",
	SameTest -> MatchQ,
	TimeConstraint -> 300,
	TestID -> "The-compiled-kernel-alone-refuses-a-different-function-for-each-role"
]

(* the two verdicts are the same, role by role, on the functions above and on others that fail: a projection for each
   operation of numbers, and a comparison that always says yes *)
VerificationTest[
	With[
		{
			more = TypeTheoryEnvironment[counted, {
				TypeTheoryDefinition["firstOf", Typed[Function[{Typed[t, "Count"], Typed[s, "Count"]}, t], "Count" -> "Count" -> "Count"]],
				TypeTheoryDefinition["alwaysYes", Typed[Function[{Typed[t, "Count"], Typed[s, "Count"]}, "yes"], "Count" -> "Count" -> "Flag"]]
			}]
		},
		With[
			{
				cases = Join[
					Catenate[Map[Apply[Function[{role, needed, right, wrong}, {{needed, role, right}, {needed, role, wrong}}]], roleFixtures]],
					Map[Apply[Function[{role, needed, right, wrong}, {needed, role, If[MemberQ[{"Equal", "LessEqual"}, role], "alwaysYes", "firstOf"]}]], roleFixtures]
				],
				base = Function[needed, countRegistered[more, needed]]
			},
			If[ WolframInstitute`TypeTheory`PackageScope`compiledKernelAvailableQ[],
				{
					Length[cases],
					Select[cases, Apply[Function[{needed, role, candidate}, comparisonVerdict[base[needed], <|role -> candidate|>] =!= compiledVerdict[base[needed], <|role -> candidate|>]]]],
					Count[cases, case_ /; comparisonVerdict[base[First[case]], <|case[[2]] -> Last[case]|>] === "accepted"]
				},
				"no compiled kernel"
			]
		]
	],
	{18, {}, 6} | "no compiled kernel",
	SameTest -> MatchQ,
	TimeConstraint -> 300,
	TestID -> "The-compiled-kernels-verdict-on-a-registration-is-the-comparisons"
]

(* A registration that fails keeps its report on the compiled path: a list of declarations checked at once is added
   again one at a time, and the registration names the equation; an environment that holds such a registration, which
   only one made with the comparison left out can, is refused by TypeTheoryCheck with every method, the compiled kernel
   refusing the equation and the registration's own comparison naming it. The comparison is left out only after the
   compiled kernel has accepted the equations: with the kernel of TypeChecking.wl it is made. *)
VerificationTest[
	With[{base = countBase[<||>], forged = countDeferred[countBase[<||>], <|"Addition" -> "product"|>]},
		{
			TypeTheoryEnvironment[base, {TypeTheoryNaturalNumbers["Count", "none", "more", <|"Addition" -> "product"|>]}, Method -> "Compiled"]["MessageParameters"],
			Head[forged],
			Map[
				Function[method, Replace[TypeTheoryCheck[forged, Method -> method], {failure_Failure :> {failure["Tag"], failure["MessageParameters"]}, other_ :> Head[other]}]],
				{Automatic, "Compiled", "Symbolic"}
			],
			Head[TypeTheoryEnvironment[base, {TypeTheoryNaturalNumbers["Count", "none", "more", <|"Addition" -> "sum"|>]}, Method -> "Compiled"]],
			Map[
				Function[method, Head[TypeTheoryCheck[countRegistered[base, <|"Addition" -> "sum"|>], Method -> method]]],
				{Automatic, "Symbolic"}
			]
		}
	],
	{
		{HoldForm["product"], "Addition", "t + zero == t"},
		TypeTheoryEnvironment,
		ConstantArray[{"InvalidNaturalNumberOperation", {HoldForm["product"], "Addition", "t + zero == t"}}, 3]
			| {{"InvalidNaturalNumberOperation", {HoldForm["product"], "Addition", "t + zero == t"}}, {"CompiledKernelUnavailable", _}, {"InvalidNaturalNumberOperation", {HoldForm["product"], "Addition", "t + zero == t"}}},
		TypeTheoryEnvironment,
		{Success, Success}
	},
	SameTest -> MatchQ,
	TimeConstraint -> 300,
	TestID -> "A-registration-that-fails-keeps-its-report-on-the-compiled-path"
]

(* $deferRegistrationEquations switches a comparison of the kernel off, so it is set in three places and no other: its
   value False where it is defined, and True in a Block in the two places where the compiled kernel's check stands for
   the comparison, compiledDeclarations and TypeTheoryCheck. The Kernel's sources are read held, in a context of
   their own, and every Set of the symbol is listed with the definition it is in. *)
VerificationTest[
	Module[{files, definedName, sets},
		files = FileNames["*.wl", FileNameJoin[{Directory[], "TypeTheory", "Kernel"}], Infinity];
		definedName[held_] := Replace[held, {
			HoldComplete[(Set | SetDelayed)[Verbatim[Condition][left_, _], _]] :> definedName[HoldComplete[left := Null]],
			HoldComplete[(Set | SetDelayed)[head_Symbol[___], _]] :> SymbolName[Unevaluated[head]],
			HoldComplete[(Set | SetDelayed)[symbol_Symbol, _]] :> SymbolName[Unevaluated[symbol]],
			_ -> "no definition"
		}];
		sets[file_] := Block[{$Context = "TypeTheoryFlagScan`", $ContextPath = {"System`"}},
			Catenate[Map[
				Function[held, ConstantArray[
					{FileNameTake[file], definedName[held]},
					Count[held, (Set | SetDelayed)[symbol_Symbol, _] /; SymbolName[Unevaluated[symbol]] === "$deferRegistrationEquations", {0, Infinity}, Heads -> True]
				]],
				ReadList[file, HoldComplete[Expression]]
			]]
		];
		{Length[files] > 20, Sort[Catenate[Map[sets, files]]]}
	],
	{True, {{"Declarations.wl", "compiledDeclarations"}, {"NaturalNumbers.wl", "$deferRegistrationEquations"}, {"Queries.wl", "TypeTheoryCheck"}}},
	TestID -> "The-comparison-of-a-registrations-equations-is-left-out-in-two-places-only"
]

