(* ::Package:: *)

(* Tests for Checking/TypeChecking.wl, the trusted kernel: type inference, reduction, definitional
   equality and projections, through the public queries. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

pairs = TypeTheoryEnvironment[prelude, {
	TypeTheoryInductiveType[NaturalPair, TypeUniverse[1], {NaturalPairIntroduction -> ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, NaturalPair]}],
	TypeTheoryInductiveType[Witness, TypeUniverse[0], {WitnessIntroduction -> ForAll[{Typed[a, NonNegativeIntegers], Typed[h, a == a]}, Witness]}]
}]


(* === inference === *)

VerificationTest[
	{TypeTheoryType[TypeTheoryTerm[TypeUniverse[0]]], TypeTheoryType[TypeTheoryTerm[TypeUniverse[1]]], TypeTheoryType[TypeTheoryTerm[1 == 1, prelude]]},
	{TypeTheoryTerm[TypeUniverse[1], prelude], TypeTheoryTerm[TypeUniverse[2], prelude], TypeTheoryTerm[TypeUniverse[0], prelude]},
	TestID -> "Prop-is-in-Type-and-Type-is-in-the-next-universe"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, TypeSpecifier[{A} -> A]]]],
	TypeTheoryTerm[TypeUniverse[2], prelude],
	TestID -> "A-dependent-function-type-lives-in-the-larger-universe"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, Implies[True, True]], prelude]],
	TypeTheoryTerm[TypeUniverse[0], prelude],
	TestID -> "Prop-is-impredicative"
]

VerificationTest[
	FailureQ[TypeTheoryCheck[TypeTheoryTerm[TypeUniverse[1]], TypeTheoryTerm[TypeUniverse[1]]]],
	True,
	TestID -> "Type-is-not-in-Type"
]

VerificationTest[
	First @ TypeTheoryType[TypeTheoryTerm["successor"[True], prelude]],
	"TypeMismatch",
	TestID -> "An-argument-of-the-wrong-type-is-rejected"
]

VerificationTest[
	{TypeTheoryType[TypeTheoryTerm[2 + 3]] === TypeTheoryTerm[NonNegativeIntegers, prelude], First @ TypeTheoryType[TypeTheoryTerm[2 + 3, TypeTheoryEnvironment[]]]},
	{True, "ElaborationFailed"},
	TestID -> "A-term-without-an-environment-is-in-the-prelude"
]


(* === reduction and definitional equality === *)

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, x + 1][41], prelude]],
	TypeTheoryTerm[42, prelude],
	TestID -> "Beta-reduction-and-literal-addition"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[With[{x = 2}, x + x], prelude]],
	TypeTheoryTerm[4, prelude],
	TestID -> "With-binds-a-value"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Not[1 == 2], prelude]],
	TypeTheoryTerm[Implies[1 == 2, False], prelude],
	TestID -> "Definitions-unfold"
]

VerificationTest[
	{DefinitionallyEqualQ[TypeTheoryTerm[2 + 3, prelude], TypeTheoryTerm[5, prelude]], DefinitionallyEqualQ[TypeTheoryTerm[2 + 3, prelude], TypeTheoryTerm[6, prelude]]},
	{True, False},
	TestID -> "Literals-compute"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm["successor"["successor"["zero"]], prelude], TypeTheoryTerm[2]],
	True,
	TestID -> "A-literal-is-its-constructor-form"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm["successor"[2] + 1, prelude], TypeTheoryTerm[4]],
	True,
	TestID -> "Addition-unfolds-on-a-constructor"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, "successor"[n]], prelude], TypeTheoryTerm["successor"]],
	True,
	TestID -> "Eta-equality"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p], Typed[k, p]}, "equalityReflexivity"[h]], prelude],
		TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[h, p], Typed[k, p]}, h == k]]
	], _Success],
	True,
	TestID -> "Two-proofs-of-a-proposition-are-equal"
]


(* === projections === *)

VerificationTest[
	{TypeTheoryType[TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, p[[2]]], pairs]], WeakHeadNormalForm[TypeTheoryTerm[NaturalPairIntroduction[3, 4][[2]], pairs]]},
	{TypeTheoryTerm[NaturalPair -> NonNegativeIntegers, pairs], TypeTheoryTerm[4, pairs]},
	TestID -> "A-projection-has-the-field-type-and-reduces-on-the-constructor"
]

VerificationTest[
	DefinitionallyEqualQ[
		TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, NaturalPairIntroduction[p[[1]], p[[2]]]], pairs],
		TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, p]]
	],
	True,
	TestID -> "Eta-for-structures"
]

VerificationTest[
	{
		First @ TypeTheoryType[TypeTheoryTerm[Function[{Typed[w, Witness]}, w[[1]]], pairs]],
		First @ TypeTheoryType[TypeTheoryTerm[Function[{Typed[w, Witness]}, w[[2]]], pairs]],
		TypeTheoryType[TypeTheoryTerm[Function[{Typed[h, And[True, False]]}, h[[2]]], pairs]]
	},
	{"ProjectionFromProof", "ProjectionFromProof", TypeTheoryTerm[Implies[True && False, False], pairs]},
	TestID -> "Only-proofs-independent-of-data-are-projected-out-of-a-proof"
]

VerificationTest[
	First @ TypeTheoryType[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n[[1]]], prelude]],
	"ElaborationFailed",
	TestID -> "Only-a-structure-has-fields"
]

VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[1, u]]], TypeTheoryTerm[TypeUniverse[u]]],
		DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, v]]], TypeTheoryTerm[TypeUniverse[v]]]
	},
	{True, False},
	TestID -> "The-impredicative-maximum-of-1-and-u-is-u"
]

VerificationTest[
	With[
		{
			pairs = TypeTheoryEnvironment[{
				TypeTheoryInductiveType[NaturalPair, TypeUniverse[1], {NaturalPairIntroduction -> TypeSpecifier[{Naturals, Naturals} -> NaturalPair]}],
				TypeTheoryDefinition[Swap, Function[{Typed[p, NaturalPair]}, InductiveRecursor[NaturalPair][
					Function[{Typed[q, NaturalPair]}, NaturalPair],
					Function[{Typed[a, Naturals], Typed[b, Naturals]}, NaturalPairIntroduction[b, a]],
					p
				]]]
			}]
		},
		DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, Swap[Swap[p]]], pairs], TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, p], pairs]]
	],
	True,
	TestID -> "A-structure-recursor-computes-on-a-variable-by-eta"
]

(* n - 5000 unfolds into a recursion 5000 deep on a variable n, which the comparison needs not do: after
   beta reduction both sides are Subtract applied to equal arguments *)
VerificationTest[
	TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[n, Naturals]}, "equalityReflexivity"[n - 5000]]],
		TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, Function[{Typed[k, Naturals]}, n - k][5000] == n - (4999 + 1)]]
	][[1]],
	"TypeChecked",
	TestID -> "Equal-applications-are-compared-before-their-definitions-unfold"
]

(* Parity[100000] unfolds into a recursion 100000 deep, which the comparison needs not do: ParityAgain is
   defined by Parity, so it is higher and unfolds first, and then both sides are Parity[100000] *)
VerificationTest[
	With[
		{
			parity = TypeTheoryEnvironment[prelude, {
				TypeTheoryDefinition[Parity, Function[{Typed[n, Naturals]},
					InductiveRecursor[Naturals][Function[{Typed[t, Naturals]}, Booleans], "true", Function[{Typed[k, Naturals], Typed[r, Booleans]}, "not"[r]], n]
				]],
				TypeTheoryDefinition[ParityAgain, Function[{Typed[n, Naturals]}, Parity[n]]]
			}]
		},
		{
			DefinitionallyEqualQ[TypeTheoryTerm[ParityAgain[100000], parity], TypeTheoryTerm[Parity[100000], parity]],
			DefinitionallyEqualQ[TypeTheoryTerm[ParityAgain[4], parity], TypeTheoryTerm["true", parity]],
			DefinitionallyEqualQ[TypeTheoryTerm[ParityAgain[3], parity], TypeTheoryTerm[Parity[4], parity]]
		}
	],
	{True, True, False},
	TestID -> "Of-two-definitions-the-higher-unfolds-first"
]

(* FirstOfPair reads a field of a pair, so it is an abbreviation, and unfolds before a regular
   definition: FirstOfPair["pair"[ParityAgain[100000], "false"]] is ParityAgain[100000] at once, where unfolding the higher
   ParityAgain first would run Parity's recursion 100000 deep *)
VerificationTest[
	With[
		{
			pairs = TypeTheoryEnvironment[prelude, {
				TypeTheoryDefinition[Parity, Function[{Typed[n, Naturals]},
					InductiveRecursor[Naturals][Function[{Typed[t, Naturals]}, Booleans], "true", Function[{Typed[k, Naturals], Typed[r, Booleans]}, "not"[r]], n]
				]],
				TypeTheoryDefinition[ParityAgain, Function[{Typed[n, Naturals]}, Parity[n]]],
				TypeTheoryDefinition[FirstOfPair, Function[{Typed[p, CartesianProductType[Booleans, Booleans]]}, p[[1]]]]
			}]
		},
		{
			Lookup[WolframInstitute`TypeTheory`PackageScope`constantRecord[pairs, HoldComplete[FirstOfPair]], "Hint", None],
			Lookup[WolframInstitute`TypeTheory`PackageScope`constantRecord[pairs, HoldComplete[ParityAgain]], "Hint", None],
			DefinitionallyEqualQ[TypeTheoryTerm[FirstOfPair["pair"[ParityAgain[100000], "false"]], pairs], TypeTheoryTerm[ParityAgain[100000], pairs]]
		}
	],
	{"Abbreviation", None, True},
	TimeConstraint -> 10,
	MemoryConstraint -> 2*^9,
	TestID -> "A-projection-function-is-an-abbreviation-and-unfolds-first"
]

(* a variable whose type is a definition that reduces to a function type is applied to as many arguments as that
   type takes, which the kernel finds by reducing the type in the middle of the spine *)
VerificationTest[
	With[
		{
			operations = TypeTheoryEnvironment[prelude, {
				TypeTheoryDefinition[NaturalOperation, Typed[NonNegativeIntegers -> NonNegativeIntegers -> NonNegativeIntegers, TypeUniverse[1]]],
				TypeTheoryDefinition[NaturalOperationOf, Typed[Function[{Typed[n, NonNegativeIntegers]}, NaturalOperation], NonNegativeIntegers -> TypeUniverse[1]]]
			}]
		},
		{
			TypeTheoryType[TypeTheoryTerm[Function[{Typed[f, NaturalOperation]}, f[1, 2]], operations]] === TypeTheoryTerm[NaturalOperation -> NonNegativeIntegers, operations],
			TypeTheoryType[TypeTheoryTerm[Function[{Typed[f, NaturalOperationOf[3]]}, f[1, 2] + f[2, 1]], operations]] === TypeTheoryTerm[NaturalOperationOf[3] -> NonNegativeIntegers, operations]
		}
	],
	{True, True},
	TestID -> "A-function-type-behind-a-definition-is-applied-to-all-its-arguments"
]

VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm[1935], TypeTheoryTerm[1936]],
		DefinitionallyEqualQ[TypeTheoryTerm[1936], TypeTheoryTerm[1935 + 1]]
	},
	{False, True},
	TestID -> "Two-literals-are-compared-by-their-numbers"
]

(* A remainder by unary recursion, as the dividend's successor steps, decided a few hundred steps deep: two hundred
   compute, and a thousand recurse past what Wolfram's stack holds, which gives a failure, not a crashed process *)
VerificationTest[
	With[
		{
			remainders = TypeTheoryEnvironment[{
				TypeTheoryDefinition["remainder", Function[{Typed[dividend, Naturals], Typed[divisor, Naturals]},
					InductiveRecursor[Naturals][
						Function[{Typed[n, Naturals]}, Naturals],
						0,
						Function[{Typed[n, Naturals], Typed[remainder, Naturals]},
							InductiveRecursor[Booleans][Function[{Typed[reached, Booleans]}, Naturals], remainder + 1, 0, Decide[remainder + 1 == divisor]]
						],
						dividend
					]
				]]
			}]
		},
		{
			Head[TypeTheoryProof["remainder"[200, 7] == 4, remainders, {TypeTheoryTactic["Decide"]}]],
			First[TypeTheoryProof["remainder"[1000, 7] == 6, remainders, {TypeTheoryTactic["Decide"]}]]
		}
	],
	{TypeTheoryProof, "RecursionLimit"},
	TestID -> "A-recursion-too-deep-for-the-stack-is-a-failure"
]


(* ::Section:: *)
(*Judgments of Nederpelt and Geuvers*)


(* Judgments from R. Nederpelt and H. Geuvers, Type Theory and Formal Proof (Cambridge, 2014), as José Martín-García
   worked them in his notebook Calculus of Inductive Constructions (WRI, 2015-2017). Each positive judgment is checked
   against the type the book gives, by definitional equality; the propositions are the impredicative encodings of
   chapter 7 in Prop, ⊥ = ∀γ:Prop. γ. The terms of the encodings are TypeTheoryTerm values held by Module variables,
   which a term stands for by its value. *)

(* the sorts of products, Prop impredicative: ∀x:Prop. x is a proposition, ∀x:Type. x is in Type 1; an arrow into a
   proposition is one, whatever its domain; and a variable sort of an arrow is the maximum, imax v v = v *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryType[ForAll[{Typed[x, TypeUniverse[0]]}, x]], TypeTheoryTerm[TypeUniverse[0]]],
		DefinitionallyEqualQ[TypeTheoryType[ForAll[{Typed[x, TypeUniverse[1]]}, x]], TypeTheoryTerm[TypeUniverse[2]]],
		DefinitionallyEqualQ[TypeTheoryType[Typed[a, TypeUniverse[0]] |-> (TypeUniverse[2] -> a)], TypeTheoryTerm[TypeUniverse[0] -> TypeUniverse[0]]],
		DefinitionallyEqualQ[TypeTheoryType[Typed[a, TypeUniverse[0]] |-> (a -> TypeUniverse[2])], TypeTheoryTerm[TypeUniverse[0] -> TypeUniverse[3]]],
		DefinitionallyEqualQ[
			TypeTheoryType[{Typed[d, TypeUniverse[v]], Typed[e, TypeUniverse[v]]} |-> (d -> e)],
			TypeTheoryTerm[TypeUniverse[v] -> TypeUniverse[v] -> TypeUniverse[v]]
		]
	},
	{True, True, True, True, True},
	TestID -> "The-sort-of-a-product-is-impredicative-in-Prop"
]

(* Exercise 3.14: the Church booleans in Prop. Negation instantiates the quantifier of its argument at the type of
   booleans itself, which impredicativity allows, and computes; over Type the same term is refused, as the type of
   booleans is in Type 1 *)
VerificationTest[
	Module[{booleans, true, false, negation, typeBooleans, typeTrue, typeFalse},
		booleans = TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[0]]}, A -> A -> A]];
		true = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[x, A], Typed[y, A]} |-> x];
		false = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[x, A], Typed[y, A]} |-> y];
		negation = TypeTheoryTerm[Typed[z, booleans] |-> z[booleans, false, true]];
		typeBooleans = TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, A -> A -> A]];
		typeTrue = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[x, A], Typed[y, A]} |-> x];
		typeFalse = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[x, A], Typed[y, A]} |-> y];
		{
			DefinitionallyEqualQ[TypeTheoryType[negation], TypeTheoryTerm[booleans -> booleans]],
			DefinitionallyEqualQ[TypeTheoryTerm[negation[true]], false],
			DefinitionallyEqualQ[TypeTheoryTerm[negation[negation[true]]], true],
			First[TypeTheoryType[Typed[z, typeBooleans] |-> z[typeBooleans, typeFalse, typeTrue]]]
		}
	],
	{True, True, True, "TypeMismatch"},
	TestID -> "Church-booleans-in-Prop-negate-by-impredicativity-and-not-in-Type"
]

(* excluded middle, Church-encoded, gives double negation elimination: from iET, which turns β → γ and ¬β → γ into γ,
   λβ x. iET β β (λy. y) (λw. x w β) proves ((β → ⊥) → ⊥) → β *)
VerificationTest[
	Module[{bottom, excludedMiddle},
		bottom = TypeTheoryTerm[ForAll[{Typed[G, TypeUniverse[0]]}, G]];
		excludedMiddle = TypeTheoryTerm[ForAll[{Typed[B, TypeUniverse[0]], Typed[G, TypeUniverse[0]]}, (B -> G) -> ((B -> bottom) -> G) -> G]];
		DefinitionallyEqualQ[
			TypeTheoryType[Typed[iET, excludedMiddle] |-> ({Typed[B, TypeUniverse[0]], Typed[x, (B -> bottom) -> bottom]} |->
				iET[B, B, Typed[y, B] |-> y, Typed[w, B -> bottom] |-> x[w, B]])
			],
			TypeTheoryTerm[excludedMiddle -> ForAll[{Typed[B, TypeUniverse[0]]}, ((B -> bottom) -> bottom) -> B]]
		]
	],
	True,
	TestID -> "Excluded-middle-gives-double-negation-elimination-in-Church-encoding"
]

(* the quantifiers of chapter 7, Church-encoded over a type S and predicates P, Q: ∃x:S. P x is
   ∀α:Prop. (∀x:S. P x → α) → α. Exercise 6.8, ∃ ⇒ ¬∀¬; the example of page 156, ¬∃ ⇒ ∀¬; Exercise 7.14,
   ∃(P ∧ Q) ⇒ ∃P, with P ∧ Q as ∀γ:Prop. (P → Q → γ) → γ *)
VerificationTest[
	Module[{bottom, exists, existsBoth, both},
		bottom = TypeTheoryTerm[ForAll[{Typed[G, TypeUniverse[0]]}, G]];
		{
			DefinitionallyEqualQ[
				TypeTheoryType[{Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[0]]} |-> (
					{Typed[u, ForAll[{Typed[A, TypeUniverse[0]]}, ForAll[{Typed[x, S]}, P[x] -> A] -> A]], Typed[v, ForAll[{Typed[x, S]}, P[x] -> bottom]]} |-> u[bottom, v]
				)],
				TypeTheoryTerm[ForAll[{Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[0]]},
					ForAll[{Typed[A, TypeUniverse[0]]}, ForAll[{Typed[x, S]}, P[x] -> A] -> A] -> ForAll[{Typed[x, S]}, P[x] -> bottom] -> bottom
				]]
			],
			DefinitionallyEqualQ[
				TypeTheoryType[{Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[0]]} |-> (
					{Typed[u, ForAll[{Typed[A, TypeUniverse[0]]}, ForAll[{Typed[x, S]}, P[x] -> A] -> A] -> bottom], Typed[y, S], Typed[v, P[y]]} |->
						u[{Typed[A, TypeUniverse[0]], Typed[w, ForAll[{Typed[x, S]}, P[x] -> A]]} |-> w[y, v]]
				)],
				TypeTheoryTerm[ForAll[{Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[0]]},
					(ForAll[{Typed[A, TypeUniverse[0]]}, ForAll[{Typed[x, S]}, P[x] -> A] -> A] -> bottom) -> ForAll[{Typed[y, S]}, P[y] -> bottom]
				]]
			],
			DefinitionallyEqualQ[
				TypeTheoryType[{Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[0]], Typed[Q, S -> TypeUniverse[0]]} |-> (
					{
						Typed[u, ForAll[{Typed[A, TypeUniverse[0]]}, ForAll[{Typed[x, S]}, ForAll[{Typed[G, TypeUniverse[0]]}, (P[x] -> Q[x] -> G) -> G] -> A] -> A]],
						Typed[A, TypeUniverse[0]],
						Typed[v, ForAll[{Typed[x, S]}, P[x] -> A]]
					} |-> u[A, {Typed[y, S], Typed[w, ForAll[{Typed[G, TypeUniverse[0]]}, (P[y] -> Q[y] -> G) -> G]]} |-> v[y, w[P[y], {Typed[s, P[y]], Typed[t, Q[y]]} |-> s]]]
				)],
				TypeTheoryTerm[ForAll[{Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[0]], Typed[Q, S -> TypeUniverse[0]]},
					ForAll[{Typed[A, TypeUniverse[0]]}, ForAll[{Typed[x, S]}, ForAll[{Typed[G, TypeUniverse[0]]}, (P[x] -> Q[x] -> G) -> G] -> A] -> A] ->
						ForAll[{Typed[A, TypeUniverse[0]]}, ForAll[{Typed[x, S]}, P[x] -> A] -> A]
				]]
			]
		}
	],
	{True, True, True},
	TestID -> "Church-encoded-quantifiers-of-chapter-7-prove-as-the-book-says"
]

(* Exercises 5.10 and 5.11: dependent spines, each codomain instantiated by the arguments before it *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryType[{
				Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[1]], Typed[f, S -> S], Typed[g, S -> S],
				Typed[u, ForAll[{Typed[x, S]}, P[f[x]] -> P[g[x]]]],
				Typed[v, ForAll[{Typed[x, S], Typed[y, S]}, (P[x] -> P[y]) -> P[f[x]]]]
			} |-> (Typed[x, S] |-> v[f[x], g[x], u[x]])],
			TypeTheoryTerm[ForAll[
				{
					Typed[S, TypeUniverse[1]], Typed[P, S -> TypeUniverse[1]], Typed[f, S -> S], Typed[g, S -> S],
					Typed[u, ForAll[{Typed[x, S]}, P[f[x]] -> P[g[x]]]],
					Typed[v, ForAll[{Typed[x, S], Typed[y, S]}, (P[x] -> P[y]) -> P[f[x]]]]
				},
				ForAll[{Typed[x, S]}, P[f[f[x]]]]
			]]
		],
		DefinitionallyEqualQ[
			TypeTheoryType[{
				Typed[S, TypeUniverse[1]], Typed[Q, S -> S -> TypeUniverse[1]], Typed[R, S -> S -> TypeUniverse[1]], Typed[f, S -> S], Typed[g, S -> S],
				Typed[u, ForAll[{Typed[x, S], Typed[y, S]}, Q[x, f[y]] -> Q[g[x], y]]],
				Typed[v, ForAll[{Typed[x, S], Typed[y, S]}, Q[x, f[y]] -> R[x, y]]],
				Typed[w, ForAll[{Typed[x, S]}, Q[x, f[f[x]]]]]
			} |-> (Typed[x, S] |-> v[g[g[x]], g[x], u[g[x], f[g[x]], w[g[x]]]])],
			TypeTheoryTerm[ForAll[
				{
					Typed[S, TypeUniverse[1]], Typed[Q, S -> S -> TypeUniverse[1]], Typed[R, S -> S -> TypeUniverse[1]], Typed[f, S -> S], Typed[g, S -> S],
					Typed[u, ForAll[{Typed[x, S], Typed[y, S]}, Q[x, f[y]] -> Q[g[x], y]]],
					Typed[v, ForAll[{Typed[x, S], Typed[y, S]}, Q[x, f[y]] -> R[x, y]]],
					Typed[w, ForAll[{Typed[x, S]}, Q[x, f[f[x]]]]]
				},
				ForAll[{Typed[x, S]}, R[g[g[x]], g[x]]]
			]]
		]
	},
	{True, True},
	TestID -> "Dependent-spines-of-exercises-5-10-and-5-11-instantiate-each-codomain"
]

(* f y, where the type of f binds a y of its own: the argument is not captured *)
VerificationTest[
	DefinitionallyEqualQ[
		TypeTheoryType[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[T, A -> B -> TypeUniverse[0]], Typed[f, ForAll[{Typed[x, A], Typed[y, B]}, T[x, y]]], Typed[y, A]} |-> f[y]],
		TypeTheoryTerm[ForAll[
			{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[T, A -> B -> TypeUniverse[0]], Typed[f, ForAll[{Typed[x, A], Typed[y, B]}, T[x, y]]], Typed[y, A]},
			ForAll[{Typed[z, B]}, T[y, z]]
		]]
	],
	True,
	TestID -> "An-argument-is-not-captured-by-a-binder-of-the-same-name"
]

(* simple types, chapter 2: Exercise 2.5 b uses x at two types and has none; Exercise 2.6 has a type once y has one;
   Exercise 2.8, λx y. y (λz. y x), has the type the book derives; and self-application x x has none, as x is applied
   to more arguments than its type takes *)
VerificationTest[
	{
		First[TypeTheoryType[{
			Typed[Z, TypeUniverse[1]], Typed[A, TypeUniverse[1]], Typed[T, TypeUniverse[1]], Typed[G, TypeUniverse[1]],
			Typed[x, (Z -> A) -> (T -> G)], Typed[y, T]
		} |-> x[Typed[z, Z] |-> x, y]]],
		DefinitionallyEqualQ[
			TypeTheoryType[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[y, B]} |-> (Typed[x, (A -> B) -> A] |-> x[Typed[z, A] |-> y])],
			TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[y, B]}, ((A -> B) -> A) -> A]]
		],
		DefinitionallyEqualQ[
			TypeTheoryType[{Typed[B, TypeUniverse[1]], Typed[G, TypeUniverse[1]]} |-> ({Typed[x, G -> B], Typed[y, (G -> B) -> B]} |-> y[Typed[z, G] |-> y[x]])],
			TypeTheoryTerm[ForAll[{Typed[B, TypeUniverse[1]], Typed[G, TypeUniverse[1]]}, (G -> B) -> ((G -> B) -> B) -> B]]
		],
		First[TypeTheoryType[{Typed[A, TypeUniverse[1]], Typed[x, A]} |-> x[x]]]
	},
	{"TypeMismatch", True, True, "ElaborationFailed"},
	TestID -> "Simple-types-of-chapter-2-and-self-application"
]

(* vectors indexed by their length: a literal in an index, 1 + 1 against 2, is equal by computation *)
VerificationTest[
	Head[TypeTheoryType[{
		Typed[Vector, TypeUniverse[1] -> NonNegativeIntegers -> TypeUniverse[1]],
		Typed[empty, ForAll[{Typed[A, TypeUniverse[1]]}, Vector[A, 0]]],
		Typed[cons, ForAll[{Typed[A, TypeUniverse[1]], Typed[n, NonNegativeIntegers]}, A -> Vector[A, n] -> Vector[A, n + 1]]],
		Typed[append, ForAll[{Typed[A, TypeUniverse[1]], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Vector[A, n] -> Vector[A, m] -> Vector[A, n + m]]],
		Typed[B, TypeUniverse[1]], Typed[a, B], Typed[b, B]
	} |-> Typed[append[B, 1, 1, cons[B, 0, a, empty[B]], cons[B, 0, b, empty[B]]], Vector[B, 2]]]],
	TypeTheoryTerm,
	TestID -> "A-vector-index-computes-in-a-dependent-type"
]

(* Church numerals, Exercises 3.12 and 3.13 of the book and section 5.2 of Pierce's Types and Programming Languages: a
   numeral n is ∀A. (A → A) → A → A, n applications of a function. In Prop the numerals have their types by
   impredicativity, but they are proofs of one proposition, all equal by proof irrelevance, so 2 + 3 is 6 as much as 5;
   in Type, where Type 1 holds them, successor, addition and multiplication compute: 2 + 3 is 5 and not 6, 2 × 3 is 6 *)
VerificationTest[
	Module[{numerals, successor, addition, two, three, six},
		numerals = TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[0]]}, (A -> A) -> A -> A]];
		successor = TypeTheoryTerm[{Typed[n, numerals], Typed[A, TypeUniverse[0]], Typed[f, A -> A], Typed[x, A]} |-> f[n[A, f, x]]];
		addition = TypeTheoryTerm[{Typed[m, numerals], Typed[n, numerals], Typed[A, TypeUniverse[0]], Typed[f, A -> A], Typed[x, A]} |-> m[A, f, n[A, f, x]]];
		two = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[f, A -> A], Typed[x, A]} |-> f[f[x]]];
		three = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[f, A -> A], Typed[x, A]} |-> f[f[f[x]]]];
		six = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[f, A -> A], Typed[x, A]} |-> f[f[f[f[f[f[x]]]]]]];
		{
			DefinitionallyEqualQ[TypeTheoryType[numerals], TypeTheoryTerm[TypeUniverse[0]]],
			DefinitionallyEqualQ[TypeTheoryType[successor], TypeTheoryTerm[numerals -> numerals]],
			DefinitionallyEqualQ[TypeTheoryType[addition], TypeTheoryTerm[numerals -> numerals -> numerals]],
			DefinitionallyEqualQ[TypeTheoryTerm[addition[two, three]], six]
		}
	],
	{True, True, True, True},
	TestID -> "Church-numerals-in-Prop-are-one-proof"
]

VerificationTest[
	Module[{numerals, zero, successor, addition, multiplication, two, three, five, six},
		numerals = TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, (A -> A) -> A -> A]];
		zero = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> x];
		successor = TypeTheoryTerm[{Typed[n, numerals], Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> f[n[A, f, x]]];
		addition = TypeTheoryTerm[{Typed[m, numerals], Typed[n, numerals], Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> m[A, f, n[A, f, x]]];
		multiplication = TypeTheoryTerm[{Typed[m, numerals], Typed[n, numerals], Typed[A, TypeUniverse[1]], Typed[f, A -> A]} |-> m[A, n[A, f]]];
		two = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> f[f[x]]];
		three = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> f[f[f[x]]]];
		five = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> f[f[f[f[f[x]]]]]];
		six = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> f[f[f[f[f[f[x]]]]]]];
		{
			DefinitionallyEqualQ[TypeTheoryType[numerals], TypeTheoryTerm[TypeUniverse[2]]],
			DefinitionallyEqualQ[TypeTheoryType[addition], TypeTheoryTerm[numerals -> numerals -> numerals]],
			DefinitionallyEqualQ[TypeTheoryTerm[successor[successor[zero]]], two],
			DefinitionallyEqualQ[TypeTheoryTerm[addition[two, three]], five],
			DefinitionallyEqualQ[TypeTheoryTerm[addition[two, three]], six],
			DefinitionallyEqualQ[TypeTheoryTerm[multiplication[two, three]], six]
		}
	],
	{True, True, True, True, False, True},
	TestID -> "Church-numerals-in-Type-add-and-multiply-by-computation"
]

(* the combinators of chapter 1: K and S have the types of the axioms of implication, and S K K computes to the
   identity, applied to any argument *)
VerificationTest[
	Module[{constant, substitution},
		constant = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[y, B]} |-> x];
		substitution = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[C, TypeUniverse[1]], Typed[x, A -> B -> C], Typed[y, A -> B], Typed[z, A]} |-> x[z, y[z]]];
		{
			DefinitionallyEqualQ[TypeTheoryType[constant], TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]]}, A -> B -> A]]],
			DefinitionallyEqualQ[TypeTheoryType[substitution], TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[C, TypeUniverse[1]]}, (A -> B -> C) -> (A -> B) -> A -> C]]],
			DefinitionallyEqualQ[
				TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]]} |-> substitution[A, B -> A, A, constant[A, B -> A], constant[A, B]]],
				TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[z, A]} |-> z]
			]
		}
	],
	{True, True, True},
	TestID -> "S-K-K-is-the-identity"
]

(* System F, after Girard's Proofs and Types: the polymorphic identity of Prop applies to its own type and to itself,
   which only an impredicative sort allows; a pair over Type is ∀C:Type. (A → B → C) → C, whose first projection gives
   the first element and not the second *)
VerificationTest[
	Module[{identityType, identity, pairs},
		identityType = TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[0]]}, A -> A]];
		identity = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[x, A]} |-> x];
		pairs = TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]]} |-> ForAll[{Typed[C, TypeUniverse[1]]}, (A -> B -> C) -> C]];
		{
			DefinitionallyEqualQ[TypeTheoryType[identity[identityType, identity]], identityType],
			DefinitionallyEqualQ[
				TypeTheoryType[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[a, A], Typed[b, B], Typed[C, TypeUniverse[1]], Typed[k, A -> B -> C]} |-> k[a, b]],
				TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]]}, A -> B -> pairs[A, B]]]
			],
			DefinitionallyEqualQ[
				TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[a, A], Typed[b, A]} |-> ({Typed[C, TypeUniverse[1]], Typed[k, A -> A -> C]} |-> k[a, b])[A, {Typed[x, A], Typed[y, A]} |-> x]],
				TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[a, A], Typed[b, A]} |-> a]
			],
			DefinitionallyEqualQ[
				TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[a, A], Typed[b, A]} |-> ({Typed[C, TypeUniverse[1]], Typed[k, A -> A -> C]} |-> k[a, b])[A, {Typed[x, A], Typed[y, A]} |-> x]],
				TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[a, A], Typed[b, A]} |-> b]
			]
		}
	],
	{True, True, True, False},
	TestID -> "The-polymorphic-identity-applies-to-itself-and-pairs-project"
]

(* a beta-redex is compared with its reduct in one step, however large a literal it holds: the sides are reduced
   without unfolding before their offsets are read, and a product of a variable by a positive literal is no literal at
   once, where reading its value unfolded t 2082 to t 2081 + t once for each unit, past the kernel's recursion limit *)
VerificationTest[
	Map[
		Function[k, With[
			{timed = AbsoluteTiming[DefinitionallyEqualQ[
				TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> (Typed[x, NonNegativeIntegers] |-> x + n^2)[(32 n) k]],
				TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> (32 n) k + n^2]
			]]},
			{Last[timed], First[timed] < 1}
		]],
		{2082, 9223372036854775807}
	],
	{{True, True}, {True, True}},
	TestID -> "A-redex-over-a-product-by-a-large-literal-is-equal-to-its-reduct-at-once"
]

VerificationTest[
	Map[
		Function[k, DefinitionallyEqualQ[
			TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> (Typed[x, NonNegativeIntegers] |-> x + 0)[(32 n) k]],
			TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> (32 n) k + 0]
		]],
		{2082, 9223372036854775807}
	],
	{True, True},
	TestID -> "A-redex-of-a-sum-with-zero-over-a-large-product-is-its-reduct"
]


(* beta reduction takes a projection of a value that is a structure's constructor applied in full as its field at once:
   the reduct is the same by computation, a forged equation of the wrong field is still refused, a partial application
   of the constructor and a value that only reduces to a constructor are left to the projection's own rule, and a
   variable that also occurs whole is replaced by the whole value there *)
VerificationTest[
	With[{prelude = TypeTheoryEnvironment["Prelude"]},
		{
			DefinitionallyEqualQ[TypeTheoryTerm[(Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> p[[1]] + 10 p[[2]])["pair"[1, 2]], prelude], TypeTheoryTerm[21, prelude]],
			DefinitionallyEqualQ[TypeTheoryTerm[(Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> p[[1]])["pair"[1, 2]], prelude], TypeTheoryTerm[2, prelude]],
			FailureQ[TypeTheoryProof[(Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> p[[2]])["pair"[1, 2]] == 1, prelude, {"Reflexivity"}]],
			DefinitionallyEqualQ[TypeTheoryTerm[(Typed[f, NonNegativeIntegers -> CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> f[5][[2]])["pair"[3]], prelude], TypeTheoryTerm[5, prelude]],
			DefinitionallyEqualQ[TypeTheoryTerm[(Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> p[[1]])[(Typed[k, NonNegativeIntegers] |-> "pair"[k, k + 1])[4]], prelude], TypeTheoryTerm[4, prelude]],
			DefinitionallyEqualQ[TypeTheoryTerm[(Typed[p, CartesianProductType[NonNegativeIntegers, NonNegativeIntegers]] |-> "pair"[p[[2]], p])["pair"[1, 2]], prelude], TypeTheoryTerm["pair"[2, "pair"[1, 2]], prelude]]
		}
	],
	{True, False, True, True, True, True},
	TestID -> "Beta-reduction-takes-a-projection-of-a-constructor-as-its-field"
]
