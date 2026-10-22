(* ::Package:: *)

(* Tests for Proofs/Equational.wl: the tactic "FindEquationalProof" replays the proofs that Wolfram's
   FindEquationalProof finds, critical pairs, substitutions and the conclusion, as proofs from the
   equational hypotheses, which the kernel checks again when they are declared. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

(* a group from a left identity and left inverses, the goal and the variables introduced *)
SetAttributes[groupProof, HoldAll]
groupProof[goal_, variables_List] := With[{introduce = TypeTheoryTactic @@ Join[{"Introduce", G, op, e, inv, associativity, identity, inverse}, variables]},
	TypeTheoryProof[
		ForAll[
			{Typed[G, TypeUniverse[1]], Typed[op, TypeSpecifier[{G, G} -> G]], Typed[e, G], Typed[inv, TypeSpecifier[{G} -> G]]},
			Implies[ForAll[{Typed[a, G], Typed[b, G], Typed[c, G]}, op[op[a, b], c] == op[a, op[b, c]]],
				Implies[ForAll[{Typed[a, G]}, op[e, a] == a],
					Implies[ForAll[{Typed[a, G]}, op[inv[a], a] == e], goal]]]
		],
		prelude,
		{introduce, TypeTheoryTactic["FindEquationalProof"]}
	]
]


VerificationTest[
	With[
		{
			rightIdentity = groupProof[ForAll[{Typed[x, G]}, op[x, e] == x], {x}],
			rightInverse = groupProof[ForAll[{Typed[x, G]}, op[x, inv[x]] == e], {x}],
			inverseOfProduct = groupProof[ForAll[{Typed[x, G], Typed[y, G]}, inv[op[x, y]] == op[inv[y], inv[x]]], {x, y}],
			cancellation = groupProof[ForAll[{Typed[x, G], Typed[y, G], Typed[z, G]}, Implies[op[x, y] == op[x, z], y == z]], {x, y, z, h}]
		},
		{
			rightIdentity["Goals"],
			rightInverse["Goals"],
			inverseOfProduct["Goals"],
			cancellation["Goals"],
			MatchQ[
				TypeTheoryCheck[TypeTheoryEnvironment[prelude, {
					TypeTheoryTheorem[GroupRightIdentity, rightIdentity],
					TypeTheoryTheorem[GroupRightInverse, rightInverse],
					TypeTheoryTheorem[GroupInverseOfProduct, inverseOfProduct],
					TypeTheoryTheorem[GroupCancellation, cancellation]
				}]],
				_Success
			]
		}
	],
	{{}, {}, {}, {}, True},
	TestID -> "FindEquationalProof-proves-group-laws-from-the-axioms"
]

VerificationTest[
	With[
		{
			involution = TypeTheoryProof[
				ForAll[{Typed[n, NonNegativeIntegers], Typed[f, TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]]}, Implies[ForAll[{Typed[a, NonNegativeIntegers]}, f[f[a]] == a], f[f[f[f[n]]]] == n]],
				prelude,
				{TypeTheoryTactic["Introduce", n, f, h], TypeTheoryTactic["FindEquationalProof"]}
			]
		},
		{involution["Goals"], MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[FourfoldInvolution, involution]}]], _Success]}
	],
	{{}, True},
	TestID -> "FindEquationalProof-works-in-any-type"
]

VerificationTest[
	First /@ {
		TypeTheoryProof[ForAll[{Typed[G, TypeUniverse[1]], Typed[f, TypeSpecifier[{G} -> G]], Typed[g, TypeSpecifier[{G} -> G]], Typed[x, G]}, f[x] == g[x]], prelude, {
			TypeTheoryTactic["Introduce", G, f, g, x],
			TypeTheoryTactic["FindEquationalProof"]
		}],
		TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n <= n], prelude, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["FindEquationalProof"]}]
	},
	{"NoEquationalHypotheses", "EquationExpected"},
	TestID -> "FindEquationalProof-needs-equational-hypotheses-and-an-equation"
]
