(* ::Package:: *)

(*
Zermelo-Fraenkel set theory with choice, in a model: TypeTheoryEnvironment["ZFC"] is the prelude with the sets of
Aczel's model, built and checked the first time it is asked for. Every axiom of ZFC is a theorem here, proved from the
prelude's axioms (propositional extensionality, the soundness of quotients and choice) and nothing else: no declaration
of this file is an axiom.

A pre-set is a small type of indices with a function from it to pre-sets, a well-founded tree; two pre-sets are
equivalent when every element of each is equivalent to some element of the other, and a set is a class of equivalent
pre-sets:

	"PreSet"                       the inductive type, with "preSet"[α, f] for α : TypeUniverse[1] and f : α -> "PreSet"
	"preSetEquivalent"[x, y]       by recursion on x, then on y; reflexive, symmetric and transitive
	"Set"                          QuotientType["preSetEquivalent"], in TypeUniverse[2], one universe above the indices
	Element[x, y]                  membership, x ∈ y, lifted from "preSetMember"[x, y]: x is equivalent to an element of y

"Set" lives in TypeUniverse[2], not TypeUniverse[1]: a pre-set quantifies over the small types, so it cannot be one.
Every construction is a range, "setRange"[α, F], the set of the values of a function F : α -> "Set" on a small type,
whose members "elementOfRange" gives; it takes a representative of each value by choice. With it:

	"emptySet", "pairSet"[a, b], "unionSet"[a], "powerSet"[a], "separationSet"[a, P]
	"extensionality", "regularity", "elementInduction", "replacement", "infinity"

"replacement" takes the chosen value of a functional relation at each member; "infinity" is set.mm's form, x in a
set where every member is in another member, the range of the iterated singletons of x, "singletonIterate"[x, n]. "choiceAxiom" is set.mm's form of choice: for each
nonempty w in x exactly one u in w shares a member of y with w, y being "choiceSet"[x], the pairs of each nonempty member
with its chosen member; that the choice is unique rests on "elementIrreflexive" and "elementAsymmetric", from regularity.

Classes are predicates on sets, the vocabulary of set.mm, Metamath's database of ZFC:

	"Class"                        "Set" -> Prop
	"setClass"[x]                  the class of the members of x, set.mm's cv
	"classElement"[A, B]           A is a set and a member of B, set.mm's wcel; A == B is set.mm's wceq
	"classAbstraction"[P]          the class {x | P[x]}, set.mm's cab

"classElementFunction" and "setClassEqualFunction" are equalities of functions, (B, z) |-> "classElement"["setClass"[z], B]
equal to (B, z) |-> B[z] and (x, y) |-> "setClass"[x] == "setClass"[y] equal to (x, y) |-> x == y: one substitution with
either carries a statement in set.mm's vocabulary to one about Element and == of sets.

The axioms of set.mm are theorems here under their labels, stated as MetamathLink translates them: a setvar variable is
a bound variable of "Set", a wff or class variable a function of the setvar variables it may depend on, each hypothesis
and the conclusion closed over the setvar variables of the axiom. set.mm's x = y is "setClass"[x] == "setClass"[y] and
x e. y is "classElement"["setClass"[x], "setClass"[y]].

	"ax-mp", "ax-1", "ax-2", "ax-3", "df-bi", "df-an", "df-or"     propositional calculus, the connectives native
	"df-tru", "df-fal", "df-ex", "ax-gen", "ax-4" ... "ax-13"     predicate calculus with equality
	"wsb", "df-clab", "df-cleq", "df-clel"                        substitution, as df-sb defines it, and classes
	"ax-ext", "ax-rep", "ax-sep", "ax-nul", "ax-pow", "ax-pr",     ZFC, each from the model's theorem by
	"ax-un", "ax-reg", "ax-inf", "ax-ac"                          setmmTheorem

setmmTheorem[label, statement, proof] proves a statement in set.mm's vocabulary from a proof of it read about sets: its
"classElement"["setClass"[t], B] as B[t] and its "setClass"[a] == "setClass"[b] as a == b.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[zfcEnvironment]
PackageScoped[$zfcDeclarations]
PackageScoped[$setmmDeclarations]
PackageScoped[setmmTheorem]


(* ::Section:: *)
(*Usage Messages*)


zfcEnvironment::usage = "zfcEnvironment[] gives the prelude with the sets of Aczel's model of ZFC, built and checked the first time it is asked for."
$zfcDeclarations::usage = "$zfcDeclarations is the list of the declarations of Aczel's model of ZFC, in order: definitions and theorems, no axioms."
$setmmDeclarations::usage = "$setmmDeclarations is the list of the axioms of set.mm as theorems of the model, under their labels, in the statements \
MetamathLink translates them to."
setmmTheorem::usage = "setmmTheorem[label, statement, proof] gives the theorem label of statement, in set.mm's vocabulary, from proof, a proof of the \
statement read about sets: \"classElement\"[\"setClass\"[t], B] as B[t] and \"setClass\"[a] == \"setClass\"[b] as a == b."


(* ::Section:: *)
(*Function Definitions*)


TypeTheoryEnvironment["ZFC"] := zfcEnvironment[]

zfcEnvironment[] := zfcEnvironment[] = withoutStoreTracking[
	libraryEnvironment["ZFC", preludeEnvironment[], TypeTheoryEnvironment[preludeEnvironment[], Join[$zfcDeclarations, $setmmDeclarations]]]
]

$zfcDeclarations = {
	(* pre-sets: a small type of indices and a function to pre-sets, their indices, elements, equivalence *)
	TypeTheoryInductiveType[
		"PreSet",
		TypeUniverse[2],
		{"preSet" -> ForAll[{Typed[\[Alpha], TypeUniverse[1]], Typed[elements, TypeSpecifier[{\[Alpha]} -> "PreSet"]]}, "PreSet"]}
	],
	TypeTheoryDefinition[
		"preSetIndex",
		Function[{Typed[x, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[t, "PreSet"]}, TypeUniverse[1]],
				Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]], Typed[r, ForAll[{Typed[i, \[Alpha]]}, TypeUniverse[1]]]}, \[Alpha]],
				x
			]
		]
	],
	TypeTheoryDefinition[
		"preSetElement",
		Function[{Typed[x, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[t, "PreSet"]}, TypeSpecifier[{"preSetIndex"[t]} -> "PreSet"]],
				Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]], Typed[r, ForAll[{Typed[i, \[Alpha]]}, TypeSpecifier[{"preSetIndex"[f[i]]} -> "PreSet"]]]}, f],
				x
			]
		]
	],
	TypeTheoryDefinition[
		"preSetEquivalent",
		Function[{Typed[x, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[t, "PreSet"]}, TypeSpecifier[{"PreSet"} -> TypeUniverse[0]]],
				Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]], Typed[r, ForAll[{Typed[i, \[Alpha]]}, TypeSpecifier[{"PreSet"} -> TypeUniverse[0]]]]},
					Function[{Typed[y, "PreSet"]},
						And[
							ForAll[{Typed[i, \[Alpha]]}, Exists[{Typed[j, "preSetIndex"[y]]}, r[i]["preSetElement"[y][j]]]],
							ForAll[{Typed[j, "preSetIndex"[y]]}, Exists[{Typed[i, \[Alpha]]}, r[i]["preSetElement"[y][j]]]]
						]
					]
				],
				x
			]
		]
	],
	TypeTheoryTheorem[
		"preSetEquivalentReflexive",
		ForAll[{Typed[x, "PreSet"]}, "preSetEquivalent"[x, x]],
		Function[{Typed[x, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[t, "PreSet"]}, "preSetEquivalent"[t, t]],
				Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]], Typed[r, ForAll[{Typed[i, \[Alpha]]}, "preSetEquivalent"[f[i], f[i]]]]},
					"andIntroduction"[
						Function[{Typed[i, \[Alpha]]}, "existsIntroduction"[i, r[i]]],
						Function[{Typed[i, \[Alpha]]}, "existsIntroduction"[i, r[i]]]
					]
				],
				x
			]
		]
	],
	TypeTheoryTheorem[
		"preSetEquivalentSymmetric",
		ForAll[{Typed[x, "PreSet"], Typed[y, "PreSet"]}, Implies["preSetEquivalent"[x, y], "preSetEquivalent"[y, x]]],
		Function[{Typed[x, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[t, "PreSet"]}, ForAll[{Typed[y, "PreSet"]}, Implies["preSetEquivalent"[t, y], "preSetEquivalent"[y, t]]]],
				Function[
					{
						Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]],
						Typed[r, ForAll[{Typed[i, \[Alpha]], Typed[y, "PreSet"]}, Implies["preSetEquivalent"[f[i], y], "preSetEquivalent"[y, f[i]]]]]
					},
					Function[{Typed[y, "PreSet"]},
						InductiveRecursor["PreSet"][
							Function[{Typed[s, "PreSet"]}, Implies["preSetEquivalent"["preSet"[\[Alpha], f], s], "preSetEquivalent"[s, "preSet"[\[Alpha], f]]]],
							Function[
								{
									Typed[\[Beta], TypeUniverse[1]], Typed[g, TypeSpecifier[{\[Beta]} -> "PreSet"]],
									Typed[q, ForAll[{Typed[j, \[Beta]]}, Implies["preSetEquivalent"["preSet"[\[Alpha], f], g[j]], "preSetEquivalent"[g[j], "preSet"[\[Alpha], f]]]]],
									Typed[h, "preSetEquivalent"["preSet"[\[Alpha], f], "preSet"[\[Beta], g]]]
								},
								"andIntroduction"[
									Function[{Typed[j, \[Beta]]},
										InductiveRecursor[Exists][
											Function[{Typed[e, Exists[{Typed[i, \[Alpha]]}, "preSetEquivalent"[f[i], g[j]]]]}, Exists[{Typed[i, \[Alpha]]}, "preSetEquivalent"[g[j], f[i]]]],
											Function[{Typed[i, \[Alpha]], Typed[k, "preSetEquivalent"[f[i], g[j]]]}, "existsIntroduction"[i, r[i, g[j], k]]],
											h[[2]][j]
										]
									],
									Function[{Typed[i, \[Alpha]]},
										InductiveRecursor[Exists][
											Function[{Typed[e, Exists[{Typed[j, \[Beta]]}, "preSetEquivalent"[f[i], g[j]]]]}, Exists[{Typed[j, \[Beta]]}, "preSetEquivalent"[g[j], f[i]]]],
											Function[{Typed[j, \[Beta]], Typed[k, "preSetEquivalent"[f[i], g[j]]]}, "existsIntroduction"[j, r[i, g[j], k]]],
											h[[1]][i]
										]
									]
								]
							],
							y
						]
					]
				],
				x
			]
		]
	],

	(* transitivity, the sets as classes of pre-sets, membership of pre-sets *)
	TypeTheoryDefinition[
		"existsElimination",
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], TypedImplicit[c, TypeUniverse[0]],
				Typed[h, Exists[P]], Typed[k, ForAll[{Typed[w, \[Alpha]]}, Implies[P[w], c]]]
			},
			InductiveRecursor[Exists][Function[{Typed[t, Exists[P]]}, c], k, h]
		]
	],
	TypeTheoryTheorem[
		"preSetEquivalentTransitive",
		ForAll[{Typed[x, "PreSet"], Typed[y, "PreSet"], Typed[z, "PreSet"]}, Implies["preSetEquivalent"[x, y], Implies["preSetEquivalent"[y, z], "preSetEquivalent"[x, z]]]],
		Function[{Typed[x, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[t, "PreSet"]}, ForAll[{Typed[y, "PreSet"], Typed[z, "PreSet"]}, Implies["preSetEquivalent"[t, y], Implies["preSetEquivalent"[y, z], "preSetEquivalent"[t, z]]]]],
				Function[
					{
						Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]],
						Typed[r, ForAll[{Typed[i, \[Alpha]], Typed[y, "PreSet"], Typed[z, "PreSet"]}, Implies["preSetEquivalent"[f[i], y], Implies["preSetEquivalent"[y, z], "preSetEquivalent"[f[i], z]]]]]
					},
					Function[{Typed[y, "PreSet"]},
						InductiveRecursor["PreSet"][
							Function[{Typed[s, "PreSet"]}, ForAll[{Typed[z, "PreSet"]}, Implies["preSetEquivalent"["preSet"[\[Alpha], f], s], Implies["preSetEquivalent"[s, z], "preSetEquivalent"["preSet"[\[Alpha], f], z]]]]],
							Function[
								{
									Typed[\[Beta], TypeUniverse[1]], Typed[g, TypeSpecifier[{\[Beta]} -> "PreSet"]],
									Typed[q, ForAll[{Typed[j, \[Beta]], Typed[z, "PreSet"]}, Implies["preSetEquivalent"["preSet"[\[Alpha], f], g[j]], Implies["preSetEquivalent"[g[j], z], "preSetEquivalent"["preSet"[\[Alpha], f], z]]]]]
								},
								Function[{Typed[z, "PreSet"]},
									InductiveRecursor["PreSet"][
										Function[{Typed[s, "PreSet"]}, Implies["preSetEquivalent"["preSet"[\[Alpha], f], "preSet"[\[Beta], g]], Implies["preSetEquivalent"["preSet"[\[Beta], g], s], "preSetEquivalent"["preSet"[\[Alpha], f], s]]]],
										Function[
											{
												Typed[\[Gamma], TypeUniverse[1]], Typed[k, TypeSpecifier[{\[Gamma]} -> "PreSet"]],
												Typed[o, ForAll[{Typed[l, \[Gamma]]}, Implies["preSetEquivalent"["preSet"[\[Alpha], f], "preSet"[\[Beta], g]], Implies["preSetEquivalent"["preSet"[\[Beta], g], k[l]], "preSetEquivalent"["preSet"[\[Alpha], f], k[l]]]]]],
												Typed[h, "preSetEquivalent"["preSet"[\[Alpha], f], "preSet"[\[Beta], g]]],
												Typed[hh, "preSetEquivalent"["preSet"[\[Beta], g], "preSet"[\[Gamma], k]]]
											},
											"andIntroduction"[
												Function[{Typed[i, \[Alpha]]},
													"existsElimination"[h[[1]][i], Function[{Typed[j, \[Beta]], Typed[e, "preSetEquivalent"[f[i], g[j]]]},
														"existsElimination"[hh[[1]][j], Function[{Typed[l, \[Gamma]], Typed[ee, "preSetEquivalent"[g[j], k[l]]]},
															Typed["existsIntroduction"[l, r[i, g[j], k[l], e, ee]], Exists[{Typed[m, \[Gamma]]}, "preSetEquivalent"[f[i], k[m]]]]
														]]
													]]
												],
												Function[{Typed[l, \[Gamma]]},
													"existsElimination"[hh[[2]][l], Function[{Typed[j, \[Beta]], Typed[ee, "preSetEquivalent"[g[j], k[l]]]},
														"existsElimination"[h[[2]][j], Function[{Typed[i, \[Alpha]], Typed[e, "preSetEquivalent"[f[i], g[j]]]},
															Typed["existsIntroduction"[i, r[i, g[j], k[l], e, ee]], Exists[{Typed[m, \[Alpha]]}, "preSetEquivalent"[f[m], k[l]]]]
														]]
													]]
												]
											]
										],
										z
									]
								]
							],
							y
						]
					]
				],
				x
			]
		]
	],
	TypeTheoryDefinition["Set", Typed[QuotientType["preSetEquivalent"], TypeUniverse[2]]],
	TypeTheoryDefinition["setOfPreSet", Typed[Function[{Typed[x, "PreSet"]}, QuotientIntroduction["preSetEquivalent", x]], TypeSpecifier[{"PreSet"} -> "Set"]]],
	(* x is a member of y when it is equivalent to one of the elements of y *)
	TypeTheoryDefinition[
		"preSetMember",
		Function[{Typed[x, "PreSet"], Typed[y, "PreSet"]}, Exists[{Typed[j, "preSetIndex"[y]]}, "preSetEquivalent"[x, "preSetElement"[y][j]]]]
	],
	TypeTheoryTheorem[
		"preSetMemberRespectsLeft",
		ForAll[{Typed[x, "PreSet"], Typed[xx, "PreSet"], Typed[y, "PreSet"]}, Implies["preSetEquivalent"[x, xx], Implies["preSetMember"[x, y], "preSetMember"[xx, y]]]],
		Function[{Typed[x, "PreSet"], Typed[xx, "PreSet"], Typed[y, "PreSet"], Typed[h, "preSetEquivalent"[x, xx]], Typed[m, "preSetMember"[x, y]]},
			"existsElimination"[m, Function[{Typed[j, "preSetIndex"[y]], Typed[e, "preSetEquivalent"[x, "preSetElement"[y][j]]]},
				Typed[
					"existsIntroduction"[j, "preSetEquivalentTransitive"[xx, x, "preSetElement"[y][j], "preSetEquivalentSymmetric"[x, xx, h], e]],
					"preSetMember"[xx, y]
				]
			]]
		]
	],
	TypeTheoryTheorem[
		"preSetMemberRespectsRight",
		ForAll[{Typed[x, "PreSet"], Typed[y, "PreSet"], Typed[yy, "PreSet"]}, Implies["preSetEquivalent"[y, yy], Implies["preSetMember"[x, y], "preSetMember"[x, yy]]]],
		Function[{Typed[x, "PreSet"], Typed[y, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[s, "PreSet"]}, ForAll[{Typed[yy, "PreSet"]}, Implies["preSetEquivalent"[s, yy], Implies["preSetMember"[x, s], "preSetMember"[x, yy]]]]],
				Function[
					{
						Typed[\[Beta], TypeUniverse[1]], Typed[g, TypeSpecifier[{\[Beta]} -> "PreSet"]],
						Typed[q, ForAll[{Typed[j, \[Beta]], Typed[yy, "PreSet"]}, Implies["preSetEquivalent"[g[j], yy], Implies["preSetMember"[x, g[j]], "preSetMember"[x, yy]]]]],
						Typed[yy, "PreSet"]
					},
					InductiveRecursor["PreSet"][
						Function[{Typed[s, "PreSet"]}, Implies["preSetEquivalent"["preSet"[\[Beta], g], s], Implies["preSetMember"[x, "preSet"[\[Beta], g]], "preSetMember"[x, s]]]],
						Function[
							{
								Typed[\[Gamma], TypeUniverse[1]], Typed[k, TypeSpecifier[{\[Gamma]} -> "PreSet"]],
								Typed[o, ForAll[{Typed[l, \[Gamma]]}, Implies["preSetEquivalent"["preSet"[\[Beta], g], k[l]], Implies["preSetMember"[x, "preSet"[\[Beta], g]], "preSetMember"[x, k[l]]]]]],
								Typed[h, "preSetEquivalent"["preSet"[\[Beta], g], "preSet"[\[Gamma], k]]],
								Typed[m, "preSetMember"[x, "preSet"[\[Beta], g]]]
							},
							"existsElimination"[m, Function[{Typed[j, \[Beta]], Typed[e, "preSetEquivalent"[x, g[j]]]},
								"existsElimination"[h[[1]][j], Function[{Typed[l, \[Gamma]], Typed[ee, "preSetEquivalent"[g[j], k[l]]]},
									Typed["existsIntroduction"[l, "preSetEquivalentTransitive"[x, g[j], k[l], e, ee]], "preSetMember"[x, "preSet"[\[Gamma], k]]]
								]]
							]]
						],
						yy
					]
				],
				y
			]
		]
	],

	(* membership of sets, extensionality *)
	TypeTheoryTheorem[
		"preSetMemberRespects",
		ForAll[{Typed[x, "PreSet"], Typed[y, "PreSet"], Typed[yy, "PreSet"]}, Implies["preSetEquivalent"[y, yy], "preSetMember"[x, y] == "preSetMember"[x, yy]]],
		Function[{Typed[x, "PreSet"], Typed[y, "PreSet"], Typed[yy, "PreSet"], Typed[h, "preSetEquivalent"[y, yy]]},
			"propositionalExtensionality"["equivalentIntroduction"[
				"preSetMemberRespectsRight"[x, y, yy, h],
				"preSetMemberRespectsRight"[x, yy, y, "preSetEquivalentSymmetric"[y, yy, h]]
			]]
		]
	],
	(* x a member of the set b *)
	TypeTheoryDefinition[
		"preSetMemberOfSet",
		Function[{Typed[x, "PreSet"], Typed[b, "Set"]},
			QuotientLift[Function[{Typed[y, "PreSet"]}, "preSetMember"[x, y]], Function[{Typed[y, "PreSet"], Typed[yy, "PreSet"]}, "preSetMemberRespects"[x, y, yy]], b]
		]
	],
	TypeTheoryTheorem[
		"preSetMemberOfSetRespects",
		ForAll[{Typed[b, "Set"], Typed[x, "PreSet"], Typed[xx, "PreSet"]}, Implies["preSetEquivalent"[x, xx], "preSetMemberOfSet"[x, b] == "preSetMemberOfSet"[xx, b]]],
		Function[{Typed[b, "Set"], Typed[x, "PreSet"], Typed[xx, "PreSet"], Typed[h, "preSetEquivalent"[x, xx]]},
			Construct[
				QuotientInduction,
				"PreSet",
				"preSetEquivalent",
				Function[{Typed[c, "Set"]}, "preSetMemberOfSet"[x, c] == "preSetMemberOfSet"[xx, c]],
				Function[{Typed[y, "PreSet"]},
					"propositionalExtensionality"["equivalentIntroduction"[
						"preSetMemberRespectsLeft"[x, xx, y, h],
						"preSetMemberRespectsLeft"[xx, x, y, "preSetEquivalentSymmetric"[x, xx, h]]
					]]
				],
				b
			]
		]
	],
	TypeTheoryDefinition[
		Element,
		Typed[
			Function[{Typed[a, "Set"], Typed[b, "Set"]},
				QuotientLift[Function[{Typed[x, "PreSet"]}, "preSetMemberOfSet"[x, b]], "preSetMemberOfSetRespects"[b], a]
			],
			TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]
		]
	],
	(* extensionality of pre-sets: the same members make equivalent pre-sets *)
	TypeTheoryTheorem[
		"preSetExtensionality",
		ForAll[{Typed[x, "PreSet"], Typed[y, "PreSet"]}, Implies[ForAll[{Typed[z, "PreSet"]}, Equivalent["preSetMember"[z, x], "preSetMember"[z, y]]], "preSetEquivalent"[x, y]]],
		Function[{Typed[x, "PreSet"]},
			InductiveRecursor["PreSet"][
				Function[{Typed[s, "PreSet"]}, ForAll[{Typed[y, "PreSet"]}, Implies[ForAll[{Typed[z, "PreSet"]}, Equivalent["preSetMember"[z, s], "preSetMember"[z, y]]], "preSetEquivalent"[s, y]]]],
				Function[
					{
						Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]],
						Typed[r, ForAll[{Typed[i, \[Alpha]], Typed[y, "PreSet"]}, Implies[ForAll[{Typed[z, "PreSet"]}, Equivalent["preSetMember"[z, f[i]], "preSetMember"[z, y]]], "preSetEquivalent"[f[i], y]]]],
						Typed[y, "PreSet"]
					},
					InductiveRecursor["PreSet"][
						Function[{Typed[s, "PreSet"]}, Implies[ForAll[{Typed[z, "PreSet"]}, Equivalent["preSetMember"[z, "preSet"[\[Alpha], f]], "preSetMember"[z, s]]], "preSetEquivalent"["preSet"[\[Alpha], f], s]]],
						Function[
							{
								Typed[\[Beta], TypeUniverse[1]], Typed[g, TypeSpecifier[{\[Beta]} -> "PreSet"]],
								Typed[q, ForAll[{Typed[j, \[Beta]]}, Implies[ForAll[{Typed[z, "PreSet"]}, Equivalent["preSetMember"[z, "preSet"[\[Alpha], f]], "preSetMember"[z, g[j]]]], "preSetEquivalent"["preSet"[\[Alpha], f], g[j]]]]],
								Typed[h, ForAll[{Typed[z, "PreSet"]}, Equivalent["preSetMember"[z, "preSet"[\[Alpha], f]], "preSetMember"[z, "preSet"[\[Beta], g]]]]]
							},
							"andIntroduction"[
								Function[{Typed[i, \[Alpha]]},
									h[f[i]][[1]][Typed["existsIntroduction"[i, "preSetEquivalentReflexive"[f[i]]], "preSetMember"[f[i], "preSet"[\[Alpha], f]]]]
								],
								Function[{Typed[j, \[Beta]]},
									"existsElimination"[
										h[g[j]][[2]][Typed["existsIntroduction"[j, "preSetEquivalentReflexive"[g[j]]], "preSetMember"[g[j], "preSet"[\[Beta], g]]]],
										Function[{Typed[i, \[Alpha]], Typed[e, "preSetEquivalent"[g[j], f[i]]]},
											Typed["existsIntroduction"[i, "preSetEquivalentSymmetric"[g[j], f[i], e]], Exists[{Typed[k, \[Alpha]]}, "preSetEquivalent"[f[k], g[j]]]]
										]
									]
								]
							]
						],
						y
					]
				],
				x
			]
		]
	],
	TypeTheoryTheorem[
		"extensionality",
		ForAll[{Typed[a, "Set"], Typed[b, "Set"]}, Implies[ForAll[{Typed[z, "Set"]}, Equivalent[Element[z, a], Element[z, b]]], a == b]],
		Function[{Typed[a, "Set"]},
			Construct[
				QuotientInduction,
				"PreSet",
				"preSetEquivalent",
				Function[{Typed[c, "Set"]}, ForAll[{Typed[b, "Set"]}, Implies[ForAll[{Typed[z, "Set"]}, Equivalent[Element[z, c], Element[z, b]]], c == b]]],
				Function[{Typed[x, "PreSet"], Typed[b, "Set"]},
					Construct[
						QuotientInduction,
						"PreSet",
						"preSetEquivalent",
						Function[{Typed[c, "Set"]}, Implies[ForAll[{Typed[z, "Set"]}, Equivalent[Element[z, "setOfPreSet"[x]], Element[z, c]]], "setOfPreSet"[x] == c]],
						Function[{Typed[y, "PreSet"], Typed[h, ForAll[{Typed[z, "Set"]}, Equivalent[Element[z, "setOfPreSet"[x]], Element[z, "setOfPreSet"[y]]]]]},
							"quotientSoundness"["preSetExtensionality"[x, y, Function[{Typed[z, "PreSet"]}, h["setOfPreSet"[z]]]]]
						],
						b
					]
				],
				a
			]
		]
	],

	(* exactness, representatives, the range of a function on a small type *)
	TypeTheoryTheorem[
		"preSetEquivalentRespects",
		ForAll[{Typed[x, "PreSet"], Typed[w, "PreSet"], Typed[ww, "PreSet"]}, Implies["preSetEquivalent"[w, ww], "preSetEquivalent"[x, w] == "preSetEquivalent"[x, ww]]],
		Function[{Typed[x, "PreSet"], Typed[w, "PreSet"], Typed[ww, "PreSet"], Typed[h, "preSetEquivalent"[w, ww]]},
			"propositionalExtensionality"["equivalentIntroduction"[
				Function[{Typed[e, "preSetEquivalent"[x, w]]}, "preSetEquivalentTransitive"[x, w, ww, e, h]],
				Function[{Typed[e, "preSetEquivalent"[x, ww]]}, "preSetEquivalentTransitive"[x, ww, w, e, "preSetEquivalentSymmetric"[w, ww, h]]]
			]]
		]
	],
	(* equal classes come from equivalent pre-sets *)
	TypeTheoryTheorem[
		"preSetExact",
		ForAll[{Typed[x, "PreSet"], Typed[y, "PreSet"]}, Implies["setOfPreSet"[x] == "setOfPreSet"[y], "preSetEquivalent"[x, y]]],
		Function[{Typed[x, "PreSet"], Typed[y, "PreSet"], Typed[h, "setOfPreSet"[x] == "setOfPreSet"[y]]},
			Construct[
				"equalitySubstitution",
				"Set",
				Function[{Typed[c, "Set"]}, QuotientLift[Function[{Typed[w, "PreSet"]}, "preSetEquivalent"[x, w]], "preSetEquivalentRespects"[x], c]],
				"setOfPreSet"[x],
				"setOfPreSet"[y],
				h,
				"preSetEquivalentReflexive"[x]
			]
		]
	],
	TypeTheoryTheorem[
		"setRepresentativeExists",
		ForAll[{Typed[a, "Set"]}, Exists[{Typed[x, "PreSet"]}, "setOfPreSet"[x] == a]],
		Function[{Typed[a, "Set"]},
			Construct[
				QuotientInduction,
				"PreSet",
				"preSetEquivalent",
				Function[{Typed[c, "Set"]}, Exists[{Typed[x, "PreSet"]}, "setOfPreSet"[x] == c]],
				Function[{Typed[y, "PreSet"]}, Typed["existsIntroduction"[y, "equalityReflexivity"["setOfPreSet"[y]]], Exists[{Typed[x, "PreSet"]}, "setOfPreSet"[x] == "setOfPreSet"[y]]]],
				a
			]
		]
	],
	TypeTheoryDefinition["setRepresentative", Typed[Function[{Typed[a, "Set"]}, ChosenWitness["setRepresentativeExists"[a]]], TypeSpecifier[{"Set"} -> "PreSet"]]],
	TypeTheoryTheorem[
		"setRepresentativeProperty",
		ForAll[{Typed[a, "Set"]}, "setOfPreSet"["setRepresentative"[a]] == a],
		Function[{Typed[a, "Set"]}, "chosenWitnessProperty"["setRepresentativeExists"[a]]]
	],
	(* the members of the class of a pre-set are the classes of its elements *)
	TypeTheoryTheorem[
		"elementOfSetOfPreSet",
		ForAll[{Typed[x, "PreSet"], Typed[c, "Set"]}, Equivalent[Element[c, "setOfPreSet"[x]], Exists[{Typed[j, "preSetIndex"[x]]}, c == "setOfPreSet"["preSetElement"[x][j]]]]],
		Function[{Typed[x, "PreSet"], Typed[c, "Set"]},
			Construct[
				QuotientInduction,
				"PreSet",
				"preSetEquivalent",
				Function[{Typed[d, "Set"]}, Equivalent[Element[d, "setOfPreSet"[x]], Exists[{Typed[j, "preSetIndex"[x]]}, d == "setOfPreSet"["preSetElement"[x][j]]]]],
				Function[{Typed[z, "PreSet"]},
					"equivalentIntroduction"[
						Function[{Typed[m, "preSetMember"[z, x]]},
							"existsElimination"[m, Function[{Typed[j, "preSetIndex"[x]], Typed[e, "preSetEquivalent"[z, "preSetElement"[x][j]]]},
								Typed["existsIntroduction"[j, "quotientSoundness"[e]], Exists[{Typed[k, "preSetIndex"[x]]}, "setOfPreSet"[z] == "setOfPreSet"["preSetElement"[x][k]]]]
							]]
						],
						Function[{Typed[m, Exists[{Typed[k, "preSetIndex"[x]]}, "setOfPreSet"[z] == "setOfPreSet"["preSetElement"[x][k]]]]},
							"existsElimination"[m, Function[{Typed[j, "preSetIndex"[x]], Typed[e, "setOfPreSet"[z] == "setOfPreSet"["preSetElement"[x][j]]]},
								Typed["existsIntroduction"[j, "preSetExact"[z, "preSetElement"[x][j], e]], "preSetMember"[z, x]]
							]]
						]
					]
				],
				c
			]
		]
	],
	(* the set of the values of a function on a small type *)
	TypeTheoryDefinition[
		"setRange",
		Typed[
			Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[F, TypeSpecifier[{\[Alpha]} -> "Set"]]}, "setOfPreSet"["preSet"[\[Alpha], Function[{Typed[i, \[Alpha]]}, "setRepresentative"[F[i]]]]]],
			ForAll[{Typed[\[Alpha], TypeUniverse[1]]}, TypeSpecifier[{TypeSpecifier[{\[Alpha]} -> "Set"]} -> "Set"]]
		]
	],
	TypeTheoryTheorem[
		"elementOfRange",
		ForAll[{Typed[\[Alpha], TypeUniverse[1]], Typed[F, TypeSpecifier[{\[Alpha]} -> "Set"]], Typed[c, "Set"]}, Equivalent[Element[c, "setRange"[\[Alpha], F]], Exists[{Typed[j, \[Alpha]]}, c == F[j]]]],
		Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[F, TypeSpecifier[{\[Alpha]} -> "Set"]], Typed[c, "Set"]},
			With[{membership = "elementOfSetOfPreSet"["preSet"[\[Alpha], Function[{Typed[i, \[Alpha]]}, "setRepresentative"[F[i]]]], c]},
				"equivalentIntroduction"[
					Function[{Typed[m, Element[c, "setRange"[\[Alpha], F]]]},
						"existsElimination"[membership[[1]][m], Function[{Typed[j, \[Alpha]], Typed[e, c == "setOfPreSet"["setRepresentative"[F[j]]]]},
							Typed["existsIntroduction"[j, "equalityTransitivity"[e, "setRepresentativeProperty"[F[j]]]], Exists[{Typed[k, \[Alpha]]}, c == F[k]]]
						]]
					],
					Function[{Typed[m, Exists[{Typed[k, \[Alpha]]}, c == F[k]]]},
						membership[[2]]["existsElimination"[m, Function[{Typed[j, \[Alpha]], Typed[e, c == F[j]]},
							Typed[
								"existsIntroduction"[j, "equalityTransitivity"[e, "equalitySymmetry"["setRepresentativeProperty"[F[j]]]]],
								Exists[{Typed[k, \[Alpha]]}, c == "setOfPreSet"["setRepresentative"[F[k]]]]
							]
						]]]
					]
				]
			]
		]
	],
	(* the elements of a set by its representative *)
	TypeTheoryDefinition["setIndex", Typed[Function[{Typed[a, "Set"]}, "preSetIndex"["setRepresentative"[a]]], TypeSpecifier[{"Set"} -> TypeUniverse[1]]]],
	TypeTheoryDefinition[
		"setElement",
		Typed[Function[{Typed[a, "Set"], Typed[i, "setIndex"[a]]}, "setOfPreSet"["preSetElement"["setRepresentative"[a]][i]]], ForAll[{Typed[a, "Set"]}, TypeSpecifier[{"setIndex"[a]} -> "Set"]]]
	],
	TypeTheoryTheorem[
		"elementOfSet",
		ForAll[{Typed[a, "Set"], Typed[c, "Set"]}, Equivalent[Element[c, a], Exists[{Typed[j, "setIndex"[a]]}, c == "setElement"[a, j]]]],
		Function[{Typed[a, "Set"], Typed[c, "Set"]},
			Construct[
				"equalitySubstitution",
				"Set",
				Function[{Typed[s, "Set"]}, Equivalent[Element[c, s], Exists[{Typed[j, "setIndex"[a]]}, c == "setElement"[a, j]]]],
				"setOfPreSet"["setRepresentative"[a]],
				a,
				"setRepresentativeProperty"[a],
				"elementOfSetOfPreSet"["setRepresentative"[a], c]
			]
		]
	],

	(* the empty set, pairs, unions *)
	TypeTheoryDefinition[
		"emptySet",
		Typed[
			"setRange"[Subtype[Function[{Typed[t, Booleans]}, False]], Function[{Typed[s, Subtype[Function[{Typed[t, Booleans]}, False]]]}, InductiveRecursor[False][Function[{Typed[e, False]}, "Set"], s[[2]]]]],
			"Set"
		]
	],
	TypeTheoryTheorem[
		"emptySetEmpty",
		ForAll[{Typed[c, "Set"]}, Not[Element[c, "emptySet"]]],
		Function[{Typed[c, "Set"], Typed[m, Element[c, "emptySet"]]},
			"existsElimination"[
				"elementOfRange"[
					Subtype[Function[{Typed[t, Booleans]}, False]],
					Function[{Typed[s, Subtype[Function[{Typed[t, Booleans]}, False]]]}, InductiveRecursor[False][Function[{Typed[e, False]}, "Set"], s[[2]]]],
					c
				][[1]][m],
				Function[{Typed[s, Subtype[Function[{Typed[t, Booleans]}, False]]], Typed[e, c == InductiveRecursor[False][Function[{Typed[f, False]}, "Set"], s[[2]]]]}, s[[2]]]
			]
		]
	],
	TypeTheoryDefinition[
		"pairSet",
		Typed[
			Function[{Typed[a, "Set"], Typed[b, "Set"]}, "setRange"[Booleans, Function[{Typed[t, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[r, Booleans]}, "Set"], a, b, t]]]],
			TypeSpecifier[{"Set", "Set"} -> "Set"]
		]
	],
	TypeTheoryTheorem[
		"elementOfPair",
		ForAll[{Typed[a, "Set"], Typed[b, "Set"], Typed[c, "Set"]}, Equivalent[Element[c, "pairSet"[a, b]], Or[c == a, c == b]]],
		Function[{Typed[a, "Set"], Typed[b, "Set"], Typed[c, "Set"]},
			With[{range = "elementOfRange"[Booleans, Function[{Typed[t, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[r, Booleans]}, "Set"], a, b, t]], c]},
				"equivalentIntroduction"[
					Function[{Typed[m, Element[c, "pairSet"[a, b]]]},
						"existsElimination"[range[[1]][m], Function[{Typed[t, Booleans]},
							InductiveRecursor[Booleans][
								Function[{Typed[r, Booleans]}, Implies[c == InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "Set"], a, b, r], Or[c == a, c == b]]],
								Function[{Typed[e, c == a]}, "orIntroductionLeft"[e]],
								Function[{Typed[e, c == b]}, "orIntroductionRight"[e]],
								t
							]
						]]
					],
					Function[{Typed[o, Or[c == a, c == b]]},
						range[[2]][InductiveRecursor[Or][
							Function[{Typed[p, Or[c == a, c == b]]}, Exists[{Typed[t, Booleans]}, c == InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "Set"], a, b, t]]],
							Function[{Typed[e, c == a]}, "existsIntroduction"["false", e]],
							Function[{Typed[e, c == b]}, "existsIntroduction"["true", e]],
							o
						]]
					]
				]
			]
		]
	],
	TypeTheoryInductiveType[
		"DependentPair",
		ForAll[{Typed[\[Alpha], TypeUniverse[1]], Typed[\[Beta], TypeSpecifier[{\[Alpha]} -> TypeUniverse[1]]]}, TypeUniverse[1]],
		{
			"dependentPair" -> ForAll[
				{TypedImplicit[\[Alpha], TypeUniverse[1]], TypedImplicit[\[Beta], TypeSpecifier[{\[Alpha]} -> TypeUniverse[1]]], Typed[first, \[Alpha]], Typed[second, \[Beta][first]]},
				"DependentPair"[\[Alpha], \[Beta]]
			]
		}
	],
	TypeTheoryDefinition[
		"unionSet",
		Typed[
			Function[{Typed[a, "Set"]},
				"setRange"[
					"DependentPair"["setIndex"[a], Function[{Typed[i, "setIndex"[a]]}, "setIndex"["setElement"[a, i]]]],
					Function[{Typed[p, "DependentPair"["setIndex"[a], Function[{Typed[i, "setIndex"[a]]}, "setIndex"["setElement"[a, i]]]]]}, "setElement"["setElement"[a, p[[1]]], p[[2]]]]
				]
			],
			TypeSpecifier[{"Set"} -> "Set"]
		]
	],
	TypeTheoryTheorem[
		"elementOfUnion",
		ForAll[{Typed[a, "Set"], Typed[c, "Set"]}, Equivalent[Element[c, "unionSet"[a]], Exists[{Typed[y, "Set"]}, And[Element[y, a], Element[c, y]]]]],
		Function[{Typed[a, "Set"], Typed[c, "Set"]},
			With[
				{
					range = "elementOfRange"[
						"DependentPair"["setIndex"[a], Function[{Typed[i, "setIndex"[a]]}, "setIndex"["setElement"[a, i]]]],
						Function[{Typed[p, "DependentPair"["setIndex"[a], Function[{Typed[i, "setIndex"[a]]}, "setIndex"["setElement"[a, i]]]]]}, "setElement"["setElement"[a, p[[1]]], p[[2]]]],
						c
					]
				},
				"equivalentIntroduction"[
					Function[{Typed[m, Element[c, "unionSet"[a]]]},
						"existsElimination"[range[[1]][m], Function[
							{
								Typed[p, "DependentPair"["setIndex"[a], Function[{Typed[i, "setIndex"[a]]}, "setIndex"["setElement"[a, i]]]]],
								Typed[e, c == "setElement"["setElement"[a, p[[1]]], p[[2]]]]
							},
							Typed[
								"existsIntroduction"[
									"setElement"[a, p[[1]]],
									"andIntroduction"[
										"elementOfSet"[a, "setElement"[a, p[[1]]]][[2]][Typed["existsIntroduction"[p[[1]], "equalityReflexivity"["setElement"[a, p[[1]]]]], Exists[{Typed[j, "setIndex"[a]]}, "setElement"[a, p[[1]]] == "setElement"[a, j]]]],
										"elementOfSet"["setElement"[a, p[[1]]], c][[2]][Typed["existsIntroduction"[p[[2]], e], Exists[{Typed[j, "setIndex"["setElement"[a, p[[1]]]]]}, c == "setElement"["setElement"[a, p[[1]]], j]]]]
									]
								],
								Exists[{Typed[y, "Set"]}, And[Element[y, a], Element[c, y]]]
							]
						]]
					],
					Function[{Typed[m, Exists[{Typed[y, "Set"]}, And[Element[y, a], Element[c, y]]]]},
						"existsElimination"[m, Function[{Typed[y, "Set"], Typed[k, And[Element[y, a], Element[c, y]]]},
							"existsElimination"["elementOfSet"[a, y][[1]][k[[1]]], Function[{Typed[i, "setIndex"[a]], Typed[e, y == "setElement"[a, i]]},
								"existsElimination"[
									"elementOfSet"["setElement"[a, i], c][[1]][Construct["equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, Element[c, s]], y, "setElement"[a, i], e, k[[2]]]],
									Function[{Typed[j, "setIndex"["setElement"[a, i]]], Typed[ee, c == "setElement"["setElement"[a, i], j]]},
										range[[2]][Typed[
											"existsIntroduction"[
												"dependentPair"[i, j],
												ee
											],
											Exists[
												{Typed[p, "DependentPair"["setIndex"[a], Function[{Typed[l, "setIndex"[a]]}, "setIndex"["setElement"[a, l]]]]]},
												c == "setElement"["setElement"[a, p[[1]]], p[[2]]]
											]
										]]
									]
								]
							]]
						]]
					]
				]
			]
		]
	],

	(* separation, power sets, induction on membership *)
	TypeTheoryDefinition[
		"separationSet",
		Typed[
			Function[{Typed[a, "Set"], Typed[P, TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
				"setRange"[
					Subtype[Function[{Typed[i, "setIndex"[a]]}, P["setElement"[a, i]]]],
					Function[{Typed[s, Subtype[Function[{Typed[i, "setIndex"[a]]}, P["setElement"[a, i]]]]]}, "setElement"[a, s[[1]]]]
				]
			],
			TypeSpecifier[{"Set", TypeSpecifier[{"Set"} -> TypeUniverse[0]]} -> "Set"]
		]
	],
	TypeTheoryTheorem[
		"elementOfSeparation",
		ForAll[{Typed[a, "Set"], Typed[P, TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[c, "Set"]}, Equivalent[Element[c, "separationSet"[a, P]], And[Element[c, a], P[c]]]],
		Function[{Typed[a, "Set"], Typed[P, TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[c, "Set"]},
			With[
				{
					range = "elementOfRange"[
						Subtype[Function[{Typed[i, "setIndex"[a]]}, P["setElement"[a, i]]]],
						Function[{Typed[s, Subtype[Function[{Typed[i, "setIndex"[a]]}, P["setElement"[a, i]]]]]}, "setElement"[a, s[[1]]]],
						c
					]
				},
				"equivalentIntroduction"[
					Function[{Typed[m, Element[c, "separationSet"[a, P]]]},
						"existsElimination"[range[[1]][m], Function[{Typed[s, Subtype[Function[{Typed[i, "setIndex"[a]]}, P["setElement"[a, i]]]]], Typed[e, c == "setElement"[a, s[[1]]]]},
							"andIntroduction"[
								"elementOfSet"[a, c][[2]][Typed["existsIntroduction"[s[[1]], e], Exists[{Typed[j, "setIndex"[a]]}, c == "setElement"[a, j]]]],
								Construct["equalitySubstitution", "Set", P, "setElement"[a, s[[1]]], c, "equalitySymmetry"[e], s[[2]]]
							]
						]]
					],
					Function[{Typed[k, And[Element[c, a], P[c]]]},
						"existsElimination"["elementOfSet"[a, c][[1]][k[[1]]], Function[{Typed[i, "setIndex"[a]], Typed[e, c == "setElement"[a, i]]},
							range[[2]][Typed[
								"existsIntroduction"["subtype"[i, Construct["equalitySubstitution", "Set", P, c, "setElement"[a, i], e, k[[2]]]], e],
								Exists[{Typed[s, Subtype[Function[{Typed[j, "setIndex"[a]]}, P["setElement"[a, j]]]]]}, c == "setElement"[a, s[[1]]]]
							]]
						]]
					]
				]
			]
		]
	],
	TypeTheoryDefinition[
		"powerSet",
		Typed[
			Function[{Typed[a, "Set"]},
				"setRange"[
					TypeSpecifier[{"setIndex"[a]} -> TypeUniverse[0]],
					Function[{Typed[p, TypeSpecifier[{"setIndex"[a]} -> TypeUniverse[0]]]}, "separationSet"[a, Function[{Typed[z, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[p[i], z == "setElement"[a, i]]]]]]
				]
			],
			TypeSpecifier[{"Set"} -> "Set"]
		]
	],
	TypeTheoryTheorem[
		"elementOfPower",
		ForAll[{Typed[a, "Set"], Typed[c, "Set"]}, Equivalent[Element[c, "powerSet"[a]], ForAll[{Typed[z, "Set"]}, Implies[Element[z, c], Element[z, a]]]]],
		Function[{Typed[a, "Set"], Typed[c, "Set"]},
			With[
				{
					range = "elementOfRange"[
						TypeSpecifier[{"setIndex"[a]} -> TypeUniverse[0]],
						Function[{Typed[p, TypeSpecifier[{"setIndex"[a]} -> TypeUniverse[0]]]}, "separationSet"[a, Function[{Typed[z, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[p[i], z == "setElement"[a, i]]]]]],
						c
					]
				},
				"equivalentIntroduction"[
					Function[{Typed[m, Element[c, "powerSet"[a]]], Typed[z, "Set"], Typed[n, Element[z, c]]},
						"existsElimination"[range[[1]][m], Function[
							{
								Typed[p, TypeSpecifier[{"setIndex"[a]} -> TypeUniverse[0]]],
								Typed[e, c == "separationSet"[a, Function[{Typed[w, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[p[i], w == "setElement"[a, i]]]]]]
							},
							"elementOfSeparation"[a, Function[{Typed[w, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[p[i], w == "setElement"[a, i]]]], z][[1]][
								Construct["equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, Element[z, s]], c, "separationSet"[a, Function[{Typed[w, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[p[i], w == "setElement"[a, i]]]]], e, n]
							][[1]]
						]]
					],
					Function[{Typed[k, ForAll[{Typed[z, "Set"]}, Implies[Element[z, c], Element[z, a]]]]},
						range[[2]][Typed[
							"existsIntroduction"[
								Function[{Typed[i, "setIndex"[a]]}, Element["setElement"[a, i], c]],
								"extensionality"[
									c,
									"separationSet"[a, Function[{Typed[w, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[Element["setElement"[a, i], c], w == "setElement"[a, i]]]]],
									Function[{Typed[z, "Set"]},
										With[{separation = "elementOfSeparation"[a, Function[{Typed[w, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[Element["setElement"[a, i], c], w == "setElement"[a, i]]]], z]},
											"equivalentIntroduction"[
												Function[{Typed[n, Element[z, c]]},
													separation[[2]]["andIntroduction"[
														k[z, n],
														"existsElimination"["elementOfSet"[a, z][[1]][k[z, n]], Function[{Typed[i, "setIndex"[a]], Typed[e, z == "setElement"[a, i]]},
															Typed[
																"existsIntroduction"[i, "andIntroduction"[Construct["equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, Element[s, c]], z, "setElement"[a, i], e, n], e]],
																Exists[{Typed[j, "setIndex"[a]]}, And[Element["setElement"[a, j], c], z == "setElement"[a, j]]]
															]
														]]
													]]
												],
												Function[{Typed[n, Element[z, "separationSet"[a, Function[{Typed[w, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[Element["setElement"[a, i], c], w == "setElement"[a, i]]]]]]]},
													"existsElimination"[separation[[1]][n][[2]], Function[{Typed[i, "setIndex"[a]], Typed[q, And[Element["setElement"[a, i], c], z == "setElement"[a, i]]]},
														Construct["equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, Element[s, c]], "setElement"[a, i], z, "equalitySymmetry"[q[[2]]], q[[1]]]
													]]
												]
											]
										]
									]
								]
							],
							Exists[
								{Typed[p, TypeSpecifier[{"setIndex"[a]} -> TypeUniverse[0]]]},
								c == "separationSet"[a, Function[{Typed[w, "Set"]}, Exists[{Typed[i, "setIndex"[a]]}, And[p[i], w == "setElement"[a, i]]]]]
							]
						]]
					]
				]
			]
		]
	],
	(* induction on membership, from induction on pre-sets *)
	TypeTheoryTheorem[
		"elementInduction",
		ForAll[
			{Typed[P, TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			Implies[ForAll[{Typed[a, "Set"]}, Implies[ForAll[{Typed[b, "Set"]}, Implies[Element[b, a], P[b]]], P[a]]], ForAll[{Typed[a, "Set"]}, P[a]]]
		],
		Function[
			{
				Typed[P, TypeSpecifier[{"Set"} -> TypeUniverse[0]]],
				Typed[h, ForAll[{Typed[a, "Set"]}, Implies[ForAll[{Typed[b, "Set"]}, Implies[Element[b, a], P[b]]], P[a]]]],
				Typed[a, "Set"]
			},
			Construct[
				QuotientInduction,
				"PreSet",
				"preSetEquivalent",
				P,
				Function[{Typed[x, "PreSet"]},
					InductiveRecursor["PreSet"][
						Function[{Typed[s, "PreSet"]}, P["setOfPreSet"[s]]],
						Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]], Typed[r, ForAll[{Typed[i, \[Alpha]]}, P["setOfPreSet"[f[i]]]]]},
							h["setOfPreSet"["preSet"[\[Alpha], f]], Function[{Typed[b, "Set"], Typed[m, Element[b, "setOfPreSet"["preSet"[\[Alpha], f]]]]},
								"existsElimination"["elementOfSetOfPreSet"["preSet"[\[Alpha], f], b][[1]][m], Function[{Typed[j, \[Alpha]], Typed[e, b == "setOfPreSet"[f[j]]]},
									Construct["equalitySubstitution", "Set", P, "setOfPreSet"[f[j]], b, "equalitySymmetry"[e], r[j]]
								]]
							]]
						],
						x
					]
				],
				a
			]
		]
	],

	(* classes, the two equalities that carry set.mm's statements to sets, regularity *)
	TypeTheoryDefinition["Class", Typed[TypeSpecifier[{"Set"} -> TypeUniverse[0]], TypeUniverse[2]]],
	TypeTheoryDefinition["setClass", Typed[Function[{Typed[x, "Set"], Typed[z, "Set"]}, Element[z, x]], TypeSpecifier[{"Set"} -> "Class"]]],
	TypeTheoryDefinition["classAbstraction", Typed[Function[{Typed[P, TypeSpecifier[{"Set"} -> TypeUniverse[0]]]}, P], TypeSpecifier[{TypeSpecifier[{"Set"} -> TypeUniverse[0]]} -> "Class"]]],
	TypeTheoryDefinition[
		"classElement",
		Typed[Function[{Typed[A, "Class"], Typed[B, "Class"]}, Exists[{Typed[a, "Set"]}, And[A == "setClass"[a], B[a]]]], TypeSpecifier[{"Class", "Class"} -> TypeUniverse[0]]]
	],
	TypeTheoryTheorem[
		"setClassInjective",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Implies["setClass"[x] == "setClass"[y], x == y]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[h, "setClass"[x] == "setClass"[y]]},
			"extensionality"[x, y, Function[{Typed[z, "Set"]},
				Construct[
					"equalitySubstitution",
					"Class",
					Function[{Typed[C, "Class"]}, Equivalent[Element[z, x], C[z]]],
					"setClass"[x],
					"setClass"[y],
					h,
					"equivalentReflexivity"[Element[z, x]]
				]
			]]
		]
	],
	TypeTheoryTheorem[
		"classElementSetClass",
		ForAll[{Typed[x, "Set"], Typed[B, "Class"]}, Equivalent["classElement"["setClass"[x], B], B[x]]],
		Function[{Typed[x, "Set"], Typed[B, "Class"]},
			"equivalentIntroduction"[
				Function[{Typed[m, "classElement"["setClass"[x], B]]},
					"existsElimination"[m, Function[{Typed[a, "Set"], Typed[k, And["setClass"[x] == "setClass"[a], B[a]]]},
						Construct["equalitySubstitution", "Set", B, a, x, "equalitySymmetry"["setClassInjective"[x, a, k[[1]]]], k[[2]]]
					]]
				],
				Function[{Typed[k, B[x]]},
					Typed["existsIntroduction"[x, "andIntroduction"["equalityReflexivity"["setClass"[x]], k]], "classElement"["setClass"[x], B]]
				]
			]
		]
	],
	(* the two equalities of functions that carry a statement of set.mm to one of sets *)
	TypeTheoryTheorem[
		"classElementFunction",
		Function[{Typed[B, "Class"], Typed[z, "Set"]}, "classElement"["setClass"[z], B]] == Function[{Typed[B, "Class"], Typed[z, "Set"]}, B[z]],
		"functionExtensionality"[Function[{Typed[B, "Class"]},
			"functionExtensionality"[Function[{Typed[z, "Set"]}, "propositionalExtensionality"["classElementSetClass"[z, B]]]]
		]]
	],
	TypeTheoryTheorem[
		"setClassEqualFunction",
		Function[{Typed[x, "Set"], Typed[y, "Set"]}, "setClass"[x] == "setClass"[y]] == Function[{Typed[x, "Set"], Typed[y, "Set"]}, x == y],
		"functionExtensionality"[Function[{Typed[x, "Set"]},
			"functionExtensionality"[Function[{Typed[y, "Set"]},
				"propositionalExtensionality"["equivalentIntroduction"[
					"setClassInjective"[x, y],
					Function[{Typed[e, x == y]}, "equalityCongruence"["setClass", e]]
				]]
			]]
		]]
	],
	(* regularity, classically from induction on membership *)
	TypeTheoryTheorem[
		"regularity",
		ForAll[
			{Typed[x, "Set"]},
			Implies[
				Exists[{Typed[y, "Set"]}, Element[y, x]],
				Exists[{Typed[y, "Set"]}, And[Element[y, x], ForAll[{Typed[z, "Set"]}, Implies[Element[z, y], Not[Element[z, x]]]]]]
			]
		],
		Function[{Typed[x, "Set"], Typed[h, Exists[{Typed[y, "Set"]}, Element[y, x]]]},
			"doubleNegationElimination"[
				Exists[{Typed[y, "Set"]}, And[Element[y, x], ForAll[{Typed[z, "Set"]}, Implies[Element[z, y], Not[Element[z, x]]]]]],
				Function[{Typed[none, Not[Exists[{Typed[y, "Set"]}, And[Element[y, x], ForAll[{Typed[z, "Set"]}, Implies[Element[z, y], Not[Element[z, x]]]]]]]]},
					"existsElimination"[h, Function[{Typed[y, "Set"], Typed[m, Element[y, x]]},
						"elementInduction"[
							Function[{Typed[a, "Set"]}, Not[Element[a, x]]],
							Function[{Typed[a, "Set"], Typed[r, ForAll[{Typed[b, "Set"]}, Implies[Element[b, a], Not[Element[b, x]]]]], Typed[n, Element[a, x]]},
								none["existsIntroduction"[a, "andIntroduction"[n, r]]]
							],
							y,
							m
						]
					]]
				]
			]
		]
	],

	(* replacement and infinity *)
	(* replacement: the chosen values of a functional relation on the members of x *)
	TypeTheoryTheorem[
		"replacement",
		ForAll[
			{Typed[\[Psi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"]},
			Implies[
				ForAll[{Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[\[Psi][z, w], z == y]]]],
				Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Equivalent[Element[z, y], Exists[{Typed[w, "Set"]}, And[Element[w, x], \[Psi][z, w]]]]]]
			]
		],
		Function[
			{
				Typed[\[Psi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"],
				Typed[functional, ForAll[{Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[\[Psi][z, w], z == y]]]]]
			},
			With[
				{
					image = "setRange"[
						Subtype[Function[{Typed[i, "setIndex"[x]]}, Exists[{Typed[z, "Set"]}, \[Psi][z, "setElement"[x, i]]]]],
						Function[{Typed[s, Subtype[Function[{Typed[i, "setIndex"[x]]}, Exists[{Typed[z, "Set"]}, \[Psi][z, "setElement"[x, i]]]]]]}, ChosenWitness[s[[2]]]]
					]
				},
				Typed[
					"existsIntroduction"[image, Function[{Typed[z, "Set"]},
						With[
							{
								range = "elementOfRange"[
									Subtype[Function[{Typed[i, "setIndex"[x]]}, Exists[{Typed[v, "Set"]}, \[Psi][v, "setElement"[x, i]]]]],
									Function[{Typed[s, Subtype[Function[{Typed[i, "setIndex"[x]]}, Exists[{Typed[v, "Set"]}, \[Psi][v, "setElement"[x, i]]]]]]}, ChosenWitness[s[[2]]]],
									z
								]
							},
							"equivalentIntroduction"[
								Function[{Typed[m, Element[z, image]]},
									"existsElimination"[range[[1]][m], Function[
										{
											Typed[s, Subtype[Function[{Typed[i, "setIndex"[x]]}, Exists[{Typed[v, "Set"]}, \[Psi][v, "setElement"[x, i]]]]]],
											Typed[e, z == ChosenWitness[s[[2]]]]
										},
										Typed[
											"existsIntroduction"[
												"setElement"[x, s[[1]]],
												"andIntroduction"[
													"elementOfSet"[x, "setElement"[x, s[[1]]]][[2]][Typed["existsIntroduction"[s[[1]], "equalityReflexivity"["setElement"[x, s[[1]]]]], Exists[{Typed[j, "setIndex"[x]]}, "setElement"[x, s[[1]]] == "setElement"[x, j]]]],
													Construct[
														"equalitySubstitution", "Set", Function[{Typed[v, "Set"]}, \[Psi][v, "setElement"[x, s[[1]]]]],
														ChosenWitness[s[[2]]], z, "equalitySymmetry"[e], "chosenWitnessProperty"[s[[2]]]
													]
												]
											],
											Exists[{Typed[w, "Set"]}, And[Element[w, x], \[Psi][z, w]]]
										]
									]]
								],
								Function[{Typed[m, Exists[{Typed[w, "Set"]}, And[Element[w, x], \[Psi][z, w]]]]},
									"existsElimination"[m, Function[{Typed[w, "Set"], Typed[k, And[Element[w, x], \[Psi][z, w]]]},
										"existsElimination"["elementOfSet"[x, w][[1]][k[[1]]], Function[{Typed[i, "setIndex"[x]], Typed[e, w == "setElement"[x, i]]},
											With[{holds = Construct["equalitySubstitution", "Set", Function[{Typed[v, "Set"]}, \[Psi][z, v]], w, "setElement"[x, i], e, k[[2]]]},
												With[{exists = Typed["existsIntroduction"[z, holds], Exists[{Typed[v, "Set"]}, \[Psi][v, "setElement"[x, i]]]]},
													"existsElimination"[functional["setElement"[x, i]], Function[
														{Typed[y, "Set"], Typed[unique, ForAll[{Typed[v, "Set"]}, Implies[\[Psi][v, "setElement"[x, i]], v == y]]]},
														range[[2]][Typed[
															"existsIntroduction"[
																"subtype"[i, exists],
																"equalityTransitivity"[unique[z, holds], "equalitySymmetry"[unique[ChosenWitness[exists], "chosenWitnessProperty"[exists]]]]
															],
															Exists[
																{Typed[s, Subtype[Function[{Typed[j, "setIndex"[x]]}, Exists[{Typed[v, "Set"]}, \[Psi][v, "setElement"[x, j]]]]]]},
																z == ChosenWitness[s[[2]]]
															]
														]]
													]]
												]
											]
										]]
									]]
								]
							]
						]
					]],
					Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Equivalent[Element[z, y], Exists[{Typed[w, "Set"]}, And[Element[w, x], \[Psi][z, w]]]]]]
				]
			]
		]
	],
	(* infinity, in the form of set.mm: x, its singleton, the singleton of that, and so on *)
	TypeTheoryDefinition[
		"singletonIterate",
		Typed[
			Function[{Typed[x, "Set"], Typed[n, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, "Set"], x, Function[{Typed[k, NonNegativeIntegers], Typed[r, "Set"]}, "pairSet"[r, r]], n]
			],
			TypeSpecifier[{"Set", NonNegativeIntegers} -> "Set"]
		]
	],
	TypeTheoryTheorem[
		"infinity",
		ForAll[
			{Typed[x, "Set"]},
			Exists[{Typed[y, "Set"]}, And[Element[x, y], ForAll[{Typed[z, "Set"]}, Implies[Element[z, y], Exists[{Typed[w, "Set"]}, And[Element[z, w], Element[w, y]]]]]]]
		],
		Function[{Typed[x, "Set"]},
			With[{range = Function[{Typed[c, "Set"]}, "elementOfRange"[NonNegativeIntegers, Function[{Typed[n, NonNegativeIntegers]}, "singletonIterate"[x, n]], c]]},
				Typed[
					"existsIntroduction"[
						"setRange"[NonNegativeIntegers, Function[{Typed[n, NonNegativeIntegers]}, "singletonIterate"[x, n]]],
						"andIntroduction"[
							range[x][[2]][Typed["existsIntroduction"["zero", "equalityReflexivity"[x]], Exists[{Typed[n, NonNegativeIntegers]}, x == "singletonIterate"[x, n]]]],
							Function[{Typed[z, "Set"], Typed[m, Element[z, "setRange"[NonNegativeIntegers, Function[{Typed[n, NonNegativeIntegers]}, "singletonIterate"[x, n]]]]]},
								"existsElimination"[range[z][[1]][m], Function[{Typed[n, NonNegativeIntegers], Typed[e, z == "singletonIterate"[x, n]]},
									Typed[
										"existsIntroduction"[
											"pairSet"["singletonIterate"[x, n], "singletonIterate"[x, n]],
											"andIntroduction"[
												"elementOfPair"["singletonIterate"[x, n], "singletonIterate"[x, n], z][[2]]["orIntroductionLeft"[e]],
												range["pairSet"["singletonIterate"[x, n], "singletonIterate"[x, n]]][[2]][Typed[
													"existsIntroduction"["successor"[n], "equalityReflexivity"["pairSet"["singletonIterate"[x, n], "singletonIterate"[x, n]]]],
													Exists[{Typed[k, NonNegativeIntegers]}, "pairSet"["singletonIterate"[x, n], "singletonIterate"[x, n]] == "singletonIterate"[x, k]]
												]]
											]
										],
										Exists[{Typed[w, "Set"]}, And[Element[z, w], Element[w, "setRange"[NonNegativeIntegers, Function[{Typed[k, NonNegativeIntegers]}, "singletonIterate"[x, k]]]]]]
									]
								]]
							]
						]
					],
					Exists[{Typed[y, "Set"]}, And[Element[x, y], ForAll[{Typed[z, "Set"]}, Implies[Element[z, y], Exists[{Typed[w, "Set"]}, And[Element[z, w], Element[w, y]]]]]]]
				]
			]
		]
	],

	(* choice, in the form of set.mm *)
	TypeTheoryDefinition[
		"orElimination",
		Function[
			{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], TypedImplicit[c, TypeUniverse[0]], Typed[h, Or[a, b]], Typed[l, Implies[a, c]], Typed[r, Implies[b, c]]},
			InductiveRecursor[Or][Function[{Typed[o, Or[a, b]]}, c], l, r, h]
		]
	],
	TypeTheoryTheorem[
		"elementIrreflexive",
		ForAll[{Typed[a, "Set"]}, Not[Element[a, a]]],
		"elementInduction"[
			Function[{Typed[a, "Set"]}, Not[Element[a, a]]],
			Function[{Typed[a, "Set"], Typed[r, ForAll[{Typed[b, "Set"]}, Implies[Element[b, a], Not[Element[b, b]]]]], Typed[m, Element[a, a]]}, r[a, m, m]]
		]
	],
	TypeTheoryTheorem[
		"elementAsymmetric",
		ForAll[{Typed[a, "Set"], Typed[b, "Set"]}, Implies[Element[a, b], Not[Element[b, a]]]],
		"elementInduction"[
			Function[{Typed[a, "Set"]}, ForAll[{Typed[b, "Set"]}, Implies[Element[a, b], Not[Element[b, a]]]]],
			Function[
				{
					Typed[a, "Set"],
					Typed[r, ForAll[{Typed[c, "Set"]}, Implies[Element[c, a], ForAll[{Typed[b, "Set"]}, Implies[Element[c, b], Not[Element[b, c]]]]]]],
					Typed[b, "Set"], Typed[m, Element[a, b]], Typed[n, Element[b, a]]
				},
				r[b, n, a, n, m]
			]
		]
	],
	(* the chosen member of a set depends on the set alone *)
	TypeTheoryTheorem[
		"chosenElementCongruence",
		ForAll[
			{Typed[a, "Set"], Typed[b, "Set"]},
			Implies[a == b, ForAll[{Typed[h, Exists[{Typed[q, "Set"]}, Element[q, a]]], Typed[k, Exists[{Typed[q, "Set"]}, Element[q, b]]]}, ChosenWitness[h] == ChosenWitness[k]]]
		],
		Function[{Typed[a, "Set"], Typed[b, "Set"], Typed[e, a == b]},
			Construct[
				"equalitySubstitution",
				"Set",
				Function[{Typed[c, "Set"]}, ForAll[{Typed[h, Exists[{Typed[q, "Set"]}, Element[q, a]]], Typed[k, Exists[{Typed[q, "Set"]}, Element[q, c]]]}, ChosenWitness[h] == ChosenWitness[k]]],
				a,
				b,
				e,
				Function[{Typed[h, Exists[{Typed[q, "Set"]}, Element[q, a]]], Typed[k, Exists[{Typed[q, "Set"]}, Element[q, a]]]}, "equalityReflexivity"[ChosenWitness[h]]]
			]
		]
	],
	(* the indices of the nonempty members of x, and the pairs of each with its chosen member *)
	TypeTheoryDefinition[
		"nonemptyIndex",
		Typed[
			Function[{Typed[x, "Set"]}, Subtype[Function[{Typed[i, "setIndex"[x]]}, Exists[{Typed[q, "Set"]}, Element[q, "setElement"[x, i]]]]]],
			TypeSpecifier[{"Set"} -> TypeUniverse[1]]
		]
	],
	TypeTheoryDefinition[
		"choiceSet",
		Typed[
			Function[{Typed[x, "Set"]},
				"setRange"["nonemptyIndex"[x], Function[{Typed[s, "nonemptyIndex"[x]]}, "pairSet"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]]]]]
			],
			TypeSpecifier[{"Set"} -> "Set"]
		]
	],
	TypeTheoryTheorem[
		"choiceAxiom",
		ForAll[
			{Typed[x, "Set"]},
			Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"], Typed[w, "Set"]}, Implies[
				And[Element[z, w], Element[w, x]],
				Exists[{Typed[v, "Set"]}, ForAll[{Typed[u, "Set"]}, Equivalent[
					Exists[{Typed[t, "Set"]}, And[And[Element[u, w], Element[w, t]], And[Element[u, t], Element[t, y]]]],
					u == v
				]]]
			]]]
		],
		Function[{Typed[x, "Set"]},
			Typed[
				"existsIntroduction"["choiceSet"[x], Function[{Typed[z, "Set"], Typed[w, "Set"], Typed[zw, And[Element[z, w], Element[w, x]]]},
					With[{nonempty = Typed["existsIntroduction"[z, zw[[1]]], Exists[{Typed[q, "Set"]}, Element[q, w]]]},
						Typed[
							"existsIntroduction"[ChosenWitness[nonempty], Function[{Typed[u, "Set"]},
								"equivalentIntroduction"[
									(* a pair of the choice set holding u and w is the pair of w and its chosen member *)
									Function[{Typed[k, Exists[{Typed[t, "Set"]}, And[And[Element[u, w], Element[w, t]], And[Element[u, t], Element[t, "choiceSet"[x]]]]]]},
										"existsElimination"[k, Function[{Typed[t, "Set"], Typed[kt, And[And[Element[u, w], Element[w, t]], And[Element[u, t], Element[t, "choiceSet"[x]]]]]},
											"existsElimination"[
												"elementOfRange"["nonemptyIndex"[x], Function[{Typed[s, "nonemptyIndex"[x]]}, "pairSet"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]]]], t][[1]][kt[[2]][[2]]],
												Function[{Typed[s, "nonemptyIndex"[x]], Typed[et, t == "pairSet"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]]]]},
													With[
														{
															wInPair = Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[w, c]], t, "pairSet"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]]], et, kt[[1]][[2]]],
															uInPair = Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[u, c]], t, "pairSet"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]]], et, kt[[2]][[1]]]
														},
														"orElimination"[
															"elementOfPair"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]], w][[1]][wInPair],
															(* w is the first of the pair: u is then w, a member of itself, or its chosen member *)
															Function[{Typed[wa, w == "setElement"[x, s[[1]]]]},
																"orElimination"[
																	"elementOfPair"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]], u][[1]][uInPair],
																	Function[{Typed[ua, u == "setElement"[x, s[[1]]]]},
																		Typed[
																			"falseElimination"["elementIrreflexive"[w, Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[c, w]], u, w, "equalityTransitivity"[ua, "equalitySymmetry"[wa]], kt[[1]][[1]]]]],
																			u == ChosenWitness[nonempty]
																		]
																	],
																	Function[{Typed[uca, u == ChosenWitness[s[[2]]]]},
																		"equalityTransitivity"[uca, "equalitySymmetry"["chosenElementCongruence"[w, "setElement"[x, s[[1]]], wa, nonempty, s[[2]]]]]
																	]
																]
															],
															(* w is the chosen member of the first: either way a cycle of membership *)
															Function[{Typed[wca, w == ChosenWitness[s[[2]]]]},
																With[{wa = Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[c, "setElement"[x, s[[1]]]]], ChosenWitness[s[[2]]], w, "equalitySymmetry"[wca], "chosenWitnessProperty"[s[[2]]]]},
																	"orElimination"[
																		"elementOfPair"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]], u][[1]][uInPair],
																		Function[{Typed[ua, u == "setElement"[x, s[[1]]]]},
																			Typed[
																				"falseElimination"["elementAsymmetric"[u, w, kt[[1]][[1]], Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[w, c]], "setElement"[x, s[[1]]], u, "equalitySymmetry"[ua], wa]]],
																				u == ChosenWitness[nonempty]
																			]
																		],
																		Function[{Typed[uca, u == ChosenWitness[s[[2]]]]},
																			Typed[
																				"falseElimination"["elementIrreflexive"[u, Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[u, c]], w, u, "equalityTransitivity"[wca, "equalitySymmetry"[uca]], kt[[1]][[1]]]]],
																				u == ChosenWitness[nonempty]
																			]
																		]
																	]
																]
															]
														]
													]
												]
											]
										]]
									],
									(* the chosen member of w is in the pair of w's index *)
									Function[{Typed[e, u == ChosenWitness[nonempty]]},
										"existsElimination"["elementOfSet"[x, w][[1]][zw[[2]]], Function[{Typed[i, "setIndex"[x]], Typed[ew, w == "setElement"[x, i]]},
											With[
												{
													ni = Typed[
														"existsIntroduction"[z, Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[z, c]], w, "setElement"[x, i], ew, zw[[1]]]],
														Exists[{Typed[q, "Set"]}, Element[q, "setElement"[x, i]]]
													]
												},
												Typed[
													"existsIntroduction"[
														"pairSet"["setElement"[x, i], ChosenWitness[ni]],
														"andIntroduction"[
															"andIntroduction"[
																Construct["equalitySubstitution", "Set", Function[{Typed[c, "Set"]}, Element[c, w]], ChosenWitness[nonempty], u, "equalitySymmetry"[e], "chosenWitnessProperty"[nonempty]],
																"elementOfPair"["setElement"[x, i], ChosenWitness[ni], w][[2]]["orIntroductionLeft"[ew]]
															],
															"andIntroduction"[
																"elementOfPair"["setElement"[x, i], ChosenWitness[ni], u][[2]]["orIntroductionRight"["equalityTransitivity"[e, "chosenElementCongruence"[w, "setElement"[x, i], ew, nonempty, ni]]]],
																"elementOfRange"["nonemptyIndex"[x], Function[{Typed[s, "nonemptyIndex"[x]]}, "pairSet"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]]]], "pairSet"["setElement"[x, i], ChosenWitness[ni]]][[2]][
																	Typed[
																		"existsIntroduction"["subtype"[i, ni], "equalityReflexivity"["pairSet"["setElement"[x, i], ChosenWitness[ni]]]],
																		Exists[{Typed[s, "nonemptyIndex"[x]]}, "pairSet"["setElement"[x, i], ChosenWitness[ni]] == "pairSet"["setElement"[x, s[[1]]], ChosenWitness[s[[2]]]]]
																	]
																]
															]
														]
													],
													Exists[{Typed[t, "Set"]}, And[And[Element[u, w], Element[w, t]], And[Element[u, t], Element[t, "choiceSet"[x]]]]]
												]
											]
										]]
									]
								]
							]],
							Exists[{Typed[v, "Set"]}, ForAll[{Typed[u, "Set"]}, Equivalent[
								Exists[{Typed[t, "Set"]}, And[And[Element[u, w], Element[w, t]], And[Element[u, t], Element[t, "choiceSet"[x]]]]],
								u == v
							]]]
						]
					]
				]],
				Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"], Typed[w, "Set"]}, Implies[
					And[Element[z, w], Element[w, x]],
					Exists[{Typed[v, "Set"]}, ForAll[{Typed[u, "Set"]}, Equivalent[
						Exists[{Typed[t, "Set"]}, And[And[Element[u, w], Element[w, t]], And[Element[u, t], Element[t, y]]]],
						u == v
					]]]
				]]]
			]
		]
	]
}


(* ::Subsection:: *)
(*The axioms of set.mm*)


(* a theorem in set.mm's vocabulary from its proof about sets: the held statement with each "classElement"["setClass"[t], B]
   made membership[B, t] is the motive of a substitution along "classElementFunction", and with each
   "setClass"[a] == "setClass"[b] also made equality[a, b], that of one along "setClassEqualFunction"; at the two functions
   (B, z) |-> B[z] and (a, b) |-> a == b the statement is about Element and == of sets, which proof proves *)
SetAttributes[setmmTheorem, HoldAll]
setmmTheorem[name_, statement_, native_] := Module[{membership, equality},
	With[
		{
			byMembership = Hold[statement] /. HoldPattern["classElement"["setClass"[t_], b_]] :> membership[b, t]
		},
		With[{byBoth = byMembership /. HoldPattern["setClass"[a_] == "setClass"[b_]] :> equality[a, b] /. membership -> Function[{Typed[B, "Class"], Typed[z, "Set"]}, B[z]]},
			Replace[
				{byMembership, byBoth, Hold[native]},
				{Hold[k_], Hold[kl_], Hold[proof_]} :> TypeTheoryTheorem[
					name,
					statement,
					Construct[
						"equalitySubstitution",
						TypeSpecifier[{"Class", "Set"} -> TypeUniverse[0]],
						Function[{Typed[membership, TypeSpecifier[{"Class", "Set"} -> TypeUniverse[0]]]}, k],
						Function[{Typed[B, "Class"], Typed[z, "Set"]}, B[z]],
						Function[{Typed[B, "Class"], Typed[z, "Set"]}, "classElement"["setClass"[z], B]],
						"equalitySymmetry"["classElementFunction"],
						Construct[
							"equalitySubstitution",
							TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]],
							Function[{Typed[equality, TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]}, kl],
							Function[{Typed[a, "Set"], Typed[b, "Set"]}, a == b],
							Function[{Typed[a, "Set"], Typed[b, "Set"]}, "setClass"[a] == "setClass"[b]],
							"equalitySymmetry"["setClassEqualFunction"],
							proof
						]
					]
				]
			]
		]
	]
]

$setmmDeclarations = {
	(* propositional calculus *)
	TypeTheoryTheorem[
		"ax-mp",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Implies[\[CurlyPhi], Implies[Implies[\[CurlyPhi], \[Psi]], \[Psi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[minor, \[CurlyPhi]], Typed[major, Implies[\[CurlyPhi], \[Psi]]]}, major[minor]]
	],
	TypeTheoryTheorem[
		"ax-1",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Implies[\[CurlyPhi], Implies[\[Psi], \[CurlyPhi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[p, \[CurlyPhi]], Typed[q, \[Psi]]}, p]
	],
	TypeTheoryTheorem[
		"ax-2",
		ForAll[
			{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[\[Chi], TypeUniverse[0]]},
			Implies[Implies[\[CurlyPhi], Implies[\[Psi], \[Chi]]], Implies[Implies[\[CurlyPhi], \[Psi]], Implies[\[CurlyPhi], \[Chi]]]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[\[Chi], TypeUniverse[0]],
				Typed[f, Implies[\[CurlyPhi], Implies[\[Psi], \[Chi]]]], Typed[g, Implies[\[CurlyPhi], \[Psi]]], Typed[p, \[CurlyPhi]]
			},
			f[p, g[p]]
		]
	],
	TypeTheoryTheorem[
		"ax-3",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Implies[Implies[Not[\[CurlyPhi]], Not[\[Psi]]], Implies[\[Psi], \[CurlyPhi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[f, Implies[Not[\[CurlyPhi]], Not[\[Psi]]]], Typed[q, \[Psi]]},
			"doubleNegationElimination"[\[CurlyPhi], Function[{Typed[n, Not[\[CurlyPhi]]]}, f[n, q]]]
		]
	],
	TypeTheoryTheorem[
		"df-bi",
		ForAll[
			{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]},
			Not[Implies[
				Implies[Equivalent[\[CurlyPhi], \[Psi]], Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]],
				Not[Implies[Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]], Equivalent[\[CurlyPhi], \[Psi]]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]],
				Typed[k, Implies[
					Implies[Equivalent[\[CurlyPhi], \[Psi]], Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]],
					Not[Implies[Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]], Equivalent[\[CurlyPhi], \[Psi]]]]
				]]
			},
			k[
				Function[{Typed[e, Equivalent[\[CurlyPhi], \[Psi]]], Typed[m, Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]}, m[e[[1]], e[[2]]]],
				Function[{Typed[b, Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]]},
					"equivalentIntroduction"[
						"doubleNegationElimination"[Implies[\[CurlyPhi], \[Psi]], Function[{Typed[n, Not[Implies[\[CurlyPhi], \[Psi]]]]},
							b[Function[{Typed[f, Implies[\[CurlyPhi], \[Psi]]]}, Typed["falseElimination"[n[f]], Not[Implies[\[Psi], \[CurlyPhi]]]]]]
						]],
						"doubleNegationElimination"[Implies[\[Psi], \[CurlyPhi]], Function[{Typed[n, Not[Implies[\[Psi], \[CurlyPhi]]]]},
							b[Function[{Typed[f, Implies[\[CurlyPhi], \[Psi]]]}, n]]
						]]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-an",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Equivalent[And[\[CurlyPhi], \[Psi]], Not[Implies[\[CurlyPhi], Not[\[Psi]]]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]},
			"equivalentIntroduction"[
				Function[{Typed[a, And[\[CurlyPhi], \[Psi]]], Typed[k, Implies[\[CurlyPhi], Not[\[Psi]]]]}, k[a[[1]], a[[2]]]],
				Function[{Typed[b, Not[Implies[\[CurlyPhi], Not[\[Psi]]]]]},
					"andIntroduction"[
						"doubleNegationElimination"[\[CurlyPhi], Function[{Typed[n, Not[\[CurlyPhi]]]}, b[Function[{Typed[p, \[CurlyPhi]]}, Typed["falseElimination"[n[p]], Not[\[Psi]]]]]]],
						"doubleNegationElimination"[\[Psi], Function[{Typed[n, Not[\[Psi]]]}, b[Function[{Typed[p, \[CurlyPhi]]}, n]]]]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-or",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Equivalent[Or[\[CurlyPhi], \[Psi]], Implies[Not[\[CurlyPhi]], \[Psi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]},
			"equivalentIntroduction"[
				Function[{Typed[o, Or[\[CurlyPhi], \[Psi]]], Typed[n, Not[\[CurlyPhi]]]},
					"orElimination"[o, Function[{Typed[p, \[CurlyPhi]]}, Typed["falseElimination"[n[p]], \[Psi]]], Function[{Typed[q, \[Psi]]}, q]]
				],
				Function[{Typed[f, Implies[Not[\[CurlyPhi]], \[Psi]]]},
					"orElimination"["excludedMiddle"[\[CurlyPhi]], Function[{Typed[p, \[CurlyPhi]]}, "orIntroductionLeft"[p]], Function[{Typed[n, Not[\[CurlyPhi]]]}, "orIntroductionRight"[f[n]]]]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-tru",
		ForAll[{Typed[x, "Set"]}, Equivalent[True, Implies[ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]], ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]]]]],
		Function[{Typed[x, "Set"]},
			"equivalentIntroduction"[
				Function[{Typed[t, True], Typed[h, ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]]]}, h],
				Function[{Typed[f, Implies[ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]], ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]]]]}, "trueIntroduction"]
			]
		]
	],
	TypeTheoryTheorem[
		"df-fal",
		Equivalent[False, Not[True]],
		"equivalentIntroduction"[
			Function[{Typed[f, False]}, Typed["falseElimination"[f], Not[True]]],
			Function[{Typed[n, Not[True]]}, n["trueIntroduction"]]
		]
	],
	(* predicate calculus *)
	TypeTheoryTheorem[
		"df-ex",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"]}, Equivalent[Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]], Not[ForAll[{Typed[x, "Set"]}, Not[\[CurlyPhi][x]]]]]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"]},
			"equivalentIntroduction"[
				Function[{Typed[e, Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]]], Typed[n, ForAll[{Typed[x, "Set"]}, Not[\[CurlyPhi][x]]]]},
					"existsElimination"[e, Function[{Typed[w, "Set"], Typed[p, \[CurlyPhi][w]]}, n[w, p]]]
				],
				Function[{Typed[k, Not[ForAll[{Typed[x, "Set"]}, Not[\[CurlyPhi][x]]]]]},
					"doubleNegationElimination"[
						Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]],
						Function[{Typed[n, Not[Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]},
							k[Function[{Typed[w, "Set"], Typed[p, \[CurlyPhi][w]]}, n[Typed["existsIntroduction"[w, p], Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]]]
						]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"ax-gen",
		ForAll[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]}, Implies[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]], ForAll[{Typed[x, "Set"]}, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[h, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]], Typed[x, "Set"], Typed[w, "Set"]}, h[w]]
	],
	TypeTheoryTheorem[
		"ax-4",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[\[Psi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"]}, Implies[
				ForAll[{Typed[x, "Set"]}, Implies[\[CurlyPhi][x], \[Psi][x]]],
				Implies[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]], ForAll[{Typed[x, "Set"]}, \[Psi][x]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[\[Psi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"],
				Typed[f, ForAll[{Typed[x, "Set"]}, Implies[\[CurlyPhi][x], \[Psi][x]]]], Typed[g, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]], Typed[w, "Set"]
			},
			f[w, g[w]]
		]
	],
	TypeTheoryTheorem[
		"ax-5",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]]}, ForAll[{Typed[x, "Set"]}, Implies[\[CurlyPhi], ForAll[{Typed[x, "Set"]}, \[CurlyPhi]]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[x, "Set"], Typed[p, \[CurlyPhi]], Typed[w, "Set"]}, p]
	],
	TypeTheoryTheorem[
		"ax-6",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Not[ForAll[{Typed[x, "Set"]}, Not["setClass"[x] == "setClass"[y]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[h, ForAll[{Typed[x, "Set"]}, Not["setClass"[x] == "setClass"[y]]]]}, h[y, "equalityReflexivity"["setClass"[y]]]]
	],
	TypeTheoryTheorem[
		"ax-7",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies["setClass"[x] == "setClass"[y], Implies["setClass"[x] == "setClass"[z], "setClass"[y] == "setClass"[z]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[e, "setClass"[x] == "setClass"[y]], Typed[f, "setClass"[x] == "setClass"[z]]},
			"equalityTransitivity"["equalitySymmetry"[e], f]
		]
	],
	TypeTheoryTheorem[
		"ax-8",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies["setClass"[x] == "setClass"[y], Implies["classElement"["setClass"[x], "setClass"[z]], "classElement"["setClass"[y], "setClass"[z]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[e, "setClass"[x] == "setClass"[y]]},
			Construct["equalitySubstitution", "Class", Function[{Typed[C, "Class"]}, "classElement"[C, "setClass"[z]]], "setClass"[x], "setClass"[y], e]
		]
	],
	TypeTheoryTheorem[
		"ax-9",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies["setClass"[x] == "setClass"[y], Implies["classElement"["setClass"[z], "setClass"[x]], "classElement"["setClass"[z], "setClass"[y]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[e, "setClass"[x] == "setClass"[y]]},
			Construct["equalitySubstitution", "Class", Function[{Typed[C, "Class"]}, "classElement"["setClass"[z], C]], "setClass"[x], "setClass"[y], e]
		]
	],
	TypeTheoryTheorem[
		"ax-10",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"]}, Implies[Not[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]], ForAll[{Typed[x, "Set"]}, Not[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[n, Not[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]]], Typed[w, "Set"]}, n]
	],
	TypeTheoryTheorem[
		"ax-11",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Implies[
				ForAll[{Typed[x, "Set"]}, ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]],
				ForAll[{Typed[y, "Set"]}, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x, y]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"],
				Typed[h, ForAll[{Typed[x, "Set"]}, ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]]], Typed[v, "Set"], Typed[w, "Set"]
			},
			h[w, v]
		]
	],
	TypeTheoryTheorem[
		"ax-12",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Implies[
				"setClass"[x] == "setClass"[y],
				Implies[ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]], ForAll[{Typed[x, "Set"]}, Implies["setClass"[x] == "setClass"[y], \[CurlyPhi][x, y]]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"],
				Typed[e, "setClass"[x] == "setClass"[y]], Typed[h, ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]],
				Typed[w, "Set"], Typed[f, "setClass"[w] == "setClass"[y]]
			},
			Construct[
				"equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, \[CurlyPhi][s, y]], x, w,
				"setClassInjective"[x, w, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
				h[y]
			]
		]
	],
	TypeTheoryTheorem[
		"ax-13",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies[Not["setClass"[x] == "setClass"[y]], Implies["setClass"[y] == "setClass"[z], ForAll[{Typed[x, "Set"]}, "setClass"[y] == "setClass"[z]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[n, Not["setClass"[x] == "setClass"[y]]], Typed[e, "setClass"[y] == "setClass"[z]], Typed[w, "Set"]}, e]
	],
	(* substitution, defined as df-sb defines it, and classes *)
	TypeTheoryDefinition[
		"wsb",
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[t, "Set"]},
			ForAll[{Typed[y, "Set"]}, Implies["setClass"[y] == "setClass"[t], ForAll[{Typed[x, "Set"]}, Implies["setClass"[x] == "setClass"[y], \[CurlyPhi][x, t]]]]]
		]
	],
	TypeTheoryTheorem[
		"df-clab",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Equivalent[
				"classElement"["setClass"[x], "classAbstraction"[Function[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]]],
				"wsb"[Function[{Typed[y, "Set"], Typed[x, "Set"]}, \[CurlyPhi][x, y]], x]
			]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"]},
			With[{membership = "classElementSetClass"[x, "classAbstraction"[Function[{Typed[v, "Set"]}, \[CurlyPhi][x, v]]]]},
				"equivalentIntroduction"[
					Function[{Typed[m, "classElement"["setClass"[x], "classAbstraction"[Function[{Typed[v, "Set"]}, \[CurlyPhi][x, v]]]]]},
						Function[{Typed[v, "Set"], Typed[e, "setClass"[v] == "setClass"[x]], Typed[w, "Set"], Typed[f, "setClass"[w] == "setClass"[v]]},
							Construct[
								"equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, \[CurlyPhi][x, s]], x, w,
								"equalitySymmetry"["setClassInjective"[w, x, "equalityTransitivity"[f, e]]],
								membership[[1]][m]
							]
						]
					],
					Function[{Typed[k, "wsb"[Function[{Typed[v, "Set"], Typed[u, "Set"]}, \[CurlyPhi][u, v]], x]]},
						membership[[2]][k[x, "equalityReflexivity"["setClass"[x]], x, "equalityReflexivity"["setClass"[x]]]]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-cleq",
		ForAll[
			{Typed[A, "Class"], Typed[B, "Class"]},
			Implies[
				ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
					Equivalent["setClass"[y] == "setClass"[z], ForAll[{Typed[u, "Set"]}, Equivalent["classElement"["setClass"[u], "setClass"[y]], "classElement"["setClass"[u], "setClass"[z]]]]]
				],
				Implies[
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent["setClass"[t] == "setClass"[t], ForAll[{Typed[v, "Set"]}, Equivalent["classElement"["setClass"[v], "setClass"[t]], "classElement"["setClass"[v], "setClass"[t]]]]]
					],
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent[A == B, ForAll[{Typed[x, "Set"]}, Equivalent["classElement"["setClass"[x], A], "classElement"["setClass"[x], B]]]]
					]
				]
			]
		],
		Function[
			{
				Typed[A, "Class"], Typed[B, "Class"], Typed[h, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["setClass"[y] == "setClass"[z], ForAll[{Typed[u, "Set"]}, Equivalent["classElement"["setClass"[u], "setClass"[y]], "classElement"["setClass"[u], "setClass"[z]]]]]]], Typed[k, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["setClass"[t] == "setClass"[t], ForAll[{Typed[v, "Set"]}, Equivalent["classElement"["setClass"[v], "setClass"[t]], "classElement"["setClass"[v], "setClass"[t]]]]]]],
				Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]
			},
			"equivalentIntroduction"[
				Function[{Typed[e, A == B], Typed[w, "Set"]},
					Construct[
						"equalitySubstitution", "Class", Function[{Typed[C, "Class"]}, Equivalent["classElement"["setClass"[w], A], "classElement"["setClass"[w], C]]], A, B, e,
						"equivalentReflexivity"["classElement"["setClass"[w], A]]
					]
				],
				Function[{Typed[m, ForAll[{Typed[w, "Set"]}, Equivalent["classElement"["setClass"[w], A], "classElement"["setClass"[w], B]]]]},
					"functionExtensionality"[Function[{Typed[w, "Set"]},
						"propositionalExtensionality"["equivalentIntroduction"[
							Function[{Typed[p, A[w]]}, "classElementSetClass"[w, B][[1]][m[w][[1]]["classElementSetClass"[w, A][[2]][p]]]],
							Function[{Typed[p, B[w]]}, "classElementSetClass"[w, A][[1]][m[w][[2]]["classElementSetClass"[w, B][[2]][p]]]]
						]]
					]]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-clel",
		ForAll[
			{Typed[A, "Class"], Typed[B, "Class"]},
			Implies[
				ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
					Equivalent["classElement"["setClass"[y], "setClass"[z]], Exists[{Typed[u, "Set"]}, And["setClass"[u] == "setClass"[y], "classElement"["setClass"[u], "setClass"[z]]]]]
				],
				Implies[
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent["classElement"["setClass"[t], "setClass"[t]], Exists[{Typed[v, "Set"]}, And["setClass"[v] == "setClass"[t], "classElement"["setClass"[v], "setClass"[t]]]]]
					],
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent["classElement"[A, B], Exists[{Typed[x, "Set"]}, And["setClass"[x] == A, "classElement"["setClass"[x], B]]]]
					]
				]
			]
		],
		Function[
			{
				Typed[A, "Class"], Typed[B, "Class"], Typed[h, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["classElement"["setClass"[y], "setClass"[z]], Exists[{Typed[u, "Set"]}, And["setClass"[u] == "setClass"[y], "classElement"["setClass"[u], "setClass"[z]]]]]]], Typed[k, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["classElement"["setClass"[t], "setClass"[t]], Exists[{Typed[v, "Set"]}, And["setClass"[v] == "setClass"[t], "classElement"["setClass"[v], "setClass"[t]]]]]]],
				Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]
			},
			"equivalentIntroduction"[
				Function[{Typed[m, "classElement"[A, B]]},
					"existsElimination"[m, Function[{Typed[a, "Set"], Typed[q, And[A == "setClass"[a], B[a]]]},
						Typed[
							"existsIntroduction"[a, "andIntroduction"["equalitySymmetry"[q[[1]]], "classElementSetClass"[a, B][[2]][q[[2]]]]],
							Exists[{Typed[w, "Set"]}, And["setClass"[w] == A, "classElement"["setClass"[w], B]]]
						]
					]]
				],
				Function[{Typed[m, Exists[{Typed[w, "Set"]}, And["setClass"[w] == A, "classElement"["setClass"[w], B]]]]},
					"existsElimination"[m, Function[{Typed[a, "Set"], Typed[q, And["setClass"[a] == A, "classElement"["setClass"[a], B]]]},
						Typed[
							"existsIntroduction"[a, "andIntroduction"["equalitySymmetry"[q[[1]]], "classElementSetClass"[a, B][[1]][q[[2]]]]],
							"classElement"[A, B]
						]
					]]
				]
			]
		]
	],
	(* the axioms of ZFC, from the model's *)
	setmmTheorem[
		"ax-ext",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies[
			ForAll[{Typed[z, "Set"]}, Equivalent["classElement"["setClass"[z], "setClass"[x]], "classElement"["setClass"[z], "setClass"[y]]]],
			"setClass"[x] == "setClass"[y]
		]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, "extensionality"[x, y]]
	],
	setmmTheorem[
		"ax-rep",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set", "Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Implies[
				ForAll[{Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y, z, w]], "setClass"[z] == "setClass"[y]]]]],
				Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Equivalent[
					"classElement"["setClass"[z], "setClass"[y]],
					Exists[{Typed[w, "Set"]}, And["classElement"["setClass"[w], "setClass"[x]], ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y, z, w]]]]
				]]]
			]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set", "Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			"replacement"[Function[{Typed[v, "Set"], Typed[u, "Set"]}, ForAll[{Typed[s, "Set"]}, \[CurlyPhi][x, s, v, u]]], x]
		]
	],
	setmmTheorem[
		"ax-sep",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[x, "Set"]}, Equivalent[
				"classElement"["setClass"[x], "setClass"[y]],
				And["classElement"["setClass"[x], "setClass"[z]], \[CurlyPhi][x]]
			]]]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]},
			Typed[
				"existsIntroduction"["separationSet"[z, \[CurlyPhi]], "elementOfSeparation"[z, \[CurlyPhi]]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Equivalent[Element[c, s], And[Element[c, z], \[CurlyPhi][c]]]]]
			]
		]
	],
	setmmTheorem[
		"ax-nul",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Exists[{Typed[x, "Set"]}, ForAll[{Typed[y, "Set"]}, Not["classElement"["setClass"[y], "setClass"[x]]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"]},
			Typed["existsIntroduction"["emptySet", "emptySetEmpty"], Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Not[Element[c, s]]]]]
		]
	],
	setmmTheorem[
		"ax-pow",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[
			ForAll[{Typed[w, "Set"]}, Implies["classElement"["setClass"[w], "setClass"[z]], "classElement"["setClass"[w], "setClass"[x]]]],
			"classElement"["setClass"[z], "setClass"[y]]
		]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			Typed[
				"existsIntroduction"["powerSet"[x], Function[{Typed[c, "Set"]}, "elementOfPower"[x, c][[2]]]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Implies[ForAll[{Typed[d, "Set"]}, Implies[Element[d, c], Element[d, x]]], Element[c, s]]]]
			]
		]
	],
	setmmTheorem[
		"ax-pr",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[z, "Set"]}, ForAll[{Typed[w, "Set"]}, Implies[
			Or["setClass"[w] == "setClass"[x], "setClass"[w] == "setClass"[y]],
			"classElement"["setClass"[w], "setClass"[z]]
		]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			Typed[
				"existsIntroduction"["pairSet"[x, y], Function[{Typed[c, "Set"]}, "elementOfPair"[x, y, c][[2]]]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Implies[Or[c == x, c == y], Element[c, s]]]]
			]
		]
	],
	setmmTheorem[
		"ax-un",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[
			Exists[{Typed[w, "Set"]}, And["classElement"["setClass"[z], "setClass"[w]], "classElement"["setClass"[w], "setClass"[x]]]],
			"classElement"["setClass"[z], "setClass"[y]]
		]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			Typed[
				"existsIntroduction"["unionSet"[x], Function[{Typed[c, "Set"], Typed[m, Exists[{Typed[d, "Set"]}, And[Element[c, d], Element[d, x]]]]},
					"elementOfUnion"[x, c][[2]]["existsElimination"[m, Function[{Typed[d, "Set"], Typed[k, And[Element[c, d], Element[d, x]]]},
						Typed["existsIntroduction"[d, "andIntroduction"[k[[2]], k[[1]]]], Exists[{Typed[e, "Set"]}, And[Element[e, x], Element[c, e]]]]
					]]]
				]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Implies[Exists[{Typed[d, "Set"]}, And[Element[c, d], Element[d, x]]], Element[c, s]]]]
			]
		]
	],
	setmmTheorem[
		"ax-reg",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies[
			Exists[{Typed[y, "Set"]}, "classElement"["setClass"[y], "setClass"[x]]],
			Exists[{Typed[y, "Set"]}, And["classElement"["setClass"[y], "setClass"[x]], ForAll[{Typed[z, "Set"]}, Implies["classElement"["setClass"[z], "setClass"[y]], Not["classElement"["setClass"[z], "setClass"[x]]]]]]]
		]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, "regularity"[x]]
	],
	setmmTheorem[
		"ax-inf",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, And[
			"classElement"["setClass"[x], "setClass"[y]],
			ForAll[{Typed[z, "Set"]}, Implies["classElement"["setClass"[z], "setClass"[y]], Exists[{Typed[w, "Set"]}, And["classElement"["setClass"[z], "setClass"[w]], "classElement"["setClass"[w], "setClass"[y]]]]]]
		]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, "infinity"[x]]
	],
	setmmTheorem[
		"ax-ac",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, ForAll[{Typed[w, "Set"]}, Implies[
			And["classElement"["setClass"[z], "setClass"[w]], "classElement"["setClass"[w], "setClass"[x]]],
			Exists[{Typed[v, "Set"]}, ForAll[{Typed[u, "Set"]}, Equivalent[
				Exists[{Typed[t, "Set"]}, And[And["classElement"["setClass"[u], "setClass"[w]], "classElement"["setClass"[w], "setClass"[t]]], And["classElement"["setClass"[u], "setClass"[t]], "classElement"["setClass"[t], "setClass"[y]]]]],
				"setClass"[u] == "setClass"[v]
			]]]
		]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, "choiceAxiom"[x]]
	]
}
