---
Template: TechNote
Name: Paradoxes
Title: Paradoxes
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/Paradoxes
Keywords: [paradox, inconsistency, unsound, False, Girard, Hurkens, Curry, Russell, positivity, large elimination, proof irrelevance, Type in Type, axiom, registration, trusted base]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation, TypeTheoryIntroduction, HomotopyTypeTheory, ThePrelude]
---

An environment is consistent when no term of it has the type `False`. The kernel keeps the prelude consistent by refusing every declaration that would let a proof of `False` through: a type defined by its own negation, an elimination of a proof into data, a definition that refers to itself, a universe that contains itself. What it does not refuse is what it is told to trust: an axiom, a registration of an operation on natural numbers, a rewrite rule. Each section below shows a declaration the kernel refuses, then the same thing assumed, the proof of `False` it gives, and what [TypeTheoryAxiomClosure]() finds that proof rests on.

## A Type Defined by Its Own Negation

A type whose constructor takes a function out of the type itself would contain its own negation, as the set of Russell's paradox contains itself exactly when it does not. The kernel refuses it, as the type does not occur strictly positively:

```wl
TypeTheoryEnvironment[{TypeTheoryInductiveType[Bad, TypeUniverse[0], {"badIntroduction" -> ((Bad -> False) -> Bad)}]}]
```

<!-- => Failure["NonPositiveOccurrence", ...] -->

Assumed instead, by axioms: a proposition `Bad`, a way into it from its negation, and a way out of it into its negation. From them `b ↦ "badElimination"[b, b]` is a proof that `Bad` is false, which goes into `Bad`, and the one applied to the other is a proof of `False`, the argument of Curry's paradox:

```wl
curry = TypeTheoryEnvironment[{
    TypeTheoryAxiom[Bad, TypeUniverse[0]],
    TypeTheoryAxiom["badIntroduction", (Bad -> False) -> Bad],
    TypeTheoryAxiom["badElimination", Bad -> Bad -> False],
    TypeTheoryTheorem[CurryParadox, False, (Typed[b, Bad] |-> "badElimination"[b, b])["badIntroduction"[Typed[b, Bad] |-> "badElimination"[b, b]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The proof rests on the three axioms:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[CurryParadox, curry]]
```

<!-- => <|Bad -> "Signature", "badElimination" -> "Proposition", "badIntroduction" -> "Proposition"|> -->

Had the way out computed on the way in, as the recursor of a real inductive type does, the proof of `False` would have no normal form: it reduces to itself. Positivity is what keeps every term of the kernel's own types normalizing.

## Choosing Between Two Proofs

Any two proofs of a proposition are equal by computation, which is proof irrelevance. So a function from proofs to data can never tell two proofs apart, and the kernel lets the recursor of a proposition with more than one constructor, as [Or](), eliminate only into Prop. The two proofs of `True || True`, one by each side, are equal:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed["orIntroductionLeft"["trueIntroduction"], True || True]], TypeTheoryTerm[Typed["orIntroductionRight"["trueIntroduction"], True || True]]]
```

<!-- => True -->

and a recursor that would choose a Boolean by the side is refused:

```wl
TypeTheoryType[InductiveRecursor[Or][Typed[t, True || True] |-> Booleans, Typed[h, True] |-> "true", Typed[h, True] |-> "false", Typed["orIntroductionLeft"["trueIntroduction"], True || True]]]
```

<!-- => Failure["TypeMismatch", ...] -->

Assumed instead: a choice of a Boolean from a proof of a disjunction, `"true"` from the left side and `"false"` from the right. The two proofs of `True || True` are one, so the choice gives `"true"` and `"false"` for the same proof, and `"true" == "false"` is a proof of `False`:

```wl
choice = TypeTheoryEnvironment[{
    TypeTheoryAxiom["orChoice", ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, (a || b) -> Booleans]],
    TypeTheoryAxiom["chooseLeft", ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, a]}, "orChoice"[Typed["orIntroductionLeft"[h], a || b]] == "true"]],
    TypeTheoryAxiom["chooseRight", ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, b]}, "orChoice"[Typed["orIntroductionRight"[h], a || b]] == "false"]],
    TypeTheoryTheorem[ChoiceParadox, False, "trueNotFalse"["equalityTransitivity"[
        "equalitySymmetry"[Typed["chooseLeft"["trueIntroduction"], "orChoice"[Typed["orIntroductionLeft"["trueIntroduction"], True || True]] == "true"]],
        Typed["chooseRight"["trueIntroduction"], "orChoice"[Typed["orIntroductionRight"["trueIntroduction"], True || True]] == "false"]
    ]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The transitivity joins the two equations only because their middle terms, the choices from the two proofs, are equal by proof irrelevance. The proof rests on the choice and its two equations:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[ChoiceParadox, choice]]
```

<!-- => <|"orChoice" -> "Signature", "chooseLeft" -> "Proposition", "chooseRight" -> "Proposition"|> -->

## A Definition That Refers to Itself

A definition may not use its own name, so no definition is an equation without a solution. The name `Loop` names nothing in its own value:

```wl
TypeTheoryEnvironment[{TypeTheoryDefinition[Loop, Typed[n, Naturals] |-> Loop[n] + 1]}]
```

<!-- => Failure["ElaborationFailed", ...] -->

No natural number is its own successor:

```wl
noFixedSuccessor = TypeTheoryProof[ForAll[{x}, Implies[x == x + 1, False]], {"Introduce"[x, h], "LinearArithmetic"}]
```

<!-- => Proof complete -->

So the equation, assumed instead, is a proof of `False`:

```wl
loops = TypeTheoryEnvironment[{
    TypeTheoryAxiom[Loop, Naturals -> Naturals],
    TypeTheoryAxiom["loopEquation", ForAll[{n}, Loop[n] == Loop[n] + 1]],
    TypeTheoryTheorem[NoFixedSuccessor, ForAll[{x}, Implies[x == x + 1, False]], noFixedSuccessor],
    TypeTheoryTheorem[LoopParadox, False, NoFixedSuccessor[Loop[0], "loopEquation"[0]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[LoopParadox, loops]]
```

<!-- => <|Loop -> "Signature", "loopEquation" -> "Proposition"|> -->

Recursion is by a recursor, [InductiveRecursor](), which takes one step for each constructor and so always ends.

## A Universe That Contains Itself

Each universe is in the next one, never in itself:

```wl
TypeTheoryType[Typed[TypeUniverse[1], TypeUniverse[1]]]
```

<!-- => Failure["TypeMismatch", ...] -->

Girard showed that a universe containing itself is inconsistent, and Hurkens ("A simplification of Girard's paradox", 1995) gave a short proof, which this section follows, as Mathlib's `Counterexamples.girard` does after Watkins. A universe that contains itself is assumed as a product over Type that lands in Type again: a type `"pi"[A]` of the functions that take each type `x` to an element of `A[x]`, with its abstraction `"lam"`, its application `"app"` and its computation `"beta"`:

```wl
selfContained = TypeTheoryEnvironment[{
    TypeTheoryAxiom["pi", (TypeUniverse[1] -> TypeUniverse[1]) -> TypeUniverse[1]],
    TypeTheoryAxiom["lam", ForAll[{TypedImplicit[A, TypeUniverse[1] -> TypeUniverse[1]]}, ForAll[{Typed[x, TypeUniverse[1]]}, A[x]] -> "pi"[A]]],
    TypeTheoryAxiom["app", ForAll[{TypedImplicit[A, TypeUniverse[1] -> TypeUniverse[1]]}, "pi"[A] -> ForAll[{Typed[x, TypeUniverse[1]]}, A[x]]]],
    TypeTheoryAxiom["beta", ForAll[{TypedImplicit[A, TypeUniverse[1] -> TypeUniverse[1]], Typed[f, ForAll[{Typed[x, TypeUniverse[1]]}, A[x]]], Typed[x, TypeUniverse[1]]}, "app"["lam"[f], x] == f[x]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The paradox needs a type `U` into which every set of sets of `U` packs and out of which it unpacks again: `"girardTau"` packs and `"girardSigma"` unpacks. In a universe that does not contain itself no such type exists, as the sets of sets of `U` are in a larger universe than `U`:

```wl
packing = TypeTheoryEnvironment[selfContained, {
    TypeTheoryDefinition["girardF", Typed[X, TypeUniverse[1]] |-> ((((X -> TypeUniverse[0]) -> TypeUniverse[0]) -> X) -> ((X -> TypeUniverse[0]) -> TypeUniverse[0]))],
    TypeTheoryDefinition["girardU", Typed["pi"["girardF"], TypeUniverse[1]]],
    TypeTheoryDefinition["girardG", Typed[
        Function[{Typed[T, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]], Typed[X, TypeUniverse[1]], Typed[f, ((X -> TypeUniverse[0]) -> TypeUniverse[0]) -> X], Typed[q, X -> TypeUniverse[0]]},
            T[Typed[x, "girardU"] |-> q[f["app"[x, X, f]]]]
        ],
        (("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]) -> ForAll[{Typed[X, TypeUniverse[1]]}, "girardF"[X]]
    ]],
    TypeTheoryDefinition["girardTau", Typed[Typed[T, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]] |-> "lam"["girardG"[T]], (("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]) -> "girardU"]],
    TypeTheoryDefinition["girardSigma", Typed[Typed[S, "girardU"] |-> "app"[S, "girardU", "girardTau"], "girardU" -> (("girardU" -> TypeUniverse[0]) -> TypeUniverse[0])]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 266 constants -->

By `"beta"`, unpacking what packed `S` holds of a set `s` exactly when `S` holds of the set of the `x` whose unpacking repacks into `s`, in both directions:

```wl
unpacking = TypeTheoryEnvironment[packing, {
    TypeTheoryTheorem["girardSigmaTau",
        ForAll[{Typed[s, "girardU" -> TypeUniverse[0]], Typed[S, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]]}, "girardSigma"["girardTau"[S]][s] == S[Typed[x, "girardU"] |-> s["girardTau"["girardSigma"[x]]]]],
        Function[{Typed[s, "girardU" -> TypeUniverse[0]], Typed[S, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]]},
            "equalityCongruence"[Typed[g, "girardF"["girardU"]] |-> g["girardTau", s], "beta"["girardG"[S], "girardU"]]
        ]
    ],
    TypeTheoryTheorem["girardSigmaTauForward",
        ForAll[{Typed[s, "girardU" -> TypeUniverse[0]], Typed[S, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]]}, Implies["girardSigma"["girardTau"[S]][s], S[Typed[x, "girardU"] |-> s["girardTau"["girardSigma"[x]]]]]],
        Function[{Typed[s, "girardU" -> TypeUniverse[0]], Typed[S, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]], Typed[h, "girardSigma"["girardTau"[S]][s]]},
            Construct["equalitySubstitution", TypeUniverse[0], Typed[r, TypeUniverse[0]] |-> r, "girardSigma"["girardTau"[S]][s], S[Typed[x, "girardU"] |-> s["girardTau"["girardSigma"[x]]]], "girardSigmaTau"[s, S], h]
        ]
    ],
    TypeTheoryTheorem["girardSigmaTauBackward",
        ForAll[{Typed[s, "girardU" -> TypeUniverse[0]], Typed[S, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]]}, Implies[S[Typed[x, "girardU"] |-> s["girardTau"["girardSigma"[x]]]], "girardSigma"["girardTau"[S]][s]]],
        Function[{Typed[s, "girardU" -> TypeUniverse[0]], Typed[S, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]], Typed[h, S[Typed[x, "girardU"] |-> s["girardTau"["girardSigma"[x]]]]]},
            Construct["equalitySubstitution", TypeUniverse[0], Typed[r, TypeUniverse[0]] |-> r, S[Typed[x, "girardU"] |-> s["girardTau"["girardSigma"[x]]]], "girardSigma"["girardTau"[S]][s], "equalitySymmetry"["girardSigmaTau"[s, S]], h]
        ]
    ]
}]
```

<!-- => TypeTheoryEnvironment summary box: 269 constants -->

`"girardOmega"` is the set of the sets `q` that hold of every `x` whose unpacking contains `q`, and `"girardDelta"` says of a set of sets that every set it contains holds of its packing. `"girardOmega"` has that property, and the set of the `y` whose unpacking lacks it then gives the contradiction, as the collection of all well-founded sets would be one and not one:

```wl
hurkens = TypeTheoryEnvironment[unpacking, {
    TypeTheoryDefinition["girardOmega", Typed[Typed[q, "girardU" -> TypeUniverse[0]] |-> ForAll[{Typed[x, "girardU"]}, Implies["girardSigma"[x][q], q[x]]], ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]]],
    TypeTheoryDefinition["girardDelta", Typed[Typed[S, ("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]] |-> ForAll[{Typed[q, "girardU" -> TypeUniverse[0]]}, Implies[S[q], q["girardTau"[S]]]], (("girardU" -> TypeUniverse[0]) -> TypeUniverse[0]) -> TypeUniverse[0]]],
    TypeTheoryTheorem["girardDeltaOmega", "girardDelta"["girardOmega"],
        Function[{Typed[q, "girardU" -> TypeUniverse[0]], Typed[d, "girardOmega"[q]]},
            d["girardTau"["girardOmega"], "girardSigmaTauBackward"[q, "girardOmega",
                Function[{Typed[x, "girardU"], Typed[h, "girardSigma"[x][Typed[y, "girardU"] |-> q["girardTau"["girardSigma"[y]]]]]},
                    d["girardTau"["girardSigma"[x]], "girardSigmaTauBackward"[q, "girardSigma"[x], h]]
                ]
            ]]
        ]
    ],
    TypeTheoryTheorem[GirardParadox, False,
        "girardDeltaOmega"[
            Typed[y, "girardU"] |-> Not["girardDelta"["girardSigma"[y]]],
            Function[{Typed[x, "girardU"], Typed[e, "girardSigma"[x][Typed[y, "girardU"] |-> Not["girardDelta"["girardSigma"[y]]]]], Typed[f, "girardDelta"["girardSigma"[x]]]},
                f[Typed[y, "girardU"] |-> Not["girardDelta"["girardSigma"[y]]], e,
                    Function[{Typed[r, "girardU" -> TypeUniverse[0]], Typed[h, "girardSigma"["girardTau"["girardSigma"[x]]][r]]},
                        f[Typed[y, "girardU"] |-> r["girardTau"["girardSigma"[y]]], "girardSigmaTauForward"[r, "girardSigma"[x], h]]
                    ]
                ]
            ],
            Function[{Typed[r, "girardU" -> TypeUniverse[0]], Typed[d, "girardSigma"["girardTau"["girardOmega"]][r]]},
                "girardDeltaOmega"[Typed[y, "girardU"] |-> r["girardTau"["girardSigma"[y]]], "girardSigmaTauForward"[r, "girardOmega", d]]
            ]
        ]
    ]
}]
```

<!-- => TypeTheoryEnvironment summary box: 273 constants -->

The proof of `False` rests on nothing but the four axioms that put a product over Type into Type:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[GirardParadox, hurkens]]
```

<!-- => <|"app" -> "Signature", "pi" -> "Signature", "lam" -> "Signature", "beta" -> "Proposition"|> -->

Prop may quantify over itself, as the Church booleans on the page of [TypeUniverse]() do, because its proofs are all equal: a set of sets of propositions packed into a proposition cannot be unpacked again, which is what the paradox needs. That is also why a proposition may not eliminate into data, as the section *Choosing Between Two Proofs* shows.

## A Registration That Lies

A registration of an operation on natural numbers is trusted, as an axiom is: the kernel computes the operation on literals by the Wolfram Language and trusts that its definition computes the same. Here a definition that gives its first argument is registered as the greatest common divisor:

```wl
lying = TypeTheoryEnvironment[{
    TypeTheoryDefinition[FirstNumber, {Typed[m, Naturals], Typed[n, Naturals]} |-> m],
    TypeTheoryNaturalNumbers[Naturals, "zero", "successor", <|"GCD" -> FirstNumber|>]
}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

On literals the kernel computes the greatest common divisor, 1, and on a variable it unfolds the definition, which gives the variable:

```wl
{WeakHeadNormalForm[TypeTheoryTerm[FirstNumber[2, 3], lying]], NormalForm[TypeTheoryTerm[Typed[x, Naturals] |-> FirstNumber[x, 3], lying]]}
```

<!-- => {1, (x ∶ ℕ) ↦ x} -->

So `FirstNumber[2, 3]` is 1 by computation and 2 by the definition, and `1 == 2` is a proof of `False`:

```wl
lied = TypeTheoryEnvironment[lying, {
    TypeTheoryTheorem[FirstIsIdentity, ForAll[{Typed[x, Naturals]}, FirstNumber[x, 3] == x], Typed[x, Naturals] |-> "equalityReflexivity"[x]],
    TypeTheoryTheorem[FirstIsOne, FirstNumber[2, 3] == 1, "equalityReflexivity"[1]],
    TypeTheoryTheorem[RegistrationParadox, False, "successorNotZero"[0]["equalitySymmetry"["successorInjectivity"["equalityTransitivity"["equalitySymmetry"[FirstIsOne], FirstIsIdentity[2]]]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The proof rests on no axiom, but on the registration, which [TypeTheoryAxiomClosure]() names as one:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[RegistrationParadox, lied]]
```

<!-- => <|FirstNumber -> "Registration"|> -->

The kernel checks an addition, and the other operations with defining equations, against those equations when they are registered, and refuses one that fails them. An operation without them, as the greatest common divisor, it trusts, and the closure names its registration wherever a proof rests on it, unless it is the prelude's own.

## Rewrite Rules and Univalence

A rewrite rule is trusted as an axiom is, and two rules that disagree prove two constructors equal, as the section *Rewrite Rules Are Trusted* of the tutorial *Rules and Computation* shows. Univalence contradicts proof irrelevance, as the tutorial *Homotopy Type Theory* shows, which is why its environment has no Prop.

## Summary

- The kernel refuses a type that occurs negatively in its own constructors, the elimination into data of a proposition with two constructors, a definition that uses its own name, and a universe in itself.
- Each of these, assumed by axioms, proves `False`: Curry's paradox, the choice between two equal proofs, an equation without a solution, and Girard's paradox in Hurkens's form.
- [TypeTheoryAxiomClosure]() names every trusted assumption a proof rests on: the axioms, and the registrations of operations the kernel does not check.
