---
Template: TechNote
Name: CubicalTypeTheory
Title: Cubical Type Theory
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/CubicalTypeTheory
Keywords: [cubical type theory, interval, path, univalence, Glue type, transport, composition, function extensionality, homotopy type theory, CCHM]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory, RulesAndComputation]
---

In cubical type theory a path is a function from an interval, and univalence, an axiom in homotopy type theory, is a theorem that computes. TypeTheory's cubical rules follow the theory of Cohen, Coquand, Huber and Mörtberg: an interval with the operations of a De Morgan algebra, paths over lines of types, transport and composition, and Glue types. <code>[TypeTheoryEnvironment]()["Cubical"]</code> has them with a small library, and no axiom.

## The Cubical Environment

The environment, built and checked the first time it is asked for:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its rules are cubical, Martin-Löf type theory with the primitives, and have no Prop, whose proof irrelevance would contradict univalence:

```wl
Information[cubical, "Rules"]["Name"]
```

<!-- => "CubicalTypeTheory" -->

It has no axioms:

```wl
Information[cubical, "Axioms"]
```

<!-- => {} -->

## Paths Are Functions of the Interval

A path from `x` to `y` is a function of an element of the interval, `Interval`, whose values at 0 and 1 are `x` and `y`. A constant function is a path:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[i, Interval]}, "true"], cubical]]
```

<!-- => true ≡ true -->

Its type is a path type, `Path[A, x, y]`, between its values at the endpoints. A path that is not a function computes to an endpoint of its type there:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p[0]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, x], cubical]
]
```

<!-- => True -->

The interval is a De Morgan algebra: [Min](), [Max]() and `1 - i` are its meet, join and reversal, and two of its elements are equal when their normal forms are. So `Min[i, Max[i, j]]` is `i`:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[Min[i, Max[i, j]]]], cubical],
    TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[i]], cubical]
]
```

<!-- => True -->

The path reversed is the function of `i` that is `p[1 - i]`, [PathSymmetry]():

```wl
cubical[PathSymmetry]
```

<!-- => definition PathSymmetry : ∀_{A∶Type u} ∀_{x∶A} ∀_{y∶A} x≡y→y≡x := {A∶Type u} {x∶A} {y∶A} (p∶x≡y) (i∶Interval)↦p[~i] -->

Function extensionality is a term: a path between functions is a function of the interval into functions, [PathFunctionExtensionality]():

```wl
cubical[PathFunctionExtensionality]
```

<!-- => definition PathFunctionExtensionality : ∀_{A∶Type u} ∀_{B∶Type v} ∀_{f∶A→B} ∀_{g∶A→B} (∀_x∶A f[x]≡g[x])→f≡g := {A∶Type u} {B∶Type v} {f∶A→B} {g∶A→B} (h∶∀_x∶A f[x]≡g[x]) (i∶Interval) (x∶A)↦h[x,i] -->

At 0 it is the first function, by computation. The path from `"not"["not"[b]]` to `b` for every Boolean `b`, [NegationInvolution](), gives a path between functions whose start is the double negation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[PathFunctionExtensionality[Function[{Typed[b, Booleans]}, NegationInvolution[b]]][0], cubical],
    TypeTheoryTerm[Function[{Typed[b, Booleans]}, "not"["not"[b]]], cubical]
]
```

<!-- => True -->

## Transport and Composition

[CubicalTransport]() carries an element along a line of types, a function of the interval into a universe. It computes by the type: here it carries `"not"` along the constant line of functions of Booleans, and applies it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Function[{i}, TypeSpecifier[{Booleans} -> Booleans]], 0, "not"]["true"], cubical]]
```

<!-- => false -->

Its second argument is a face where the line must be constant, and where the transport is the element itself. A path of types need not be constant where `1` holds, everywhere:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, Path[TypeUniverse[1], Booleans, Booleans]]}, CubicalTransport[p, 1, "true"]], cubical]]
```

<!-- => Failure["TransportNotConstant", ...] -->

Path induction transports along the path's connection, the function of `i` and `j` that is `p[Min[i, j]]`, [PathInduction]():

```wl
cubical[PathInduction]
```

<!-- => definition PathInduction : ∀_{A∶Type u} ∀_{x∶A} ∀_P∶∀_y∶A x≡y→Type v P[x,(i∶Interval)↦x]→∀_{y∶A} ∀_p∶x≡y P[y,p] := {A∶Type u} {x∶A} (P∶∀_y∶A x≡y→Type v) (d∶P[x,(i∶Interval)↦x]) {y∶A} (p∶x≡y)↦CubicalTransport[(i∶Interval)↦P[p[i],(j∶Interval)↦p[i∧j]],0,d] -->

[CubicalComposition]() fills an open box: given its base and its sides over faces, it gives the lid. The concatenation of two paths composes along the second, [PathTransitivity]():

```wl
cubical[PathTransitivity]
```

<!-- => definition PathTransitivity : ∀_{A∶Type u} ∀_{x∶A} ∀_{y∶A} ∀_{z∶A} x≡y→y≡z→x≡z := {A∶Type u} {x∶A} {y∶A} {z∶A} (p∶x≡y) (q∶y≡z) (i∶Interval)↦CubicalComposition[A,(j∶Interval)↦{i == 0->x,i == 1->q[j]},p[i]] -->

A composition is its side at 1 where a face holds:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalComposition[Booleans, Function[{j}, {1 -> "true"}], "true"], cubical]]
```

<!-- => true -->

## Glue Types and Univalence

An equivalence is a function whose fibers are contractible, [Equivalence]():

```wl
cubical[Equivalence]
```

<!-- => definition Equivalence : Type u → Type u → Type u := (A ∶ Type u) (B ∶ Type u) ↦ DependentSum[A → B, (f ∶ A → B) ↦ IsEquivalence[f]] -->

A [GlueType]() over `B` is, where each face of its system holds, a type glued to `B` along an equivalence. Univalence, [EquivalenceToPath](), is the line of Glue types over `B` that is `A` at 0, glued along the equivalence `e`, and `B` at 1, glued along the identity:

```wl
cubical[EquivalenceToPath]
```

<!-- => definition EquivalenceToPath : ∀_{A∶Type u} ∀_{B∶Type u} Equivalence[A,B]→A≡B := {A∶Type u} {B∶Type u} (e∶Equivalence[A,B]) (i∶Interval)↦GlueType[B,{i == 0->DependentPair[A,e],i == 1->DependentPair[B,IdentityEquivalence[B]]}] -->

Transport along it applies the equivalence. Negation is an equivalence of the Booleans, [NegationEquivalence](), made from the isomorphism it is with itself by [IsomorphismEquivalence]():

```wl
transported = TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "true"], cubical]
```

<!-- => CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, true] -->

It computes to `"false"`:

```wl
WeakHeadNormalForm[transported]
```

<!-- => false -->

In the HoTT environment univalence is an axiom, so the same transport stops at it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[Function[{Typed[X, TypeUniverse[1]]}, X], EquivalenceToEquality[NegationEquivalence], "true"], TypeTheoryEnvironment["HomotopyTypeTheory"]]]
```

<!-- => Equal_rec[(z∶Type) (q∶𝔹 == z)↦((X∶Type)↦X)[z],true,EquivalenceToEquality[NegationEquivalence]] -->

## What Has No Rule Here

A transport or a composition that no rule covers does not compute, which loses canonicity and never consistency: every rule the kernel has is one of cubical type theory. Composition in a universe has no rule, so transport along a concatenation of two paths of univalence stops. Transport in a Glue type computes where its own face is 0 and no face of the Glue type holds all along the line, as on the paths of univalence. Higher inductive types, such as the circle, are not primitives, and the rules have no Prop.
