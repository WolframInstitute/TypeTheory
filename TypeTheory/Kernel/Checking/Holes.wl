(* ::Package:: *)

(*
Holes: theorems whose proofs are not finished yet, as Lean's sorry.

TypeTheoryHole[] and TypeTheoryHole[annotation] stand in the proof of a declared theorem for a term of the type
expected there, and TypeTheoryTactic["Hole"] or TypeTheoryTactic["Hole", annotation] closes a goal of a proof with
one. A hole is closed over the variables in scope where it stands: elaboration lifts it out of each binder it is
under, as any metavariable, and what is left at the top is one metavariable of the type Π (variables in scope).
goal, applied to those variables.

A theorem whose proof has holes is declared after a constant of the kind "Hole" for each of them,
TypeTheoryHole[theorem, k] for the k-th in the order its proof term holds them. A hole's record keeps its type,
the theorem's universe parameters, its annotation and the theorem:

	<|"Kind" -> "Hole", "Type" -> type, "UniverseParameters" -> {...}, "Annotation" -> annotation, "Theorem" -> HoldComplete[theorem]|>

The kernel checks the theorem with its holes as it would with axioms in their place, so a hole is never taken for
a proof: TypeTheoryAxiomClosure leaves holes out of the axioms, and Information[term, "Holes"] gives the holes a
term rests on, those of the theorems it uses included. TypeTheoryCheck replays a hole as it replays an axiom, and
a theorem's proof reads back with TypeTheoryHole[annotation] where its holes stand, so Normal gives the one
declaration that declares the theorem and its holes again.

An annotation is stored as given: a string is short for <|"Citation" -> string|>, an association, such as
<|"Citation" -> refs, "Mathlib" -> name|> or <|"Evaluation" -> HoldForm[expr], "Value" -> value|>, is kept as it
is, and a hole written with none has None.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryHole]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[$elaboratedHoles]
PackageScoped[holeAnnotation]
PackageScoped[declareWithHoles]
PackageScoped[declareHole]
PackageScoped[holeNameQ]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryHole::usage = "TypeTheoryHole[] stands in the proof of a declared theorem for a term of the type expected there, a proof left to give, as Lean's sorry.\n\
TypeTheoryHole[annotation] carries annotation, a citation or the evidence of a computation, which the hole's record keeps.\n\
TypeTheoryHole[theorem, k] is the k-th hole of the proof of theorem, a constant of the environment that declares theorem."
$elaboratedHoles::usage = "$elaboratedHoles is the list of the holes elaboration closed while a declaration's proof was elaborated, each \
<|\"Id\" -> id, \"Type\" -> type, \"Annotation\" -> annotation|>, or None outside a declaration."
holeAnnotation::usage = "holeAnnotation[{annotation}] gives the annotation a hole is written with: a string as <|\"Citation\" -> string|>, \
anything else as it is, and None for no annotation."
declareWithHoles::usage = "declareWithHoles[environment, HoldComplete[name], universeParameters, term, holes, declare] declares the holes of term, \
each a constant of the kind \"Hole\", then gives declare[extended, value], value being term with the constants in place of its holes."
declareHole::usage = "declareHole[environment, HoldComplete[name], universeParameters, type, annotation, HoldComplete[theorem]] gives environment \
with the hole name of the proof of theorem, after checking that its type is a type."
holeNameQ::usage = "holeNameQ[HoldComplete[name]] gives True if name is the name of a hole, TypeTheoryHole[theorem, k]."


(* ::Section:: *)
(*Function Definitions*)


$elaboratedHoles = None

holeAnnotation[{}] := None
holeAnnotation[{citation_String}] := <|"Citation" -> citation|>
holeAnnotation[{annotation_}] := annotation

holeNameQ[HoldComplete[TypeTheoryHole[_Symbol | _String, _Integer?Positive]]] := True
holeNameQ[_] := False

(* the holes in the order term holds them, each the constant TypeTheoryHole[theorem, k] at the declaration's universe
   parameters, declared before declare is given term with the constants in place *)
declareWithHoles[environment_, name_HoldComplete, universeParameters_List, term_, holes_List, declare_] := Block[
	{
		holeOrder = Select[DeleteDuplicates[Cases[term, metavariable[id_] :> id, {0, Infinity}, Heads -> True]], Function[id, MemberQ[holes[[All, "Id"]], id]]],
		holeEntries = Association[Function[hole, hole["Id"] -> hole] /@ holes],
		holeNames, holeEnvironment
	},
	holeNames = AssociationThread[holeOrder, holeName[name, #]& /@ Range[Length[holeOrder]]];
	holeEnvironment = Fold[
		Function[{partial, id}, declareHole[partial, holeNames[id], universeParameters, holeEntries[id]["Type"], holeEntries[id]["Annotation"], name]],
		environment,
		holeOrder
	];
	declare[holeEnvironment, ReplaceAll[term, metavariable[id_] /; KeyExistsQ[holeNames, id] :> With[
		{reference = constantReference[holeNames[id], levelParameter /@ universeParameters]},
		reference /; True
	]]]
]

holeName[HoldComplete[theorem_], k_Integer] := HoldComplete[TypeTheoryHole[theorem, k]]

declareHole[environment_, name_HoldComplete, universeParameters_List, type_, annotation_, theorem_HoldComplete] := withCheckedTerms[
	checkUniverseParameters[name, universeParameters, {type}];
	If[! $deferKernelChecks, sortLevel[environment, <||>, type]];
	addConstantRecords[environment, <|name -> <|
		"Kind" -> "Hole",
		"Type" -> type,
		"UniverseParameters" -> universeParameters,
		"Annotation" -> annotation,
		"Theorem" -> theorem
	|>|>]
]
