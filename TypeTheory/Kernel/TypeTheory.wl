(* ::Package:: *)

(* ::Section::Closed:: *)
(*PackageInitialize*)


(* WolframInstitute`TypeTheory`: a proof engine for the Calculus of Inductive Constructions, in pure
   Wolfram Language. FinalEvaluations.wl runs last because it declares the prelude, which needs every
   other file's definitions. *)

PackageInitialize["WolframInstitute`TypeTheory`",
	<|
		"HiddenImports" -> {},
		"LoadFirstFiles" -> {},
		"LoadLastFiles" -> {"FinalEvaluations.wl"},
		"IgnoreFiles" -> {}
	|>
]

(* When another loaded package defines a name TypeTheory exports and both contexts are on the context path, the
   loader sets up its shadowing message by parsing "General::shdw = ..." in TypeTheory's context with an empty
   context path, which creates a symbol General there; it is removed, so that General is System's. *)
Quiet[Remove["WolframInstitute`TypeTheory`General"]]
