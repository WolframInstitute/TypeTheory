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
