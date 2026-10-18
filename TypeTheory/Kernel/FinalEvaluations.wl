(* ::Package:: *)

(* Runs after every other file: the empty environment, the constructive environment and the prelude, which
   extends it with the classical declarations, built and checked on loading.
   All three are kept for the session, so their stores are not reported to any cleanup. *)

$emptyEnvironment = withoutStoreTracking[emptyEnvironment[]]

$constructiveEnvironment = withoutStoreTracking[TypeTheoryEnvironment[$emptyEnvironment, $constructiveDeclarations]]

$preludeEnvironment = withoutStoreTracking[TypeTheoryEnvironment[$constructiveEnvironment, $classicalDeclarations]]
