(* ::Package:: *)

(* Runs after every other file: the empty environment, and the prelude, built and checked on loading.
   Both are kept for the session, so their stores are not reported to any cleanup. *)

$emptyEnvironment = withoutStoreTracking[emptyEnvironment[]]

$preludeEnvironment = withoutStoreTracking[TypeTheoryEnvironment[$emptyEnvironment, $preludeDeclarations]]
