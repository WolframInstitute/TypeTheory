(* ::Package:: *)

(* Runs after every other file: the empty environment, the constructive environment and the prelude, which
   extends it with the classical declarations, read from the paclet's saved files when this kernel wrote them,
   and otherwise built and checked on loading (SavedEnvironments.wl).
   All three are kept for the session, so their stores are not reported to any cleanup. *)

$emptyEnvironment = withoutStoreTracking[emptyEnvironment[]]

$constructiveEnvironment = withoutStoreTracking[libraryEnvironment["Constructive", $emptyEnvironment, TypeTheoryEnvironment[$emptyEnvironment, $constructiveDeclarations]]]

$preludeEnvironment = withoutStoreTracking[libraryEnvironment["Prelude", $constructiveEnvironment, TypeTheoryEnvironment[$constructiveEnvironment, $classicalDeclarations]]]

(* the default environment, until SetTypeTheoryEnvironment sets another *)
$TypeTheoryEnvironment = $preludeEnvironment
