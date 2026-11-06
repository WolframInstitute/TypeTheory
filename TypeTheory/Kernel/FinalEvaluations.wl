(* ::Package:: *)

(* Runs after every other file: the empty environment, the constructive environment and the prelude, which
   extends it with the classical declarations and the Wolfram Language's expressions, strings and matches
   (WolframLanguage.wl), read from the paclet's saved files when this kernel wrote them, and otherwise built and
   checked on loading (SavedEnvironments.wl).
   All three are kept for the session, so their stores are not reported to any cleanup. *)

$emptyEnvironment = withoutStoreTracking[emptyEnvironment[]]

$constructiveEnvironment = withoutStoreTracking[libraryEnvironment["Constructive", $emptyEnvironment, TypeTheoryEnvironment[$emptyEnvironment, $constructiveDeclarations]]]

$preludeEnvironment = withoutStoreTracking[libraryEnvironment["Prelude", $constructiveEnvironment,
	TypeTheoryEnvironment[$constructiveEnvironment, Join[$classicalDeclarations, $wolframLanguageDeclarations]]
]]

(* the default environment, until SetTypeTheoryEnvironment sets another *)
$TypeTheoryEnvironment = $preludeEnvironment

(* in a notebook, the front end completes the names of the library environments and of the rules, as it completes the
   arguments of a built-in *)
If[TrueQ[$Notebooks],
	Scan[
		Function[completion, Quiet[FrontEndExecute[FrontEnd`Value[FEPrivate`AddSpecialArgCompletion[completion]]]]],
		{
			"TypeTheoryEnvironment" -> {$environmentNames},
			"SetTypeTheoryEnvironment" -> {$environmentNames},
			"TypeTheoryRules" -> {Keys[$namedRules]}
		}
	]
]
