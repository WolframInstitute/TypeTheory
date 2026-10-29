#!/usr/bin/env wolframscript
(* Publish TypeTheory's documentation site with PacletPage, in one run: save the library environments (as
   scripts/save_environments.wls does), build the documentation (as build_docs.wls does), build the paclet
   archive and check that it loads alone in a fresh kernel,
   deploy the paclet resource, publish the site around it with its feedback form, and check the site as
   an anonymous reader sees it:

       https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory

   Publishing needs a kernel connected as $siteAccount (see pacletpage.wl). WOLFRAM_ID /
   WOLFRAM_PASSWORD connect it explicitly; otherwise the cached login is used, and the script stops
   before building anything if that is another account. A dry run deploys nothing and runs under any
   login, or none.

       wl -f release.wls [--no-cache]   build, deploy and publish
       wl -f release.wls --dry-run      build and check the documentation and the archive; deploy nothing
       wl -f release.wls --republish    replace the deployed release of this same version
*)

Get[FileNameJoin[{DirectoryName[$InputFileName], "pacletpage.wl"}]]

dryRun = MemberQ[$ScriptCommandLine, "--dry-run"]

With[{id = Environment["WOLFRAM_ID"], password = Environment["WOLFRAM_PASSWORD"]},
	If[StringQ[id] && id =!= $WolframID, CloudDisconnect[]];
	If[ ! TrueQ[$CloudConnected] && (StringQ[id] || ! dryRun),
		If[StringQ[id] && StringQ[password], CloudConnect[id, password], If[StringQ[id], CloudConnect[id], CloudConnect[]]]
	]
]

Print["PacletPage ", loadPacletPage[], If[dryRun, ", dry run", ", publishing as " <> ToString[$WolframID]]]

If[ ! dryRun && $WolframID =!= $siteAccount,
	Print["FATAL: publishing needs a kernel connected as ", $siteAccount, " (WOLFRAM_ID / WOLFRAM_PASSWORD); this one is connected as ", $WolframID, ". Nothing was built or published."];
	Exit[1]
]

saveLibraryEnvironments[]

buildDocumentation[]

result = WolframInstitute`PacletPage`PublishPacletPage[$pacletDirectory, "TypeTheory",
	"Build" -> False,
	"DryRun" -> dryRun,
	"Account" -> $siteAccount,
	"ResourceOptions" -> If[MemberQ[$ScriptCommandLine, "--republish"], Append[$resourceOptions, "Republish" -> True], $resourceOptions],
	"SiteOptions" -> $siteOptions
]

If[ ! AssociationQ[result],
	Print["FATAL: PublishPacletPage failed", If[FailureQ[result], ": " <> result["Message"], ""]];
	Exit[1]
]

With[{resource = result["Resource"]},
	Print["archive: ", resource["Archive"], " (", resource["ArchiveSize"], "), loads alone: ", TrueQ[resource["Load", "OK"]]];
	Print["resource: ", resource["Resource"], If[dryRun, " (dry run: not deployed)", ""]];
	If[! TrueQ[resource["Load", "OK"]], Exit[1]]
]

If[AssociationQ[result["Site"]], Print["site: ", result["Site", "Site"]]]

If[ AssociationQ[result["Check"]],
	Print["check: ", If[TrueQ[result["Check", "OK"]], "OK", "FAILED " <> ToString[Lookup[result["Check"], "Failed", {}], InputForm]]];
	If[! TrueQ[result["Check", "OK"]], Exit[1]]
]

Print["done"]
