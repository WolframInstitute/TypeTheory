#!/usr/bin/env wolframscript
(* Build the TypeTheory documentation with PacletPage: each docs/paclet/en/**/*.md page whose
   frontmatter names a page template (Symbol, Guide, TechNote) becomes a notebook under
   TypeTheory/Documentation/English/, and docs/paclet/en/ResourceDefinition.md becomes
   TypeTheory/ResourceDefinition.nb. Other markdown (DOC_GUIDE.md) is skipped. No cloud login is
   needed.

   The build fails on a page that did not convert, and on a section that reads a name only an earlier
   section gave a value (see checkBuild in pacletpage.wl). A page is converted again only when its
   source or the paclet's code has changed; --no-cache evaluates every example again.

   Run with the `wl` CLI, not wolframscript, whose init can wedge the kernel mid-build:

       wl -f build_docs.wls [--no-cache]
*)

Get[FileNameJoin[{DirectoryName[$InputFileName], "pacletpage.wl"}]]

Print["PacletPage ", loadPacletPage[]]

buildDocumentation[]

Print["done"]
