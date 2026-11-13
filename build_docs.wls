#!/usr/bin/env wolframscript
(* Build the TypeTheory documentation with PacletPage: each docs/paclet/en/**/*.md page whose
   frontmatter names a page template (Symbol, Guide, TechNote) becomes a notebook under
   TypeTheory/Documentation/English/, and docs/paclet/en/ResourceDefinition.md becomes
   TypeTheory/ResourceDefinition.nb. Other markdown (DOC_GUIDE.md) is skipped. No cloud login is
   needed.

   The build fails on a page that did not convert, and on a section that reads a name only an earlier
   section gave a value (see checkBuild in pacletpage.wl). A page is converted again only when its
   source or the paclet's code has changed; --no-cache evaluates every example again. The converter is
   MarkdownToNotebook at the commit pacletpage.wl names, fetched once:

       sh scripts/fetch_converter.sh
       wolframscript -f build_docs.wls [--no-cache] [--chunk i/n]

   A whole build takes over 4 GB. Where memory is short, build in chunks first, each in a kernel of its own that stays
   near 1 GB, and then whole, which finds the pages in the cache and evaluates only the tutorial that runs LeanLink:

       for i in 1 2 3 4 5 6 7 8; do wolframscript -f build_docs.wls --chunk $i/8; done; wolframscript -f build_docs.wls
*)

Get[FileNameJoin[{DirectoryName[$InputFileName], "pacletpage.wl"}]]

Print["PacletPage ", loadPacletPage[]]

buildDocumentation[]

Print["done"]
