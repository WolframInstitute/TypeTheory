#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Save TypeTheory's library environments into TypeTheory/Environments/, from which the paclet reads them when
   they are first asked for instead of building and checking them, while the kernel sources are the ones that
   wrote them (Kernel/Checking/SavedEnvironments.wl). release.wls saves them before it builds the archive; run
   this after changing the kernel, to load fast again from the checkout:

       wl -f scripts/save_environments.wls *)

Get[FileNameJoin[{ParentDirectory[DirectoryName[$InputFileName]], "pacletpage.wl"}]]

saveLibraryEnvironments[]
