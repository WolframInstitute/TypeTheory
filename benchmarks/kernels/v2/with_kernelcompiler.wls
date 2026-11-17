(* scripts/run_tests.wls with the KernelCompiler paclet loaded first from the directory KernelCompiler beside the
   tree's root, for a kernel with no paclet installed and no network: <kernel> -f with_kernelcompiler.wls <test files>.
   Both columns of a v2 run take the compiler this way, so they run the same code. *)
With[{compiler = FileNameJoin[{Directory[], "KernelCompiler"}]},
	If[DirectoryQ[compiler], PacletDirectoryLoad[compiler]];
	Print["KernelCompiler: ", Through[PacletFind["Wolfram/KernelCompiler"]["Version"]]]
]
Get[FileNameJoin[{Directory[], "scripts", "run_tests.wls"}]]
