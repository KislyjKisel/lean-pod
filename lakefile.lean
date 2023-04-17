import Lake
open Lake DSL

package «pod» {
  srcDir := "src/lean"
}

@[default_target]
lean_lib Pod

def buildBindingsO (pkg : Package) (flags : Array String) (stem : String) : IndexBuildM (BuildJob FilePath) := do
  let oFile := pkg.irDir / "native" / (stem ++ ".o")
  let srcJob ← inputFile <| pkg.dir / "src" / "native" / (stem ++ ".c")
  buildO (stem ++ ".c") oFile srcJob flags ((get_config? cc).getD "cc")

extern_lib «lean-pod» (pkg : Package) := do
  let name := nameToStaticLib "lean-pod"
  let mut flags :=
    #["-I", (← getLeanIncludeDir).toString, "-fPIC"].append $
      Array.mk $ ((get_config? cflags).getD "").splitOn.filter $ not ∘ String.isEmpty

  let bindingsUIntOFile ← buildBindingsO pkg flags "uint"
  let bindingsFloat32OFile ← buildBindingsO pkg flags "float"
  let bindingsBytesViewOFile ← buildBindingsO pkg flags "bytes_view"
  let bindingsBytesRefOFile ← buildBindingsO pkg flags "bytes_ref"
  buildStaticLib (pkg.libDir / name) #[
    bindingsUIntOFile,
    bindingsFloat32OFile,
    bindingsBytesViewOFile,
    bindingsBytesRefOFile
  ]
