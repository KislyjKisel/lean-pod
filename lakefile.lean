import Lake
open Lake DSL

package «pod» {
  srcDir := "src/lean"
}

lean_lib Pod

@[default_target]
lean_exe Main

def buildBindingsO (pkg : Package) (flags : Array String) (stem : String) : IndexBuildM (BuildJob FilePath) := do
  let oFile := pkg.irDir / "native" / (stem ++ ".o")
  let srcJob ← inputFile <| pkg.dir / "src" / "native" / (stem ++ ".c")
  buildO (stem ++ ".c") oFile srcJob flags ((get_config? cc).getD (← getLeanCc).toString)

extern_lib «lean-pod» (pkg : Package) := do
  let name := nameToStaticLib "lean-pod"
  let mut flags :=
    #["-I", (← getLeanIncludeDir).toString, "-fPIC"].append $
      Array.mk $ ((get_config? cflags).getD "").splitOn.filter $ not ∘ String.isEmpty

  match get_config? alloc with
  | .none | .some "lean" => pure ()
  | .some "native" => flags := flags.push "-DLEAN_POD_ALLOC_NATIVE"
  | .some _ => error "Unknown `alloc` option"

  if (get_config? cc).isNone then
    flags := flags ++ #["-I", ((← getLeanIncludeDir) / "clang").toString]

  buildStaticLib (pkg.libDir / name) #[
    (← buildBindingsO pkg flags "endianness"),
    (← buildBindingsO pkg flags "storable"),
    (← buildBindingsO pkg flags "uint"),
    (← buildBindingsO pkg flags "float"),
    (← buildBindingsO pkg flags "bytes_view"),
    (← buildBindingsO pkg flags "bytes_ref"),
    (← buildBindingsO pkg flags "buffer"),
    (← buildBindingsO pkg flags "instances"),
    (← buildBindingsO pkg flags "uvector")
  ]
