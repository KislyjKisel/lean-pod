import Lake
open Lake DSL

package «pod» {
  srcDir := "src/lean"
}

lean_lib Pod

@[default_target]
lean_exe Main

def buildBindingsO
  (pkg : NPackage _package.name) (weakArgs traceArgs : Array String) (stem : String) :
    IndexBuildM (BuildJob FilePath) := do
      let oFile := pkg.irDir / "native" / (stem ++ ".o")
      let srcJob ← inputFile <| pkg.dir / "src" / "native" / (stem ++ ".c")
      buildO (stem ++ ".c") oFile srcJob weakArgs traceArgs
        ((get_config? cc).getD (← getLeanCc).toString)

extern_lib «lean-pod» pkg := do
  let name := nameToStaticLib "lean-pod"
  let mut weakArgs :=
    #["-I", (← getLeanIncludeDir).toString].append $
      Array.mk $ ((get_config? cflags).getD "").splitOn.filter $ not ∘ String.isEmpty

  let mut traceArgs := #["-fPIC"]

  match get_config? alloc with
  | .none | .some "lean" => pure ()
  | .some "native" => traceArgs := traceArgs.push "-DLEAN_POD_ALLOC_NATIVE"
  | .some _ => error "Unknown `alloc` option"

  if (get_config? cc).isNone then
    weakArgs := weakArgs ++ #["-I", ((← getLeanIncludeDir) / "clang").toString]

  buildStaticLib (pkg.nativeLibDir / name) #[
    (← buildBindingsO pkg weakArgs traceArgs "endianness"),
    (← buildBindingsO pkg weakArgs traceArgs "storable"),
    (← buildBindingsO pkg weakArgs traceArgs "uint"),
    (← buildBindingsO pkg weakArgs traceArgs "float"),
    (← buildBindingsO pkg weakArgs traceArgs "bytes_view"),
    (← buildBindingsO pkg weakArgs traceArgs "bytes_ref"),
    (← buildBindingsO pkg weakArgs traceArgs "buffer"),
    (← buildBindingsO pkg weakArgs traceArgs "instances"),
    (← buildBindingsO pkg weakArgs traceArgs "uvector")
  ]
