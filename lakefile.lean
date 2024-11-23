import Lake
open Lake DSL

def optionBindingsCompiler := (get_config? cc).getD "cc"
def optionBindingsFlags := Array.mk $ ((get_config? cflags).getD "").splitOn.filter $ not ∘ String.isEmpty
def optionAllocator := get_config? alloc

require Specs from git
  "https://github.com/axiomed/Specs.lean" @ "ab52219"

package «pod» where
  srcDir := "src/lean"
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Pod where
  precompileModules := true

@[test_driver]
lean_exe "pod-tests" where
  root := `Tests


def bindingsSources : Array String := #[
  "classes",
  "endianness",
  "storable",
  "uint",
  "float",
  "on_finalize",
  "bytes_view",
  "bytes_ref",
  "buffer",
  "instances",
  "uvector",
  "slot_map",
  "deque"
]

def bindingsSourceDirectory : System.FilePath := .mk "src" / "native"

def bindingsExtraTrace : Array System.FilePath := #[
  bindingsSourceDirectory / "include" / "lean_pod.h",
  bindingsSourceDirectory / "internal.h"
]

extern_lib «lean-pod» pkg := do
  let name := nameToStaticLib "lean-pod"
  let mut weakArgs := #["-I", (← getLeanIncludeDir).toString].append optionBindingsFlags
  let mut traceArgs := #["-fPIC"]
  let extraTrace ← mixTraceArray <$> (bindingsExtraTrace.mapM λ file ↦ computeTrace (pkg.dir / file))

  match optionAllocator with
  | .none | .some "lean" => pure ()
  | .some "native" => traceArgs := traceArgs.push "-DLEAN_POD_ALLOC_NATIVE"
  | .some _ => error "Unknown `alloc` option"

  buildStaticLib (pkg.nativeLibDir / name)
    (← bindingsSources.mapM λ stem ↦ do
      let oFile := pkg.irDir / "native" / (stem ++ ".o")
      let srcJob ← inputTextFile <| pkg.dir / bindingsSourceDirectory / (stem ++ ".c")
      buildO oFile srcJob weakArgs traceArgs optionBindingsCompiler (pure extraTrace))
