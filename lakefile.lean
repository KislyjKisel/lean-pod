import Lake
open Lake DSL

def optionBindingsCompiler := get_config? cc
def optionBindingsFlags := Array.mk $ ((get_config? cflags).getD "").splitOn.filter $ not ∘ String.isEmpty
def optionAllocator := get_config? alloc
def optionPrecompile := (get_config? precompile).isSome

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "24cceb6"

package «pod» where
  srcDir := "src"
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Pod where
  precompileModules := optionPrecompile

@[test_driver]
lean_exe PodTests


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

def bindingsSourceDirectory : System.FilePath := .mk "ffi"

def bindingsExtraTrace : Array System.FilePath := #[
  bindingsSourceDirectory / "include" / "lean_pod.h",
  bindingsSourceDirectory / "internal.h"
]

extern_lib «lean-pod» pkg := do
  let name := nameToStaticLib "lean-pod"
  let mut weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let mut traceArgs := #["-fPIC"].append optionBindingsFlags
  let extraTrace ← mixTraceArray <$> (bindingsExtraTrace.mapM λ file ↦ computeTrace (pkg.dir / file))
  let extraTrace : BuildTrace := mixTrace extraTrace (← getLeanTrace)

  match optionAllocator with
  | .none | .some "lean" => pure ()
  | .some "native" => traceArgs := traceArgs.push "-DLEAN_POD_ALLOC_NATIVE"
  | .some _ => error "Unknown `alloc` option"

  if (get_config? cc).isNone && (← getLeanCc?).isNone && (← IO.getEnv "CC").isNone then
    weakArgs := weakArgs ++ #["-I", ((← getLeanIncludeDir) / "clang").toString]

  buildStaticLib (pkg.staticLibDir / name)
    (← bindingsSources.mapM λ stem ↦ do
      buildO
        (pkg.buildDir / "ffi" / (stem ++ ".o"))
        (← inputTextFile <| pkg.dir / bindingsSourceDirectory / (stem ++ ".c"))
        weakArgs
        traceArgs
        ((get_config? cc).getD (← getLeanCc).toString)
        (pure extraTrace)
    )
