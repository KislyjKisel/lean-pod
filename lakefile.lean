import Lake
open Lake DSL

require alloy from git
  "https://github.com/KislyjKisel/lean4-alloy" @ "toolchain-nightly"

require LSpec from git
  "https://github.com/srghma/LSpec" @ "3fb9628"

package «pod» where
  srcDir := "src"
  leanOptions := #[⟨`autoImplicit, false⟩]

module_data alloy.c.o.export : System.FilePath
module_data alloy.c.o.noexport : System.FilePath

@[default_target]
lean_lib Pod where
  precompileModules := true
  nativeFacets := fun shouldExport =>
    if shouldExport then
      #[Module.oExportFacet, `module.alloy.c.o.export]
    else
      #[Module.oNoExportFacet, `module.alloy.c.o.noexport]

@[test_driver]
lean_exe PodTests
