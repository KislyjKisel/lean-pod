module

public meta import Alloy.C.IR
public meta import Lean.Compiler.IR.CompilerM
public meta import Lean.Compiler.NameMangling

public import Alloy.C.ShimElab

public meta section

namespace Pod.Alloy.DeclareLean

structure DeclInfo where
  cName : Lean.Name
  declaredInAlloy : Bool

abbrev EnvExtension :=
  Lean.PersistentEnvExtension
    (Lean.Name × Lean.Name)
    (Lean.Name × Lean.Name)
    (Lean.NameMap DeclInfo)

initialize envExtension : EnvExtension ← Lean.registerPersistentEnvExtension {
  mkInitial := pure ∅
  addEntryFn := fun s (leanName, cName) => s.insert leanName { cName, declaredInAlloy := false }
  addImportedFn := fun mods =>
    pure <| flip mods.foldl ∅ fun s modEntries =>
      flip modEntries.foldl s fun s (leanName, cName) =>
        s.insert leanName { cName, declaredInAlloy := false }
  exportEntriesFn := fun s => s.toArray.map <| Prod.map id DeclInfo.cName
}

def elabDeclareLean (nameStx : Lean.Syntax) (name : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let cId ← id do
    let env ← Lean.getEnv
    if let some declInfo := envExtension.getState env |>.find? name then
      if declInfo.declaredInAlloy
        then
          Lean.logWarningAt nameStx "already declared"
          return none
        else return some <| Lean.mkIdent declInfo.cName
    if let some cName := Lean.exportAttr.getParam? env name then
      return some <| Lean.mkIdent cName
    if let some cName :=
      (Lean.externAttr.getParam? env name >>= fun extern =>
        extern.entries.findSome? fun e =>
          if let .standard `all cName := e then some cName else none) then
      return some <| Lean.mkIdent <| Lean.Name.mkSimple cName
    let cName := Lean.Name.mkSimple <| "pod_alloy_" ++ name.mangle
    let cId := Lean.mkIdent cName
    let stubId ← Lean.mkIdent <$> (Lean.Elab.Command.liftCoreM <| Lean.mkFreshId)
    Lean.Elab.Command.elabCommand <| ← `(
      @[export $cId]
      def $stubId := $(Lean.mkIdent name)
    )
    Lean.MonadEnv.modifyEnv fun env =>
      envExtension.modifyState env fun s =>
        s.insert name { cName, declaredInAlloy := false }
    return some cId
  if let some cId := cId then
    let some irDecl := Lean.IR.findEnvDecl (← Lean.getEnv) name
      | throwErrorAt nameStx "failed to find Lean IR definition"
    let ty ← Lean.Elab.liftMacroM <| Alloy.C.expandIrResultTypeToC false irDecl.resultType
    let mut params := #[]
    for param in irDecl.params do
      let ty ← Lean.Elab.liftMacroM <| Alloy.C.expandIrParamTypeToC param.borrow param.ty
      params := params.push <| ← `(Alloy.C.paramDecl| $ty:cTypeSpec)
    Alloy.C.elabShimCommand <| ← `(cCmd|
      LEAN_EXPORT $ty:cTypeSpec $cId:ident($[$params:paramDecl],*);
    )
    Lean.MonadEnv.modifyEnv fun env =>
      envExtension.modifyState env fun s =>
        s.insert name { cName := cId.getId, declaredInAlloy := true }

/--
`alloy c declare_lean f` finds C name for `f` and ensures it is declared in Alloy C.
The name is taken from `export <name>` attribute if it exists for `f`, else from `extern "<name>"`.
Otherwise an auxiliary definition is created that is equivalent to `f` and is exported.
The C name is then declared in an Alloy C section.

`alloy c declare_lean? f` can be used instead to print used C names.

Use `lean<f>(args)` to call it later in Alloy C code.
-/
scoped elab (name := declareLeanParser) "alloy " &"c " &"declare_lean " names:ident* : command => do
  for nameStx in names do
    let name ← Lean.resolveGlobalConstNoOverload nameStx
    elabDeclareLean nameStx name

@[inherit_doc declareLeanParser]
scoped elab "alloy " &"c " &"declare_lean? " names:ident* : command => do
  for nameStx in names do
    let name ← Lean.resolveGlobalConstNoOverload nameStx
    elabDeclareLean nameStx name
    if let some declInfo := envExtension.getState (← Lean.getEnv) |>.find? name then
      Lean.logInfoAt nameStx declInfo.cName

/--
`lean<f>(args)` gets replaced with a call to a Lean function
declared in Alloy C by `alloy c declare_lean f`.
-/
syntax:1000 (name := leanCallParser) "lean" "<" ident ">" "(" cExpr,* ")" : cExpr

@[shim_elab leanCallParser]
def elabLeanCall : Alloy.ShimElab
| `(leanCallParser| lean<$nameStx>($args,*)) => do
  let name ← Lean.resolveGlobalConstNoOverload nameStx
  let some declInfo := envExtension.getState (← Lean.getEnv) |>.find? name
    | throwErrorAt nameStx "unavailable declaration, use `alloy c declare_lean name`"
  if !declInfo.declaredInAlloy then
    throwErrorAt nameStx "declaration unavailable in the current Alloy C module, use `alloy c declare_lean name`"
  let cId := Lean.mkIdent declInfo.cName
  Alloy.C.elabShimSyntax <| ← `(cExpr| $cId($args,*))
| _ => Lean.Elab.throwUnsupportedSyntax
