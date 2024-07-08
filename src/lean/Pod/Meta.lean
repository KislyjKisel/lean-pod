import Lean.Parser.Command

namespace Pod

/-- Defines a constant whose value is defined externally in foreign code. -/
scoped macro mods:declModifiers "define_foreign_constant" name:ident &" : " type:term &" := " ext:str : command => do
  `(@[extern $ext:str] private
    opaque getValue : @& Unit → $type
    $mods:declModifiers
    def $name : $type := getValue ())

/-- Defines a constant whose value is defined using foreign code. -/
scoped macro mods:declModifiers "define_foreign_constant" name:ident &" : " type:term &" := " &" inline " expr:str : command => do
  `(@[extern c inline $expr:str] private
    opaque getValue : Unit → $type
    $mods:declModifiers
    def $name : $type := getValue ())

/-- Defines a type that can be used to pass opaque foreign objects. -/
scoped macro mods:declModifiers "define_foreign_type" id:declId binders:bracketedBinder* : command => do
  let name := Lean.TSyntax.mk (id.raw.getArg 0)
  let univs := (id.raw.getArg 1).getArgs
  let univs := univs[1:univs.size - 1]
  let univs := Lean.Syntax.TSepArray.ofElems <| (univs.get! 0).getArgs.filterMap λ a ↦
    if a.getKind == `ident then some (Lean.TSyntax.mk a) else none
  let pairIdent := Lean.mkIdent (Lean.Name.appendAfter name.getId "Pointed")
  let argNames : Array Lean.Syntax := binders.concatMap λ x ↦
    match x.raw with
    | Lean.Syntax.node _ `Lean.Parser.Term.explicitBinder args =>
      Lean.Syntax.getArgs <$> (args.get? 1) |>.getD #[]
    | _ => #[]
  let applied := Lean.TSyntaxArray.mk argNames
  -- let instanceArgs : Lean.TSyntaxArray `Lean.Parser.Term.implicitBinder :=
  --   Lean.TSyntaxArray.mk $ argNames.map λ n ↦
  --     dbg_trace n;
  --     Lean.Syntax.node .none `Lean.Parser.Term.implicitBinder #[.atom .none "{", n, .atom .none "}"]
  `(private opaque $pairIdent.{$univs,*} $binders* : NonemptyType
    $mods:declModifiers
    def $name.{$univs,*} $binders* : Type := ($(pairIdent) $applied*).type
    set_option autoImplicit true in
    instance : Nonempty ($name $applied*) := ($(pairIdent) $applied*).property)

scoped macro "extern_initialize" &" => " cFn:str : command =>
  `(@[extern $cFn:str] private
    opaque initializeFn : BaseIO Unit
    builtin_initialize initializeFn)
