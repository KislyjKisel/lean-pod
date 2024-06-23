namespace Pod

/--
Defines a constant whose value is defined externally in foreign code.
-/
macro doc:(docComment)? "define_foreign_constant" name:ident &" : " type:term &" := " ext:str : command => do
  let getterIdent := Lean.mkIdent (Lean.Name.appendBefore name.getId "get_")
  if let some doc := doc
    then `(
      @[extern $ext:str] private
      opaque $getterIdent : Unit → $type
      $doc:docComment def $name : $type := $getterIdent ()
    )
    else `(
      @[extern $ext:str] private
      opaque $getterIdent : Unit → $type
      def $name : $type := $getterIdent ()
    )

/--
Defines a constant whose value is defined using foreign code.
-/
macro doc:(docComment)? "define_foreign_constant" name:ident &" : " type:term &" := " &" inline " expr:str : command => do
  let getterIdent := Lean.mkIdent (Lean.Name.appendBefore name.getId "get_")
  if let some doc := doc
    then `(
      @[extern c inline $expr:str] private
      opaque $getterIdent : Unit → $type
      $doc:docComment def $name : $type := $getterIdent ()
    )
    else `(
      @[extern c inline $expr:str] private
      opaque $getterIdent : Unit → $type
      def $name : $type := $getterIdent ()
    )

/-- Defines a type that can be used to pass opaque foreign objects. -/
macro doc:(docComment)? "define_foreign_type" name:ident binders:bracketedBinder* : command => do
  let pairIdent := Lean.mkIdent (Lean.Name.appendAfter name.getId "Pointed")
  let argNames : Array Lean.Syntax := binders.filterMap λ x ↦
    match x.raw with
    | Lean.Syntax.node _ `Lean.Parser.Term.explicitBinder args => do
      let name := (← args.get? 1).getArg 0
      if name.isMissing
        then none
        else some name
    | _ => none
  let applied := Lean.TSyntaxArray.mk argNames
  -- let instanceArgs : Lean.TSyntaxArray `Lean.Parser.Term.implicitBinder :=
  --   Lean.TSyntaxArray.mk $ argNames.map λ n ↦
  --     dbg_trace n;
  --     Lean.Syntax.node .none `Lean.Parser.Term.implicitBinder #[.atom .none "{", n, .atom .none "}"]
  if let some doc := doc
    then `(
      private opaque $pairIdent $binders* : NonemptyType
      $doc:docComment def $name $binders* : Type := ($(pairIdent) $applied*).type
      set_option autoImplicit true in
      instance : Nonempty ($name $applied*) := ($(pairIdent) $applied*).property
    )
    else `(
      private opaque $pairIdent $binders* : NonemptyType
      def $name $binders* : Type := ($(pairIdent) $applied*).type
      set_option autoImplicit true in
      instance : Nonempty ($name $applied*) := ($(pairIdent) $applied*).property
    )
