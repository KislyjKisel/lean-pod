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
macro doc:(docComment)? "define_foreign_type" name:ident : command =>
  let pairIdent := Lean.mkIdent (Lean.Name.appendAfter name.getId "Pointed")
  if let some doc := doc
    then `(
      private opaque $pairIdent : NonemptyType
      $doc:docComment def $name : Type := $(pairIdent).type
      instance : Nonempty $name := $(pairIdent).property
    )
    else `(
      private opaque $pairIdent : NonemptyType
      def $name : Type := $(pairIdent).type
      instance : Nonempty $name := $(pairIdent).property
    )
