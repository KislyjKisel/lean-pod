module

public import Alloy.C

open scoped Alloy.C

public section

namespace Pod

/--
* `define_foreign_constant my_const : Float := alloy c { return 2.4; }`
  creates a parameterless function with the specified body using Alloy.
  Requires `alloy c include <lean/lean.h>` to be present in the module before this command.
-/
scoped macro mods:declModifiers "define_foreign_constant " id:ident " : " type:term " := " &"alloy " &"c " stmts:Alloy.C.stmtSeq : command =>
  `(alloy c extern def fnId (α : Type) : ST α $type := $stmts:stmtSeq
    $mods:declModifiers def $id : $type := runST fnId)
