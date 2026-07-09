module

public import Alloy.C

open scoped Alloy.C

public section

namespace Pod

scoped elab "alloy " &"c " &"print" : command => do
  println! Alloy.C.shimExt.getState (← Lean.getEnv) |>.text.source

/--
`define_foreign_constant my_const : Float := alloy c { return 2.4; }`
creates a parameterless function with the specified body using Alloy.
Requires `alloy c include <lean/lean.h>` to be present in the module before this command.
-/
scoped macro mods:declModifiers "define_foreign_constant " id:ident " : " type:term " := " &"alloy " &"c " stmts:Alloy.C.stmtSeq : command =>
  `(alloy c extern def fnId (α : Type) : ST α $type := $stmts:stmtSeq
    $mods:declModifiers def $id : $type := runST fnId)

/--
`alloy c builtin_initialize <c-stmts>`
creates an opaque function implemented using Alloy and passes it to `builtin_initialize`.
The function doesn't have any parameters and is appended with `return lean_box(0);`
-/
scoped macro "alloy " &"c " &"builtin_initialize " stmts:Alloy.C.stmtSeq  : command => do
  -- let body : Lean.TSyntax `Alloy.C.cStmt ← `(Alloy.C.|$stmts)
  `(alloy c extern def f : BaseIO Unit := { $(.mk stmts.raw); return lean_box(0); }
    builtin_initialize f)
