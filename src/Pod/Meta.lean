module

namespace Pod

/--
`define_foreign_constant s : Float := "c_fn"`
defines a constant whose value is computed by a foreign function `double c_fn(void)`.
-/
scoped macro mods:declModifiers "define_foreign_constant " id:ident " : " type:term " := " cFn:str : command =>
  `(@[extern $cFn:str] private
    opaque fnId : ∀ α, ST α $type := fun _ ↦ ST.pure default_or_ofNonempty%
    $mods:declModifiers def $id : $type := runST fnId)

/--
`define_foreign_constant s : Float := inline "<c-expr>"`
defines a constant whose value is computed by inline C expression `<c-expr>`.
Uses `extern c inline` attribute.
-/
scoped macro mods:declModifiers "define_foreign_constant " id:ident " : " type:term " := " &"inline " cExpr:str : command =>
  `(@[extern $(Lean.mkIdent `c) inline $cExpr:str] private
    opaque fnId : ∀ α, ST α $type := fun _ ↦ ST.pure default_or_ofNonempty%
    $mods:declModifiers def $id : $type := runST fnId)

/--
`extern_initialize "c_fn"`
declares a `BaseIO Unit` typed opaque function implemented by a foreign function `c_fn` and passes it to `builtin_initialize`.
-/
scoped macro "extern_initialize " cFn:str : command =>
  `(@[extern $cFn:str] private
    opaque initializeFn : BaseIO Unit
    builtin_initialize initializeFn)
