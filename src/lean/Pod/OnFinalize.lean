import Pod.Meta

namespace Pod

/-- Noop. May be useful for artificially extending object lifetime when debugging. -/
@[extern "lean_pod_touch"]
opaque touch {α β} (val : @& α) (res : β) : β := res

/-- Opaque immutable object wrapping a callback to be executed on its finalization. -/
define_foreign_type OnFinalize

instance : Repr OnFinalize where
  reprPrec _ prec := Repr.addAppParen "onFinalize _" prec

/-- Creates an immutable finalization callback wrapper. -/
@[extern "lean_pod_onFinalize"]
opaque onFinalize : BaseIO Unit → OnFinalize

/-- Retrieves wrapper's assigned finalization callback. -/
@[extern "lean_pod_OnFinalize_get"]
opaque OnFinalize.get : @& OnFinalize → BaseIO Unit

/--
Opaque object wrapping a callback to be executed on its finalization.
Callback can be changed or removed from the object.
-/
define_foreign_type OnFinalizeMut

instance : Repr OnFinalizeMut where
  reprPrec _ prec := Repr.addAppParen "onFinalizeMut _" prec

/-- Creates a mutable finalization callback wrapper. -/
@[extern "lean_pod_onFinalizeMut"]
opaque onFinalizeMut : BaseIO Unit → BaseIO OnFinalizeMut

/-- Retrieves currently assigned finalization callback. -/
@[extern "lean_pod_OnFinalizeMut_get"]
opaque OnFinalizeMut.get : @& OnFinalize → BaseIO (Option $ BaseIO Unit)

/-- Assigns a new callback to the object. -/
@[extern "lean_pod_OnFinalizeMut_set"]
opaque OnFinalizeMut.set : @& OnFinalizeMut → BaseIO Unit → BaseIO Unit

/-- Removes callback from the object. Nothing will be done on finalization. -/
@[extern "lean_pod_OnFinalizeMut_suppress"]
opaque OnFinalizeMut.suppress : @& OnFinalizeMut → BaseIO Unit
